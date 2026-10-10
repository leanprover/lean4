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
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(lean_object* v_e_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_){
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_a_6_ = stack[5].m_obj;
lean_object* v_a_7_ = stack[6].m_obj;
lean_object* v_res_12_;
v_res_12_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v_e_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_);
stack->m_obj
 = v_res_12_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg___boxed(lean_object* v_e_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v_e_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_, v_a_18_, v_a_19_);
lean_dec(v_a_19_);
lean_dec_ref(v_a_18_);
lean_dec(v_a_17_);
lean_dec_ref(v_a_16_);
lean_dec(v_a_15_);
lean_dec_ref(v_a_14_);
return v_res_21_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(lean_object* v_e_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v_e_22_, v_a_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_);
return v___x_34_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_22_ = stack[0].m_obj;
lean_object* v_a_23_ = stack[1].m_obj;
lean_object* v_a_24_ = stack[2].m_obj;
lean_object* v_a_25_ = stack[3].m_obj;
lean_object* v_a_26_ = stack[4].m_obj;
lean_object* v_a_27_ = stack[5].m_obj;
lean_object* v_a_28_ = stack[6].m_obj;
lean_object* v_a_29_ = stack[7].m_obj;
lean_object* v_a_30_ = stack[8].m_obj;
lean_object* v_a_31_ = stack[9].m_obj;
lean_object* v_a_32_ = stack[10].m_obj;
lean_object* v_res_35_;
v_res_35_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(v_e_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_, v_a_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_);
stack->m_obj
 = v_res_35_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___boxed(lean_object* v_e_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(v_e_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_);
lean_dec(v_a_46_);
lean_dec_ref(v_a_45_);
lean_dec(v_a_44_);
lean_dec_ref(v_a_43_);
lean_dec(v_a_42_);
lean_dec_ref(v_a_41_);
lean_dec(v_a_40_);
lean_dec_ref(v_a_39_);
lean_dec(v_a_38_);
lean_dec(v_a_37_);
return v_res_48_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn___redArg(lean_object* v_fn_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v_fn_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_);
return v___x_57_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fn_49_ = stack[0].m_obj;
lean_object* v_a_50_ = stack[1].m_obj;
lean_object* v_a_51_ = stack[2].m_obj;
lean_object* v_a_52_ = stack[3].m_obj;
lean_object* v_a_53_ = stack[4].m_obj;
lean_object* v_a_54_ = stack[5].m_obj;
lean_object* v_a_55_ = stack[6].m_obj;
lean_object* v_res_58_;
v_res_58_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn___redArg(v_fn_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_);
stack->m_obj
 = v_res_58_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn___redArg___boxed(lean_object* v_fn_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn___redArg(v_fn_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
lean_dec(v_a_63_);
lean_dec_ref(v_a_62_);
lean_dec(v_a_61_);
lean_dec_ref(v_a_60_);
return v_res_67_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn(lean_object* v_fn_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v_fn_68_, v_a_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_);
return v___x_80_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn_0interp(lean_interpreter_value* stack)
{
lean_object* v_fn_68_ = stack[0].m_obj;
lean_object* v_a_69_ = stack[1].m_obj;
lean_object* v_a_70_ = stack[2].m_obj;
lean_object* v_a_71_ = stack[3].m_obj;
lean_object* v_a_72_ = stack[4].m_obj;
lean_object* v_a_73_ = stack[5].m_obj;
lean_object* v_a_74_ = stack[6].m_obj;
lean_object* v_a_75_ = stack[7].m_obj;
lean_object* v_a_76_ = stack[8].m_obj;
lean_object* v_a_77_ = stack[9].m_obj;
lean_object* v_a_78_ = stack[10].m_obj;
lean_object* v_res_81_;
v_res_81_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn(v_fn_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn___boxed(lean_object* v_fn_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn(v_fn_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
lean_dec(v_a_90_);
lean_dec_ref(v_a_89_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
lean_dec(v_a_84_);
lean_dec(v_a_83_);
return v_res_94_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocessConst(lean_object* v_c_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v_c_95_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v_a_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
lean_inc_n(v_a_108_, 2);
lean_dec_ref_known(v___x_107_, 1);
v___x_109_ = lean_unsigned_to_nat(0u);
v___x_110_ = lean_box(0);
lean_inc(v_a_105_);
lean_inc_ref(v_a_104_);
lean_inc(v_a_103_);
lean_inc_ref(v_a_102_);
lean_inc(v_a_101_);
lean_inc_ref(v_a_100_);
lean_inc(v_a_99_);
lean_inc_ref(v_a_98_);
lean_inc(v_a_97_);
lean_inc(v_a_96_);
v___x_111_ = lean_grind_internalize(v_a_108_, v___x_109_, v___x_110_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_118_; 
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_118_ == 0)
{
lean_object* v_unused_119_; 
v_unused_119_ = lean_ctor_get(v___x_111_, 0);
lean_dec(v_unused_119_);
v___x_113_ = v___x_111_;
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
else
{
lean_dec(v___x_111_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_116_; 
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v_a_108_);
v___x_116_ = v___x_113_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_a_108_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
else
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
lean_dec(v_a_108_);
v_a_120_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___x_111_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_111_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
else
{
return v___x_107_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocessConst_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_95_ = stack[0].m_obj;
lean_object* v_a_96_ = stack[1].m_obj;
lean_object* v_a_97_ = stack[2].m_obj;
lean_object* v_a_98_ = stack[3].m_obj;
lean_object* v_a_99_ = stack[4].m_obj;
lean_object* v_a_100_ = stack[5].m_obj;
lean_object* v_a_101_ = stack[6].m_obj;
lean_object* v_a_102_ = stack[7].m_obj;
lean_object* v_a_103_ = stack[8].m_obj;
lean_object* v_a_104_ = stack[9].m_obj;
lean_object* v_a_105_ = stack[10].m_obj;
lean_object* v_res_128_;
v_res_128_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocessConst(v_c_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_);
stack->m_obj
 = v_res_128_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocessConst___boxed(lean_object* v_c_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocessConst(v_c_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec(v_a_137_);
lean_dec_ref(v_a_136_);
lean_dec(v_a_135_);
lean_dec_ref(v_a_134_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
lean_dec(v_a_131_);
lean_dec(v_a_130_);
return v_res_141_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(lean_object* v_c_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_Meta_Sym_canon(v_c_142_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; lean_object* v___x_156_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_a_155_);
lean_dec_ref_known(v___x_154_, 1);
v___x_156_ = l_Lean_Meta_Sym_shareCommon(v_a_155_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v_a_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v_a_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc_n(v_a_157_, 2);
lean_dec_ref_known(v___x_156_, 1);
v___x_158_ = lean_unsigned_to_nat(0u);
v___x_159_ = lean_box(0);
lean_inc(v_a_152_);
lean_inc_ref(v_a_151_);
lean_inc(v_a_150_);
lean_inc_ref(v_a_149_);
lean_inc(v_a_148_);
lean_inc_ref(v_a_147_);
lean_inc(v_a_146_);
lean_inc_ref(v_a_145_);
lean_inc(v_a_144_);
lean_inc(v_a_143_);
v___x_160_ = lean_grind_internalize(v_a_157_, v___x_158_, v___x_159_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_167_ == 0)
{
lean_object* v_unused_168_; 
v_unused_168_ = lean_ctor_get(v___x_160_, 0);
lean_dec(v_unused_168_);
v___x_162_ = v___x_160_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_dec(v___x_160_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v_a_157_);
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_157_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
else
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_176_; 
lean_dec(v_a_157_);
v_a_169_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_176_ == 0)
{
v___x_171_ = v___x_160_;
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___x_160_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_174_; 
if (v_isShared_172_ == 0)
{
v___x_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_a_169_);
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
else
{
return v___x_156_;
}
}
else
{
return v___x_154_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_142_ = stack[0].m_obj;
lean_object* v_a_143_ = stack[1].m_obj;
lean_object* v_a_144_ = stack[2].m_obj;
lean_object* v_a_145_ = stack[3].m_obj;
lean_object* v_a_146_ = stack[4].m_obj;
lean_object* v_a_147_ = stack[5].m_obj;
lean_object* v_a_148_ = stack[6].m_obj;
lean_object* v_a_149_ = stack[7].m_obj;
lean_object* v_a_150_ = stack[8].m_obj;
lean_object* v_a_151_ = stack[9].m_obj;
lean_object* v_a_152_ = stack[10].m_obj;
lean_object* v_res_177_;
v_res_177_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v_c_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_);
stack->m_obj
 = v_res_177_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst___boxed(lean_object* v_c_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v_c_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
lean_dec(v_a_180_);
lean_dec(v_a_179_);
return v_res_190_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__1(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__0));
v___x_193_ = l_Lean_stringToMessageData(v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__3(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__2));
v___x_196_ = l_Lean_stringToMessageData(v___x_195_);
return v___x_196_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(lean_object* v_a_197_, lean_object* v_b_198_){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_200_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__1);
v___x_201_ = l_Lean_indentExpr(v_a_197_);
v___x_202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_200_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
v___x_203_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__3);
v___x_204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_202_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
v___x_205_ = l_Lean_indentExpr(v_b_198_);
v___x_206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_204_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
v___x_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_197_ = stack[0].m_obj;
lean_object* v_b_198_ = stack[1].m_obj;
lean_object* v_res_208_;
v_res_208_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_a_197_, v_b_198_);
stack->m_obj
 = v_res_208_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___boxed(lean_object* v_a_209_, lean_object* v_b_210_, lean_object* v_a_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_a_209_, v_b_210_);
return v_res_212_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg(lean_object* v_a_213_, lean_object* v_b_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_a_213_, v_b_214_);
return v___x_220_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_213_ = stack[0].m_obj;
lean_object* v_b_214_ = stack[1].m_obj;
lean_object* v_a_215_ = stack[2].m_obj;
lean_object* v_a_216_ = stack[3].m_obj;
lean_object* v_a_217_ = stack[4].m_obj;
lean_object* v_a_218_ = stack[5].m_obj;
lean_object* v_res_221_;
v_res_221_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg(v_a_213_, v_b_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
stack->m_obj
 = v_res_221_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___boxed(lean_object* v_a_222_, lean_object* v_b_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg(v_a_222_, v_b_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
return v_res_229_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(lean_object* v_msgData_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v___x_236_; lean_object* v_env_237_; uint8_t v___x_238_; lean_object* v_env_239_; lean_object* v___x_240_; lean_object* v_toCold_241_; lean_object* v_mctx_242_; lean_object* v_lctx_243_; lean_object* v_options_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_236_ = lean_st_ref_get(v___y_234_);
v_env_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc_ref(v_env_237_);
lean_dec(v___x_236_);
v___x_238_ = 0;
v_env_239_ = l_Lean_Environment_setRecordingDeps(v_env_237_, v___x_238_);
v___x_240_ = lean_st_ref_get(v___y_232_);
v_toCold_241_ = lean_ctor_get(v___y_233_, 0);
v_mctx_242_ = lean_ctor_get(v___x_240_, 0);
lean_inc_ref(v_mctx_242_);
lean_dec(v___x_240_);
v_lctx_243_ = lean_ctor_get(v___y_231_, 2);
v_options_244_ = lean_ctor_get(v_toCold_241_, 2);
lean_inc_ref(v_options_244_);
lean_inc_ref(v_lctx_243_);
v___x_245_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_245_, 0, v_env_239_);
lean_ctor_set(v___x_245_, 1, v_mctx_242_);
lean_ctor_set(v___x_245_, 2, v_lctx_243_);
lean_ctor_set(v___x_245_, 3, v_options_244_);
v___x_246_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v_msgData_230_);
v___x_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_230_ = stack[0].m_obj;
lean_object* v___y_231_ = stack[1].m_obj;
lean_object* v___y_232_ = stack[2].m_obj;
lean_object* v___y_233_ = stack[3].m_obj;
lean_object* v___y_234_ = stack[4].m_obj;
lean_object* v_res_248_;
v_res_248_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(v_msgData_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
stack->m_obj
 = v_res_248_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0___boxed(lean_object* v_msgData_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(v_msgData_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
return v_res_255_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(lean_object* v_msg_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_ref_262_; lean_object* v___x_263_; lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_272_; 
v_ref_262_ = lean_ctor_get(v___y_259_, 2);
v___x_263_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(v_msg_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
v_a_264_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_272_ == 0)
{
v___x_266_ = v___x_263_;
v_isShared_267_ = v_isSharedCheck_272_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_263_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_272_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v___x_270_; 
lean_inc(v_ref_262_);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v_ref_262_);
lean_ctor_set(v___x_268_, 1, v_a_264_);
if (v_isShared_267_ == 0)
{
lean_ctor_set_tag(v___x_266_, 1);
lean_ctor_set(v___x_266_, 0, v___x_268_);
v___x_270_ = v___x_266_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_268_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_256_ = stack[0].m_obj;
lean_object* v___y_257_ = stack[1].m_obj;
lean_object* v___y_258_ = stack[2].m_obj;
lean_object* v___y_259_ = stack[3].m_obj;
lean_object* v___y_260_ = stack[4].m_obj;
lean_object* v_res_273_;
v_res_273_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(v_msg_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
stack->m_obj
 = v_res_273_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg___boxed(lean_object* v_msg_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(v_msg_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
return v_res_280_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(lean_object* v_a_281_, lean_object* v_b_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v___x_288_; 
lean_inc_ref(v_b_282_);
lean_inc_ref(v_a_281_);
v___x_288_ = l_Lean_Meta_isDefEqD(v_a_281_, v_b_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_301_; 
v_a_289_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_301_ == 0)
{
v___x_291_ = v___x_288_;
v_isShared_292_ = v_isSharedCheck_301_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_288_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_301_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
uint8_t v___x_293_; 
v___x_293_ = lean_unbox(v_a_289_);
lean_dec(v_a_289_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; lean_object* v_a_295_; lean_object* v___x_296_; 
lean_del_object(v___x_291_);
v___x_294_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_a_281_, v_b_282_);
v_a_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_a_295_);
lean_dec_ref(v___x_294_);
v___x_296_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(v_a_295_, v_a_283_, v_a_284_, v_a_285_, v_a_286_);
return v___x_296_;
}
else
{
lean_object* v___x_297_; lean_object* v___x_299_; 
lean_dec_ref(v_b_282_);
lean_dec_ref(v_a_281_);
v___x_297_ = lean_box(0);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v___x_297_);
v___x_299_ = v___x_291_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_297_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
else
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
lean_dec_ref(v_b_282_);
lean_dec_ref(v_a_281_);
v_a_302_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_288_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_288_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_281_ = stack[0].m_obj;
lean_object* v_b_282_ = stack[1].m_obj;
lean_object* v_a_283_ = stack[2].m_obj;
lean_object* v_a_284_ = stack[3].m_obj;
lean_object* v_a_285_ = stack[4].m_obj;
lean_object* v_a_286_ = stack[5].m_obj;
lean_object* v_res_310_;
v_res_310_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_a_281_, v_b_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_);
stack->m_obj
 = v_res_310_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq___boxed(lean_object* v_a_311_, lean_object* v_b_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_a_311_, v_b_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
lean_dec(v_a_314_);
lean_dec_ref(v_a_313_);
return v_res_318_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0(lean_object* v_00_u03b1_319_, lean_object* v_msg_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(v_msg_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
return v___x_326_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_320_ = stack[1].m_obj;
lean_object* v___y_321_ = stack[2].m_obj;
lean_object* v___y_322_ = stack[3].m_obj;
lean_object* v___y_323_ = stack[4].m_obj;
lean_object* v___y_324_ = stack[5].m_obj;
lean_object* v_res_327_;
v_res_327_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0(lean_box(0), v_msg_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
stack->m_obj
 = v_res_327_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___boxed(lean_object* v_00_u03b1_328_, lean_object* v_msg_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0(v_00_u03b1_328_, v_msg_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
return v_res_335_;
}
}
lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0(lean_object* v_p_336_, lean_object* v___x_337_, lean_object* v___x_338_, lean_object* v_x_339_, size_t v_x_340_, size_t v_x_341_){
_start:
{
if (lean_obj_tag(v_x_339_) == 0)
{
lean_object* v_cs_342_; size_t v_j_343_; lean_object* v___x_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v_cs_342_ = lean_ctor_get(v_x_339_, 0);
v_j_343_ = lean_usize_shift_right(v_x_340_, v_x_341_);
v___x_344_ = lean_usize_to_nat(v_j_343_);
v___x_345_ = lean_array_get_size(v_cs_342_);
v___x_346_ = lean_nat_dec_lt(v___x_344_, v___x_345_);
if (v___x_346_ == 0)
{
lean_dec(v___x_344_);
lean_dec(v_p_336_);
return v_x_339_;
}
else
{
lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_364_; 
lean_inc_ref(v_cs_342_);
v_isSharedCheck_364_ = !lean_is_exclusive(v_x_339_);
if (v_isSharedCheck_364_ == 0)
{
lean_object* v_unused_365_; 
v_unused_365_ = lean_ctor_get(v_x_339_, 0);
lean_dec(v_unused_365_);
v___x_348_ = v_x_339_;
v_isShared_349_ = v_isSharedCheck_364_;
goto v_resetjp_347_;
}
else
{
lean_dec(v_x_339_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_364_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
size_t v___x_350_; size_t v___x_351_; size_t v___x_352_; size_t v_i_353_; size_t v___x_354_; size_t v_shift_355_; lean_object* v_v_356_; lean_object* v___x_357_; lean_object* v_xs_x27_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_350_ = ((size_t)1ULL);
v___x_351_ = lean_usize_shift_left(v___x_350_, v_x_341_);
v___x_352_ = lean_usize_sub(v___x_351_, v___x_350_);
v_i_353_ = lean_usize_land(v_x_340_, v___x_352_);
v___x_354_ = ((size_t)5ULL);
v_shift_355_ = lean_usize_sub(v_x_341_, v___x_354_);
v_v_356_ = lean_array_fget(v_cs_342_, v___x_344_);
v___x_357_ = lean_box(0);
v_xs_x27_358_ = lean_array_fset(v_cs_342_, v___x_344_, v___x_357_);
v___x_359_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0(v_p_336_, v___x_337_, v___x_338_, v_v_356_, v_i_353_, v_shift_355_);
v___x_360_ = lean_array_fset(v_xs_x27_358_, v___x_344_, v___x_359_);
lean_dec(v___x_344_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v___x_360_);
v___x_362_ = v___x_348_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_360_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
else
{
lean_object* v_vs_366_; lean_object* v___x_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v_vs_366_ = lean_ctor_get(v_x_339_, 0);
v___x_367_ = lean_usize_to_nat(v_x_340_);
v___x_368_ = lean_array_get_size(v_vs_366_);
v___x_369_ = lean_nat_dec_lt(v___x_367_, v___x_368_);
if (v___x_369_ == 0)
{
lean_dec(v___x_367_);
lean_dec(v_p_336_);
return v_x_339_;
}
else
{
lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_384_; 
lean_inc_ref(v_vs_366_);
v_isSharedCheck_384_ = !lean_is_exclusive(v_x_339_);
if (v_isSharedCheck_384_ == 0)
{
lean_object* v_unused_385_; 
v_unused_385_ = lean_ctor_get(v_x_339_, 0);
lean_dec(v_unused_385_);
v___x_371_ = v_x_339_;
v_isShared_372_ = v_isSharedCheck_384_;
goto v_resetjp_370_;
}
else
{
lean_dec(v_x_339_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_384_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
uint8_t v___x_373_; lean_object* v_v_374_; lean_object* v___x_375_; lean_object* v_xs_x27_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_373_ = lean_nat_dec_lt(v___x_337_, v___x_338_);
v_v_374_ = lean_array_fget(v_vs_366_, v___x_367_);
v___x_375_ = lean_box(0);
v_xs_x27_376_ = lean_array_fset(v_vs_366_, v___x_367_, v___x_375_);
v___x_377_ = lean_box(9);
v___x_378_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_378_, 0, v_p_336_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
lean_ctor_set_uint8(v___x_378_, sizeof(void*)*2, v___x_373_);
v___x_379_ = l_Lean_PersistentArray_push___redArg(v_v_374_, v___x_378_);
v___x_380_ = lean_array_fset(v_xs_x27_376_, v___x_367_, v___x_379_);
lean_dec(v___x_367_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v___x_380_);
v___x_382_ = v___x_371_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_336_ = stack[0].m_obj;
lean_object* v___x_337_ = stack[1].m_obj;
lean_object* v___x_338_ = stack[2].m_obj;
lean_object* v_x_339_ = stack[3].m_obj;
size_t v_x_340_ = stack[4].m_num;
size_t v_x_341_ = stack[5].m_num;
lean_object* v_res_386_;
v_res_386_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0(v_p_336_, v___x_337_, v___x_338_, v_x_339_, v_x_340_, v_x_341_);
stack->m_obj
 = v_res_386_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0___boxed(lean_object* v_p_387_, lean_object* v___x_388_, lean_object* v___x_389_, lean_object* v_x_390_, lean_object* v_x_391_, lean_object* v_x_392_){
_start:
{
size_t v_x_283__boxed_393_; size_t v_x_284__boxed_394_; lean_object* v_res_395_; 
v_x_283__boxed_393_ = lean_unbox_usize(v_x_391_);
lean_dec(v_x_391_);
v_x_284__boxed_394_ = lean_unbox_usize(v_x_392_);
lean_dec(v_x_392_);
v_res_395_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0(v_p_387_, v___x_388_, v___x_389_, v_x_390_, v_x_283__boxed_393_, v_x_284__boxed_394_);
lean_dec(v___x_389_);
lean_dec(v___x_388_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0(lean_object* v_p_396_, lean_object* v___x_397_, lean_object* v___x_398_, lean_object* v_t_399_, lean_object* v_i_400_){
_start:
{
lean_object* v_root_401_; lean_object* v_tail_402_; lean_object* v_size_403_; size_t v_shift_404_; lean_object* v_tailOff_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_432_; 
v_root_401_ = lean_ctor_get(v_t_399_, 0);
v_tail_402_ = lean_ctor_get(v_t_399_, 1);
v_size_403_ = lean_ctor_get(v_t_399_, 2);
v_shift_404_ = lean_ctor_get_usize(v_t_399_, 4);
v_tailOff_405_ = lean_ctor_get(v_t_399_, 3);
v_isSharedCheck_432_ = !lean_is_exclusive(v_t_399_);
if (v_isSharedCheck_432_ == 0)
{
v___x_407_ = v_t_399_;
v_isShared_408_ = v_isSharedCheck_432_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_tailOff_405_);
lean_inc(v_size_403_);
lean_inc(v_tail_402_);
lean_inc(v_root_401_);
lean_dec(v_t_399_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_432_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
uint8_t v___x_409_; 
v___x_409_ = lean_nat_dec_le(v_tailOff_405_, v_i_400_);
if (v___x_409_ == 0)
{
size_t v___x_410_; lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_410_ = lean_usize_of_nat(v_i_400_);
v___x_411_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0(v_p_396_, v___x_397_, v___x_398_, v_root_401_, v___x_410_, v_shift_404_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 0, v___x_411_);
v___x_413_ = v___x_407_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_411_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v_tail_402_);
lean_ctor_set(v_reuseFailAlloc_414_, 2, v_size_403_);
lean_ctor_set(v_reuseFailAlloc_414_, 3, v_tailOff_405_);
lean_ctor_set_usize(v_reuseFailAlloc_414_, 4, v_shift_404_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
else
{
lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_415_ = lean_nat_sub(v_i_400_, v_tailOff_405_);
v___x_416_ = lean_array_get_size(v_tail_402_);
v___x_417_ = lean_nat_dec_lt(v___x_415_, v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_419_; 
lean_dec(v___x_415_);
lean_dec(v_p_396_);
if (v_isShared_408_ == 0)
{
v___x_419_ = v___x_407_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_root_401_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_tail_402_);
lean_ctor_set(v_reuseFailAlloc_420_, 2, v_size_403_);
lean_ctor_set(v_reuseFailAlloc_420_, 3, v_tailOff_405_);
lean_ctor_set_usize(v_reuseFailAlloc_420_, 4, v_shift_404_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
else
{
uint8_t v___x_421_; lean_object* v_v_422_; lean_object* v___x_423_; lean_object* v_xs_x27_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_430_; 
v___x_421_ = lean_nat_dec_lt(v___x_397_, v___x_398_);
v_v_422_ = lean_array_fget(v_tail_402_, v___x_415_);
v___x_423_ = lean_box(0);
v_xs_x27_424_ = lean_array_fset(v_tail_402_, v___x_415_, v___x_423_);
v___x_425_ = lean_box(9);
v___x_426_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_426_, 0, v_p_396_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
lean_ctor_set_uint8(v___x_426_, sizeof(void*)*2, v___x_421_);
v___x_427_ = l_Lean_PersistentArray_push___redArg(v_v_422_, v___x_426_);
v___x_428_ = lean_array_fset(v_xs_x27_424_, v___x_415_, v___x_427_);
lean_dec(v___x_415_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 1, v___x_428_);
v___x_430_ = v___x_407_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_root_401_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_431_, 2, v_size_403_);
lean_ctor_set(v_reuseFailAlloc_431_, 3, v_tailOff_405_);
lean_ctor_set_usize(v_reuseFailAlloc_431_, 4, v_shift_404_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0___boxed(lean_object* v_p_433_, lean_object* v___x_434_, lean_object* v___x_435_, lean_object* v_t_436_, lean_object* v_i_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0(v_p_433_, v___x_434_, v___x_435_, v_t_436_, v_i_437_);
lean_dec(v_i_437_);
lean_dec(v___x_435_);
lean_dec(v___x_434_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0(lean_object* v_a_439_, lean_object* v_p_440_, lean_object* v_one_441_, lean_object* v_s_442_){
_start:
{
lean_object* v_structs_443_; lean_object* v_typeIdOf_444_; lean_object* v_exprToStructId_445_; lean_object* v_exprToStructIdEntries_446_; lean_object* v_forbiddenNatModules_447_; lean_object* v_natStructs_448_; lean_object* v_natTypeIdOf_449_; lean_object* v_exprToNatStructId_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v_structs_443_ = lean_ctor_get(v_s_442_, 0);
v_typeIdOf_444_ = lean_ctor_get(v_s_442_, 1);
v_exprToStructId_445_ = lean_ctor_get(v_s_442_, 2);
v_exprToStructIdEntries_446_ = lean_ctor_get(v_s_442_, 3);
v_forbiddenNatModules_447_ = lean_ctor_get(v_s_442_, 4);
v_natStructs_448_ = lean_ctor_get(v_s_442_, 5);
v_natTypeIdOf_449_ = lean_ctor_get(v_s_442_, 6);
v_exprToNatStructId_450_ = lean_ctor_get(v_s_442_, 7);
v___x_451_ = lean_array_get_size(v_structs_443_);
v___x_452_ = lean_nat_dec_lt(v_a_439_, v___x_451_);
if (v___x_452_ == 0)
{
lean_dec(v_p_440_);
return v_s_442_;
}
else
{
lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_514_; 
lean_inc_ref(v_exprToNatStructId_450_);
lean_inc_ref(v_natTypeIdOf_449_);
lean_inc_ref(v_natStructs_448_);
lean_inc_ref(v_forbiddenNatModules_447_);
lean_inc_ref(v_exprToStructIdEntries_446_);
lean_inc_ref(v_exprToStructId_445_);
lean_inc_ref(v_typeIdOf_444_);
lean_inc_ref(v_structs_443_);
v_isSharedCheck_514_ = !lean_is_exclusive(v_s_442_);
if (v_isSharedCheck_514_ == 0)
{
lean_object* v_unused_515_; lean_object* v_unused_516_; lean_object* v_unused_517_; lean_object* v_unused_518_; lean_object* v_unused_519_; lean_object* v_unused_520_; lean_object* v_unused_521_; lean_object* v_unused_522_; 
v_unused_515_ = lean_ctor_get(v_s_442_, 7);
lean_dec(v_unused_515_);
v_unused_516_ = lean_ctor_get(v_s_442_, 6);
lean_dec(v_unused_516_);
v_unused_517_ = lean_ctor_get(v_s_442_, 5);
lean_dec(v_unused_517_);
v_unused_518_ = lean_ctor_get(v_s_442_, 4);
lean_dec(v_unused_518_);
v_unused_519_ = lean_ctor_get(v_s_442_, 3);
lean_dec(v_unused_519_);
v_unused_520_ = lean_ctor_get(v_s_442_, 2);
lean_dec(v_unused_520_);
v_unused_521_ = lean_ctor_get(v_s_442_, 1);
lean_dec(v_unused_521_);
v_unused_522_ = lean_ctor_get(v_s_442_, 0);
lean_dec(v_unused_522_);
v___x_454_ = v_s_442_;
v_isShared_455_ = v_isSharedCheck_514_;
goto v_resetjp_453_;
}
else
{
lean_dec(v_s_442_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_514_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v_v_456_; lean_object* v_id_457_; lean_object* v_ringId_x3f_458_; lean_object* v_type_459_; lean_object* v_u_460_; lean_object* v_intModuleInst_461_; lean_object* v_leInst_x3f_462_; lean_object* v_ltInst_x3f_463_; lean_object* v_lawfulOrderLTInst_x3f_464_; lean_object* v_isPreorderInst_x3f_465_; lean_object* v_orderedAddInst_x3f_466_; lean_object* v_isLinearInst_x3f_467_; lean_object* v_noNatDivInst_x3f_468_; lean_object* v_ringInst_x3f_469_; lean_object* v_commRingInst_x3f_470_; lean_object* v_orderedRingInst_x3f_471_; lean_object* v_fieldInst_x3f_472_; lean_object* v_charInst_x3f_473_; lean_object* v_zero_474_; lean_object* v_ofNatZero_475_; lean_object* v_one_x3f_476_; lean_object* v_leFn_x3f_477_; lean_object* v_ltFn_x3f_478_; lean_object* v_addFn_479_; lean_object* v_zsmulFn_480_; lean_object* v_nsmulFn_481_; lean_object* v_zsmulFn_x3f_482_; lean_object* v_nsmulFn_x3f_483_; lean_object* v_homomulFn_x3f_484_; lean_object* v_subFn_485_; lean_object* v_negFn_486_; lean_object* v_vars_487_; lean_object* v_varMap_488_; lean_object* v_lowers_489_; lean_object* v_uppers_490_; lean_object* v_diseqs_491_; lean_object* v_assignment_492_; uint8_t v_caseSplits_493_; lean_object* v_conflict_x3f_494_; lean_object* v_diseqSplits_495_; lean_object* v_elimEqs_496_; lean_object* v_elimStack_497_; lean_object* v_occurs_498_; lean_object* v_ignored_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_513_; 
v_v_456_ = lean_array_fget(v_structs_443_, v_a_439_);
v_id_457_ = lean_ctor_get(v_v_456_, 0);
v_ringId_x3f_458_ = lean_ctor_get(v_v_456_, 1);
v_type_459_ = lean_ctor_get(v_v_456_, 2);
v_u_460_ = lean_ctor_get(v_v_456_, 3);
v_intModuleInst_461_ = lean_ctor_get(v_v_456_, 4);
v_leInst_x3f_462_ = lean_ctor_get(v_v_456_, 5);
v_ltInst_x3f_463_ = lean_ctor_get(v_v_456_, 6);
v_lawfulOrderLTInst_x3f_464_ = lean_ctor_get(v_v_456_, 7);
v_isPreorderInst_x3f_465_ = lean_ctor_get(v_v_456_, 8);
v_orderedAddInst_x3f_466_ = lean_ctor_get(v_v_456_, 9);
v_isLinearInst_x3f_467_ = lean_ctor_get(v_v_456_, 10);
v_noNatDivInst_x3f_468_ = lean_ctor_get(v_v_456_, 11);
v_ringInst_x3f_469_ = lean_ctor_get(v_v_456_, 12);
v_commRingInst_x3f_470_ = lean_ctor_get(v_v_456_, 13);
v_orderedRingInst_x3f_471_ = lean_ctor_get(v_v_456_, 14);
v_fieldInst_x3f_472_ = lean_ctor_get(v_v_456_, 15);
v_charInst_x3f_473_ = lean_ctor_get(v_v_456_, 16);
v_zero_474_ = lean_ctor_get(v_v_456_, 17);
v_ofNatZero_475_ = lean_ctor_get(v_v_456_, 18);
v_one_x3f_476_ = lean_ctor_get(v_v_456_, 19);
v_leFn_x3f_477_ = lean_ctor_get(v_v_456_, 20);
v_ltFn_x3f_478_ = lean_ctor_get(v_v_456_, 21);
v_addFn_479_ = lean_ctor_get(v_v_456_, 22);
v_zsmulFn_480_ = lean_ctor_get(v_v_456_, 23);
v_nsmulFn_481_ = lean_ctor_get(v_v_456_, 24);
v_zsmulFn_x3f_482_ = lean_ctor_get(v_v_456_, 25);
v_nsmulFn_x3f_483_ = lean_ctor_get(v_v_456_, 26);
v_homomulFn_x3f_484_ = lean_ctor_get(v_v_456_, 27);
v_subFn_485_ = lean_ctor_get(v_v_456_, 28);
v_negFn_486_ = lean_ctor_get(v_v_456_, 29);
v_vars_487_ = lean_ctor_get(v_v_456_, 30);
v_varMap_488_ = lean_ctor_get(v_v_456_, 31);
v_lowers_489_ = lean_ctor_get(v_v_456_, 32);
v_uppers_490_ = lean_ctor_get(v_v_456_, 33);
v_diseqs_491_ = lean_ctor_get(v_v_456_, 34);
v_assignment_492_ = lean_ctor_get(v_v_456_, 35);
v_caseSplits_493_ = lean_ctor_get_uint8(v_v_456_, sizeof(void*)*42);
v_conflict_x3f_494_ = lean_ctor_get(v_v_456_, 36);
v_diseqSplits_495_ = lean_ctor_get(v_v_456_, 37);
v_elimEqs_496_ = lean_ctor_get(v_v_456_, 38);
v_elimStack_497_ = lean_ctor_get(v_v_456_, 39);
v_occurs_498_ = lean_ctor_get(v_v_456_, 40);
v_ignored_499_ = lean_ctor_get(v_v_456_, 41);
v_isSharedCheck_513_ = !lean_is_exclusive(v_v_456_);
if (v_isSharedCheck_513_ == 0)
{
v___x_501_ = v_v_456_;
v_isShared_502_ = v_isSharedCheck_513_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_ignored_499_);
lean_inc(v_occurs_498_);
lean_inc(v_elimStack_497_);
lean_inc(v_elimEqs_496_);
lean_inc(v_diseqSplits_495_);
lean_inc(v_conflict_x3f_494_);
lean_inc(v_assignment_492_);
lean_inc(v_diseqs_491_);
lean_inc(v_uppers_490_);
lean_inc(v_lowers_489_);
lean_inc(v_varMap_488_);
lean_inc(v_vars_487_);
lean_inc(v_negFn_486_);
lean_inc(v_subFn_485_);
lean_inc(v_homomulFn_x3f_484_);
lean_inc(v_nsmulFn_x3f_483_);
lean_inc(v_zsmulFn_x3f_482_);
lean_inc(v_nsmulFn_481_);
lean_inc(v_zsmulFn_480_);
lean_inc(v_addFn_479_);
lean_inc(v_ltFn_x3f_478_);
lean_inc(v_leFn_x3f_477_);
lean_inc(v_one_x3f_476_);
lean_inc(v_ofNatZero_475_);
lean_inc(v_zero_474_);
lean_inc(v_charInst_x3f_473_);
lean_inc(v_fieldInst_x3f_472_);
lean_inc(v_orderedRingInst_x3f_471_);
lean_inc(v_commRingInst_x3f_470_);
lean_inc(v_ringInst_x3f_469_);
lean_inc(v_noNatDivInst_x3f_468_);
lean_inc(v_isLinearInst_x3f_467_);
lean_inc(v_orderedAddInst_x3f_466_);
lean_inc(v_isPreorderInst_x3f_465_);
lean_inc(v_lawfulOrderLTInst_x3f_464_);
lean_inc(v_ltInst_x3f_463_);
lean_inc(v_leInst_x3f_462_);
lean_inc(v_intModuleInst_461_);
lean_inc(v_u_460_);
lean_inc(v_type_459_);
lean_inc(v_ringId_x3f_458_);
lean_inc(v_id_457_);
lean_dec(v_v_456_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_513_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v_xs_x27_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_503_ = lean_box(0);
v_xs_x27_504_ = lean_array_fset(v_structs_443_, v_a_439_, v___x_503_);
v___x_505_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0(v_p_440_, v_a_439_, v___x_451_, v_lowers_489_, v_one_441_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 32, v___x_505_);
v___x_507_ = v___x_501_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_id_457_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v_ringId_x3f_458_);
lean_ctor_set(v_reuseFailAlloc_512_, 2, v_type_459_);
lean_ctor_set(v_reuseFailAlloc_512_, 3, v_u_460_);
lean_ctor_set(v_reuseFailAlloc_512_, 4, v_intModuleInst_461_);
lean_ctor_set(v_reuseFailAlloc_512_, 5, v_leInst_x3f_462_);
lean_ctor_set(v_reuseFailAlloc_512_, 6, v_ltInst_x3f_463_);
lean_ctor_set(v_reuseFailAlloc_512_, 7, v_lawfulOrderLTInst_x3f_464_);
lean_ctor_set(v_reuseFailAlloc_512_, 8, v_isPreorderInst_x3f_465_);
lean_ctor_set(v_reuseFailAlloc_512_, 9, v_orderedAddInst_x3f_466_);
lean_ctor_set(v_reuseFailAlloc_512_, 10, v_isLinearInst_x3f_467_);
lean_ctor_set(v_reuseFailAlloc_512_, 11, v_noNatDivInst_x3f_468_);
lean_ctor_set(v_reuseFailAlloc_512_, 12, v_ringInst_x3f_469_);
lean_ctor_set(v_reuseFailAlloc_512_, 13, v_commRingInst_x3f_470_);
lean_ctor_set(v_reuseFailAlloc_512_, 14, v_orderedRingInst_x3f_471_);
lean_ctor_set(v_reuseFailAlloc_512_, 15, v_fieldInst_x3f_472_);
lean_ctor_set(v_reuseFailAlloc_512_, 16, v_charInst_x3f_473_);
lean_ctor_set(v_reuseFailAlloc_512_, 17, v_zero_474_);
lean_ctor_set(v_reuseFailAlloc_512_, 18, v_ofNatZero_475_);
lean_ctor_set(v_reuseFailAlloc_512_, 19, v_one_x3f_476_);
lean_ctor_set(v_reuseFailAlloc_512_, 20, v_leFn_x3f_477_);
lean_ctor_set(v_reuseFailAlloc_512_, 21, v_ltFn_x3f_478_);
lean_ctor_set(v_reuseFailAlloc_512_, 22, v_addFn_479_);
lean_ctor_set(v_reuseFailAlloc_512_, 23, v_zsmulFn_480_);
lean_ctor_set(v_reuseFailAlloc_512_, 24, v_nsmulFn_481_);
lean_ctor_set(v_reuseFailAlloc_512_, 25, v_zsmulFn_x3f_482_);
lean_ctor_set(v_reuseFailAlloc_512_, 26, v_nsmulFn_x3f_483_);
lean_ctor_set(v_reuseFailAlloc_512_, 27, v_homomulFn_x3f_484_);
lean_ctor_set(v_reuseFailAlloc_512_, 28, v_subFn_485_);
lean_ctor_set(v_reuseFailAlloc_512_, 29, v_negFn_486_);
lean_ctor_set(v_reuseFailAlloc_512_, 30, v_vars_487_);
lean_ctor_set(v_reuseFailAlloc_512_, 31, v_varMap_488_);
lean_ctor_set(v_reuseFailAlloc_512_, 32, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_512_, 33, v_uppers_490_);
lean_ctor_set(v_reuseFailAlloc_512_, 34, v_diseqs_491_);
lean_ctor_set(v_reuseFailAlloc_512_, 35, v_assignment_492_);
lean_ctor_set(v_reuseFailAlloc_512_, 36, v_conflict_x3f_494_);
lean_ctor_set(v_reuseFailAlloc_512_, 37, v_diseqSplits_495_);
lean_ctor_set(v_reuseFailAlloc_512_, 38, v_elimEqs_496_);
lean_ctor_set(v_reuseFailAlloc_512_, 39, v_elimStack_497_);
lean_ctor_set(v_reuseFailAlloc_512_, 40, v_occurs_498_);
lean_ctor_set(v_reuseFailAlloc_512_, 41, v_ignored_499_);
lean_ctor_set_uint8(v_reuseFailAlloc_512_, sizeof(void*)*42, v_caseSplits_493_);
v___x_507_ = v_reuseFailAlloc_512_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_508_ = lean_array_fset(v_xs_x27_504_, v_a_439_, v___x_507_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_508_);
v___x_510_ = v___x_454_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_508_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_typeIdOf_444_);
lean_ctor_set(v_reuseFailAlloc_511_, 2, v_exprToStructId_445_);
lean_ctor_set(v_reuseFailAlloc_511_, 3, v_exprToStructIdEntries_446_);
lean_ctor_set(v_reuseFailAlloc_511_, 4, v_forbiddenNatModules_447_);
lean_ctor_set(v_reuseFailAlloc_511_, 5, v_natStructs_448_);
lean_ctor_set(v_reuseFailAlloc_511_, 6, v_natTypeIdOf_449_);
lean_ctor_set(v_reuseFailAlloc_511_, 7, v_exprToNatStructId_450_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0___boxed(lean_object* v_a_523_, lean_object* v_p_524_, lean_object* v_one_525_, lean_object* v_s_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0(v_a_523_, v_p_524_, v_one_525_, v_s_526_);
lean_dec(v_one_525_);
lean_dec(v_a_523_);
return v_res_527_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_unsigned_to_nat(1u);
v___x_529_ = lean_nat_to_int(v___x_528_);
return v___x_529_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0);
v___x_531_ = lean_int_neg(v___x_530_);
return v___x_531_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(lean_object* v_one_532_, lean_object* v_a_533_, lean_object* v_a_534_){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v_p_538_; lean_object* v___f_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_536_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1);
v___x_537_ = lean_box(0);
lean_inc(v_one_532_);
v_p_538_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_p_538_, 0, v___x_536_);
lean_ctor_set(v_p_538_, 1, v_one_532_);
lean_ctor_set(v_p_538_, 2, v___x_537_);
lean_inc(v_a_533_);
v___f_539_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_539_, 0, v_a_533_);
lean_closure_set(v___f_539_, 1, v_p_538_);
lean_closure_set(v___f_539_, 2, v_one_532_);
v___x_540_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_541_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_540_, v___f_539_, v_a_534_);
return v___x_541_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_one_532_ = stack[0].m_obj;
lean_object* v_a_533_ = stack[1].m_obj;
lean_object* v_a_534_ = stack[2].m_obj;
lean_object* v_res_542_;
v_res_542_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(v_one_532_, v_a_533_, v_a_534_);
stack->m_obj
 = v_res_542_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___boxed(lean_object* v_one_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(v_one_543_, v_a_544_, v_a_545_);
lean_dec(v_a_545_);
lean_dec(v_a_544_);
return v_res_547_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne(lean_object* v_one_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(v_one_548_, v_a_549_, v_a_550_);
return v___x_561_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_0interp(lean_interpreter_value* stack)
{
lean_object* v_one_548_ = stack[0].m_obj;
lean_object* v_a_549_ = stack[1].m_obj;
lean_object* v_a_550_ = stack[2].m_obj;
lean_object* v_a_551_ = stack[3].m_obj;
lean_object* v_a_552_ = stack[4].m_obj;
lean_object* v_a_553_ = stack[5].m_obj;
lean_object* v_a_554_ = stack[6].m_obj;
lean_object* v_a_555_ = stack[7].m_obj;
lean_object* v_a_556_ = stack[8].m_obj;
lean_object* v_a_557_ = stack[9].m_obj;
lean_object* v_a_558_ = stack[10].m_obj;
lean_object* v_a_559_ = stack[11].m_obj;
lean_object* v_res_562_;
v_res_562_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne(v_one_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
stack->m_obj
 = v_res_562_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___boxed(lean_object* v_one_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne(v_one_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
lean_dec(v_a_570_);
lean_dec_ref(v_a_569_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
lean_dec(v_a_566_);
lean_dec(v_a_565_);
lean_dec(v_a_564_);
return v_res_576_;
}
}
lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0(lean_object* v_p_577_, lean_object* v_x_578_, size_t v_x_579_, size_t v_x_580_){
_start:
{
if (lean_obj_tag(v_x_578_) == 0)
{
lean_object* v_cs_581_; size_t v_j_582_; lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v_cs_581_ = lean_ctor_get(v_x_578_, 0);
v_j_582_ = lean_usize_shift_right(v_x_579_, v_x_580_);
v___x_583_ = lean_usize_to_nat(v_j_582_);
v___x_584_ = lean_array_get_size(v_cs_581_);
v___x_585_ = lean_nat_dec_lt(v___x_583_, v___x_584_);
if (v___x_585_ == 0)
{
lean_dec(v___x_583_);
lean_dec(v_p_577_);
return v_x_578_;
}
else
{
lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_603_; 
lean_inc_ref(v_cs_581_);
v_isSharedCheck_603_ = !lean_is_exclusive(v_x_578_);
if (v_isSharedCheck_603_ == 0)
{
lean_object* v_unused_604_; 
v_unused_604_ = lean_ctor_get(v_x_578_, 0);
lean_dec(v_unused_604_);
v___x_587_ = v_x_578_;
v_isShared_588_ = v_isSharedCheck_603_;
goto v_resetjp_586_;
}
else
{
lean_dec(v_x_578_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_603_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
size_t v___x_589_; size_t v___x_590_; size_t v___x_591_; size_t v_i_592_; size_t v___x_593_; size_t v_shift_594_; lean_object* v_v_595_; lean_object* v___x_596_; lean_object* v_xs_x27_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_589_ = ((size_t)1ULL);
v___x_590_ = lean_usize_shift_left(v___x_589_, v_x_580_);
v___x_591_ = lean_usize_sub(v___x_590_, v___x_589_);
v_i_592_ = lean_usize_land(v_x_579_, v___x_591_);
v___x_593_ = ((size_t)5ULL);
v_shift_594_ = lean_usize_sub(v_x_580_, v___x_593_);
v_v_595_ = lean_array_fget(v_cs_581_, v___x_583_);
v___x_596_ = lean_box(0);
v_xs_x27_597_ = lean_array_fset(v_cs_581_, v___x_583_, v___x_596_);
v___x_598_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0(v_p_577_, v_v_595_, v_i_592_, v_shift_594_);
v___x_599_ = lean_array_fset(v_xs_x27_597_, v___x_583_, v___x_598_);
lean_dec(v___x_583_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_599_);
v___x_601_ = v___x_587_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_599_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
else
{
lean_object* v_vs_605_; lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v_vs_605_ = lean_ctor_get(v_x_578_, 0);
v___x_606_ = lean_usize_to_nat(v_x_579_);
v___x_607_ = lean_array_get_size(v_vs_605_);
v___x_608_ = lean_nat_dec_lt(v___x_606_, v___x_607_);
if (v___x_608_ == 0)
{
lean_dec(v___x_606_);
lean_dec(v_p_577_);
return v_x_578_;
}
else
{
lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_622_; 
lean_inc_ref(v_vs_605_);
v_isSharedCheck_622_ = !lean_is_exclusive(v_x_578_);
if (v_isSharedCheck_622_ == 0)
{
lean_object* v_unused_623_; 
v_unused_623_ = lean_ctor_get(v_x_578_, 0);
lean_dec(v_unused_623_);
v___x_610_ = v_x_578_;
v_isShared_611_ = v_isSharedCheck_622_;
goto v_resetjp_609_;
}
else
{
lean_dec(v_x_578_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_622_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v_v_612_; lean_object* v___x_613_; lean_object* v_xs_x27_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_620_; 
v_v_612_ = lean_array_fget(v_vs_605_, v___x_606_);
v___x_613_ = lean_box(0);
v_xs_x27_614_ = lean_array_fset(v_vs_605_, v___x_606_, v___x_613_);
v___x_615_ = lean_box(6);
v___x_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_616_, 0, v_p_577_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = l_Lean_PersistentArray_push___redArg(v_v_612_, v___x_616_);
v___x_618_ = lean_array_fset(v_xs_x27_614_, v___x_606_, v___x_617_);
lean_dec(v___x_606_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_618_);
v___x_620_ = v___x_610_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_577_ = stack[0].m_obj;
lean_object* v_x_578_ = stack[1].m_obj;
size_t v_x_579_ = stack[2].m_num;
size_t v_x_580_ = stack[3].m_num;
lean_object* v_res_624_;
v_res_624_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0(v_p_577_, v_x_578_, v_x_579_, v_x_580_);
stack->m_obj
 = v_res_624_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0___boxed(lean_object* v_p_625_, lean_object* v_x_626_, lean_object* v_x_627_, lean_object* v_x_628_){
_start:
{
size_t v_x_266__boxed_629_; size_t v_x_267__boxed_630_; lean_object* v_res_631_; 
v_x_266__boxed_629_ = lean_unbox_usize(v_x_627_);
lean_dec(v_x_627_);
v_x_267__boxed_630_ = lean_unbox_usize(v_x_628_);
lean_dec(v_x_628_);
v_res_631_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0(v_p_625_, v_x_626_, v_x_266__boxed_629_, v_x_267__boxed_630_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0(lean_object* v_p_632_, lean_object* v_t_633_, lean_object* v_i_634_){
_start:
{
lean_object* v_root_635_; lean_object* v_tail_636_; lean_object* v_size_637_; size_t v_shift_638_; lean_object* v_tailOff_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_665_; 
v_root_635_ = lean_ctor_get(v_t_633_, 0);
v_tail_636_ = lean_ctor_get(v_t_633_, 1);
v_size_637_ = lean_ctor_get(v_t_633_, 2);
v_shift_638_ = lean_ctor_get_usize(v_t_633_, 4);
v_tailOff_639_ = lean_ctor_get(v_t_633_, 3);
v_isSharedCheck_665_ = !lean_is_exclusive(v_t_633_);
if (v_isSharedCheck_665_ == 0)
{
v___x_641_ = v_t_633_;
v_isShared_642_ = v_isSharedCheck_665_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_tailOff_639_);
lean_inc(v_size_637_);
lean_inc(v_tail_636_);
lean_inc(v_root_635_);
lean_dec(v_t_633_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_665_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
uint8_t v___x_643_; 
v___x_643_ = lean_nat_dec_le(v_tailOff_639_, v_i_634_);
if (v___x_643_ == 0)
{
size_t v___x_644_; lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_644_ = lean_usize_of_nat(v_i_634_);
v___x_645_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0(v_p_632_, v_root_635_, v___x_644_, v_shift_638_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v___x_645_);
v___x_647_ = v___x_641_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_tail_636_);
lean_ctor_set(v_reuseFailAlloc_648_, 2, v_size_637_);
lean_ctor_set(v_reuseFailAlloc_648_, 3, v_tailOff_639_);
lean_ctor_set_usize(v_reuseFailAlloc_648_, 4, v_shift_638_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_649_ = lean_nat_sub(v_i_634_, v_tailOff_639_);
v___x_650_ = lean_array_get_size(v_tail_636_);
v___x_651_ = lean_nat_dec_lt(v___x_649_, v___x_650_);
if (v___x_651_ == 0)
{
lean_object* v___x_653_; 
lean_dec(v___x_649_);
lean_dec(v_p_632_);
if (v_isShared_642_ == 0)
{
v___x_653_ = v___x_641_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_root_635_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_tail_636_);
lean_ctor_set(v_reuseFailAlloc_654_, 2, v_size_637_);
lean_ctor_set(v_reuseFailAlloc_654_, 3, v_tailOff_639_);
lean_ctor_set_usize(v_reuseFailAlloc_654_, 4, v_shift_638_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
else
{
lean_object* v_v_655_; lean_object* v___x_656_; lean_object* v_xs_x27_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
v_v_655_ = lean_array_fget(v_tail_636_, v___x_649_);
v___x_656_ = lean_box(0);
v_xs_x27_657_ = lean_array_fset(v_tail_636_, v___x_649_, v___x_656_);
v___x_658_ = lean_box(6);
v___x_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_659_, 0, v_p_632_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
v___x_660_ = l_Lean_PersistentArray_push___redArg(v_v_655_, v___x_659_);
v___x_661_ = lean_array_fset(v_xs_x27_657_, v___x_649_, v___x_660_);
lean_dec(v___x_649_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 1, v___x_661_);
v___x_663_ = v___x_641_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_root_635_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_664_, 2, v_size_637_);
lean_ctor_set(v_reuseFailAlloc_664_, 3, v_tailOff_639_);
lean_ctor_set_usize(v_reuseFailAlloc_664_, 4, v_shift_638_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0___boxed(lean_object* v_p_666_, lean_object* v_t_667_, lean_object* v_i_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0(v_p_666_, v_t_667_, v_i_668_);
lean_dec(v_i_668_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0(lean_object* v_a_670_, lean_object* v_p_671_, lean_object* v_one_672_, lean_object* v_s_673_){
_start:
{
lean_object* v_structs_674_; lean_object* v_typeIdOf_675_; lean_object* v_exprToStructId_676_; lean_object* v_exprToStructIdEntries_677_; lean_object* v_forbiddenNatModules_678_; lean_object* v_natStructs_679_; lean_object* v_natTypeIdOf_680_; lean_object* v_exprToNatStructId_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v_structs_674_ = lean_ctor_get(v_s_673_, 0);
v_typeIdOf_675_ = lean_ctor_get(v_s_673_, 1);
v_exprToStructId_676_ = lean_ctor_get(v_s_673_, 2);
v_exprToStructIdEntries_677_ = lean_ctor_get(v_s_673_, 3);
v_forbiddenNatModules_678_ = lean_ctor_get(v_s_673_, 4);
v_natStructs_679_ = lean_ctor_get(v_s_673_, 5);
v_natTypeIdOf_680_ = lean_ctor_get(v_s_673_, 6);
v_exprToNatStructId_681_ = lean_ctor_get(v_s_673_, 7);
v___x_682_ = lean_array_get_size(v_structs_674_);
v___x_683_ = lean_nat_dec_lt(v_a_670_, v___x_682_);
if (v___x_683_ == 0)
{
lean_dec(v_p_671_);
return v_s_673_;
}
else
{
lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_745_; 
lean_inc_ref(v_exprToNatStructId_681_);
lean_inc_ref(v_natTypeIdOf_680_);
lean_inc_ref(v_natStructs_679_);
lean_inc_ref(v_forbiddenNatModules_678_);
lean_inc_ref(v_exprToStructIdEntries_677_);
lean_inc_ref(v_exprToStructId_676_);
lean_inc_ref(v_typeIdOf_675_);
lean_inc_ref(v_structs_674_);
v_isSharedCheck_745_ = !lean_is_exclusive(v_s_673_);
if (v_isSharedCheck_745_ == 0)
{
lean_object* v_unused_746_; lean_object* v_unused_747_; lean_object* v_unused_748_; lean_object* v_unused_749_; lean_object* v_unused_750_; lean_object* v_unused_751_; lean_object* v_unused_752_; lean_object* v_unused_753_; 
v_unused_746_ = lean_ctor_get(v_s_673_, 7);
lean_dec(v_unused_746_);
v_unused_747_ = lean_ctor_get(v_s_673_, 6);
lean_dec(v_unused_747_);
v_unused_748_ = lean_ctor_get(v_s_673_, 5);
lean_dec(v_unused_748_);
v_unused_749_ = lean_ctor_get(v_s_673_, 4);
lean_dec(v_unused_749_);
v_unused_750_ = lean_ctor_get(v_s_673_, 3);
lean_dec(v_unused_750_);
v_unused_751_ = lean_ctor_get(v_s_673_, 2);
lean_dec(v_unused_751_);
v_unused_752_ = lean_ctor_get(v_s_673_, 1);
lean_dec(v_unused_752_);
v_unused_753_ = lean_ctor_get(v_s_673_, 0);
lean_dec(v_unused_753_);
v___x_685_ = v_s_673_;
v_isShared_686_ = v_isSharedCheck_745_;
goto v_resetjp_684_;
}
else
{
lean_dec(v_s_673_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_745_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v_v_687_; lean_object* v_id_688_; lean_object* v_ringId_x3f_689_; lean_object* v_type_690_; lean_object* v_u_691_; lean_object* v_intModuleInst_692_; lean_object* v_leInst_x3f_693_; lean_object* v_ltInst_x3f_694_; lean_object* v_lawfulOrderLTInst_x3f_695_; lean_object* v_isPreorderInst_x3f_696_; lean_object* v_orderedAddInst_x3f_697_; lean_object* v_isLinearInst_x3f_698_; lean_object* v_noNatDivInst_x3f_699_; lean_object* v_ringInst_x3f_700_; lean_object* v_commRingInst_x3f_701_; lean_object* v_orderedRingInst_x3f_702_; lean_object* v_fieldInst_x3f_703_; lean_object* v_charInst_x3f_704_; lean_object* v_zero_705_; lean_object* v_ofNatZero_706_; lean_object* v_one_x3f_707_; lean_object* v_leFn_x3f_708_; lean_object* v_ltFn_x3f_709_; lean_object* v_addFn_710_; lean_object* v_zsmulFn_711_; lean_object* v_nsmulFn_712_; lean_object* v_zsmulFn_x3f_713_; lean_object* v_nsmulFn_x3f_714_; lean_object* v_homomulFn_x3f_715_; lean_object* v_subFn_716_; lean_object* v_negFn_717_; lean_object* v_vars_718_; lean_object* v_varMap_719_; lean_object* v_lowers_720_; lean_object* v_uppers_721_; lean_object* v_diseqs_722_; lean_object* v_assignment_723_; uint8_t v_caseSplits_724_; lean_object* v_conflict_x3f_725_; lean_object* v_diseqSplits_726_; lean_object* v_elimEqs_727_; lean_object* v_elimStack_728_; lean_object* v_occurs_729_; lean_object* v_ignored_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_744_; 
v_v_687_ = lean_array_fget(v_structs_674_, v_a_670_);
v_id_688_ = lean_ctor_get(v_v_687_, 0);
v_ringId_x3f_689_ = lean_ctor_get(v_v_687_, 1);
v_type_690_ = lean_ctor_get(v_v_687_, 2);
v_u_691_ = lean_ctor_get(v_v_687_, 3);
v_intModuleInst_692_ = lean_ctor_get(v_v_687_, 4);
v_leInst_x3f_693_ = lean_ctor_get(v_v_687_, 5);
v_ltInst_x3f_694_ = lean_ctor_get(v_v_687_, 6);
v_lawfulOrderLTInst_x3f_695_ = lean_ctor_get(v_v_687_, 7);
v_isPreorderInst_x3f_696_ = lean_ctor_get(v_v_687_, 8);
v_orderedAddInst_x3f_697_ = lean_ctor_get(v_v_687_, 9);
v_isLinearInst_x3f_698_ = lean_ctor_get(v_v_687_, 10);
v_noNatDivInst_x3f_699_ = lean_ctor_get(v_v_687_, 11);
v_ringInst_x3f_700_ = lean_ctor_get(v_v_687_, 12);
v_commRingInst_x3f_701_ = lean_ctor_get(v_v_687_, 13);
v_orderedRingInst_x3f_702_ = lean_ctor_get(v_v_687_, 14);
v_fieldInst_x3f_703_ = lean_ctor_get(v_v_687_, 15);
v_charInst_x3f_704_ = lean_ctor_get(v_v_687_, 16);
v_zero_705_ = lean_ctor_get(v_v_687_, 17);
v_ofNatZero_706_ = lean_ctor_get(v_v_687_, 18);
v_one_x3f_707_ = lean_ctor_get(v_v_687_, 19);
v_leFn_x3f_708_ = lean_ctor_get(v_v_687_, 20);
v_ltFn_x3f_709_ = lean_ctor_get(v_v_687_, 21);
v_addFn_710_ = lean_ctor_get(v_v_687_, 22);
v_zsmulFn_711_ = lean_ctor_get(v_v_687_, 23);
v_nsmulFn_712_ = lean_ctor_get(v_v_687_, 24);
v_zsmulFn_x3f_713_ = lean_ctor_get(v_v_687_, 25);
v_nsmulFn_x3f_714_ = lean_ctor_get(v_v_687_, 26);
v_homomulFn_x3f_715_ = lean_ctor_get(v_v_687_, 27);
v_subFn_716_ = lean_ctor_get(v_v_687_, 28);
v_negFn_717_ = lean_ctor_get(v_v_687_, 29);
v_vars_718_ = lean_ctor_get(v_v_687_, 30);
v_varMap_719_ = lean_ctor_get(v_v_687_, 31);
v_lowers_720_ = lean_ctor_get(v_v_687_, 32);
v_uppers_721_ = lean_ctor_get(v_v_687_, 33);
v_diseqs_722_ = lean_ctor_get(v_v_687_, 34);
v_assignment_723_ = lean_ctor_get(v_v_687_, 35);
v_caseSplits_724_ = lean_ctor_get_uint8(v_v_687_, sizeof(void*)*42);
v_conflict_x3f_725_ = lean_ctor_get(v_v_687_, 36);
v_diseqSplits_726_ = lean_ctor_get(v_v_687_, 37);
v_elimEqs_727_ = lean_ctor_get(v_v_687_, 38);
v_elimStack_728_ = lean_ctor_get(v_v_687_, 39);
v_occurs_729_ = lean_ctor_get(v_v_687_, 40);
v_ignored_730_ = lean_ctor_get(v_v_687_, 41);
v_isSharedCheck_744_ = !lean_is_exclusive(v_v_687_);
if (v_isSharedCheck_744_ == 0)
{
v___x_732_ = v_v_687_;
v_isShared_733_ = v_isSharedCheck_744_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_ignored_730_);
lean_inc(v_occurs_729_);
lean_inc(v_elimStack_728_);
lean_inc(v_elimEqs_727_);
lean_inc(v_diseqSplits_726_);
lean_inc(v_conflict_x3f_725_);
lean_inc(v_assignment_723_);
lean_inc(v_diseqs_722_);
lean_inc(v_uppers_721_);
lean_inc(v_lowers_720_);
lean_inc(v_varMap_719_);
lean_inc(v_vars_718_);
lean_inc(v_negFn_717_);
lean_inc(v_subFn_716_);
lean_inc(v_homomulFn_x3f_715_);
lean_inc(v_nsmulFn_x3f_714_);
lean_inc(v_zsmulFn_x3f_713_);
lean_inc(v_nsmulFn_712_);
lean_inc(v_zsmulFn_711_);
lean_inc(v_addFn_710_);
lean_inc(v_ltFn_x3f_709_);
lean_inc(v_leFn_x3f_708_);
lean_inc(v_one_x3f_707_);
lean_inc(v_ofNatZero_706_);
lean_inc(v_zero_705_);
lean_inc(v_charInst_x3f_704_);
lean_inc(v_fieldInst_x3f_703_);
lean_inc(v_orderedRingInst_x3f_702_);
lean_inc(v_commRingInst_x3f_701_);
lean_inc(v_ringInst_x3f_700_);
lean_inc(v_noNatDivInst_x3f_699_);
lean_inc(v_isLinearInst_x3f_698_);
lean_inc(v_orderedAddInst_x3f_697_);
lean_inc(v_isPreorderInst_x3f_696_);
lean_inc(v_lawfulOrderLTInst_x3f_695_);
lean_inc(v_ltInst_x3f_694_);
lean_inc(v_leInst_x3f_693_);
lean_inc(v_intModuleInst_692_);
lean_inc(v_u_691_);
lean_inc(v_type_690_);
lean_inc(v_ringId_x3f_689_);
lean_inc(v_id_688_);
lean_dec(v_v_687_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_744_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; lean_object* v_xs_x27_735_; lean_object* v___x_736_; lean_object* v___x_738_; 
v___x_734_ = lean_box(0);
v_xs_x27_735_ = lean_array_fset(v_structs_674_, v_a_670_, v___x_734_);
v___x_736_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0(v_p_671_, v_diseqs_722_, v_one_672_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 34, v___x_736_);
v___x_738_ = v___x_732_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_id_688_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_ringId_x3f_689_);
lean_ctor_set(v_reuseFailAlloc_743_, 2, v_type_690_);
lean_ctor_set(v_reuseFailAlloc_743_, 3, v_u_691_);
lean_ctor_set(v_reuseFailAlloc_743_, 4, v_intModuleInst_692_);
lean_ctor_set(v_reuseFailAlloc_743_, 5, v_leInst_x3f_693_);
lean_ctor_set(v_reuseFailAlloc_743_, 6, v_ltInst_x3f_694_);
lean_ctor_set(v_reuseFailAlloc_743_, 7, v_lawfulOrderLTInst_x3f_695_);
lean_ctor_set(v_reuseFailAlloc_743_, 8, v_isPreorderInst_x3f_696_);
lean_ctor_set(v_reuseFailAlloc_743_, 9, v_orderedAddInst_x3f_697_);
lean_ctor_set(v_reuseFailAlloc_743_, 10, v_isLinearInst_x3f_698_);
lean_ctor_set(v_reuseFailAlloc_743_, 11, v_noNatDivInst_x3f_699_);
lean_ctor_set(v_reuseFailAlloc_743_, 12, v_ringInst_x3f_700_);
lean_ctor_set(v_reuseFailAlloc_743_, 13, v_commRingInst_x3f_701_);
lean_ctor_set(v_reuseFailAlloc_743_, 14, v_orderedRingInst_x3f_702_);
lean_ctor_set(v_reuseFailAlloc_743_, 15, v_fieldInst_x3f_703_);
lean_ctor_set(v_reuseFailAlloc_743_, 16, v_charInst_x3f_704_);
lean_ctor_set(v_reuseFailAlloc_743_, 17, v_zero_705_);
lean_ctor_set(v_reuseFailAlloc_743_, 18, v_ofNatZero_706_);
lean_ctor_set(v_reuseFailAlloc_743_, 19, v_one_x3f_707_);
lean_ctor_set(v_reuseFailAlloc_743_, 20, v_leFn_x3f_708_);
lean_ctor_set(v_reuseFailAlloc_743_, 21, v_ltFn_x3f_709_);
lean_ctor_set(v_reuseFailAlloc_743_, 22, v_addFn_710_);
lean_ctor_set(v_reuseFailAlloc_743_, 23, v_zsmulFn_711_);
lean_ctor_set(v_reuseFailAlloc_743_, 24, v_nsmulFn_712_);
lean_ctor_set(v_reuseFailAlloc_743_, 25, v_zsmulFn_x3f_713_);
lean_ctor_set(v_reuseFailAlloc_743_, 26, v_nsmulFn_x3f_714_);
lean_ctor_set(v_reuseFailAlloc_743_, 27, v_homomulFn_x3f_715_);
lean_ctor_set(v_reuseFailAlloc_743_, 28, v_subFn_716_);
lean_ctor_set(v_reuseFailAlloc_743_, 29, v_negFn_717_);
lean_ctor_set(v_reuseFailAlloc_743_, 30, v_vars_718_);
lean_ctor_set(v_reuseFailAlloc_743_, 31, v_varMap_719_);
lean_ctor_set(v_reuseFailAlloc_743_, 32, v_lowers_720_);
lean_ctor_set(v_reuseFailAlloc_743_, 33, v_uppers_721_);
lean_ctor_set(v_reuseFailAlloc_743_, 34, v___x_736_);
lean_ctor_set(v_reuseFailAlloc_743_, 35, v_assignment_723_);
lean_ctor_set(v_reuseFailAlloc_743_, 36, v_conflict_x3f_725_);
lean_ctor_set(v_reuseFailAlloc_743_, 37, v_diseqSplits_726_);
lean_ctor_set(v_reuseFailAlloc_743_, 38, v_elimEqs_727_);
lean_ctor_set(v_reuseFailAlloc_743_, 39, v_elimStack_728_);
lean_ctor_set(v_reuseFailAlloc_743_, 40, v_occurs_729_);
lean_ctor_set(v_reuseFailAlloc_743_, 41, v_ignored_730_);
lean_ctor_set_uint8(v_reuseFailAlloc_743_, sizeof(void*)*42, v_caseSplits_724_);
v___x_738_ = v_reuseFailAlloc_743_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_739_ = lean_array_fset(v_xs_x27_735_, v_a_670_, v___x_738_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 0, v___x_739_);
v___x_741_ = v___x_685_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_typeIdOf_675_);
lean_ctor_set(v_reuseFailAlloc_742_, 2, v_exprToStructId_676_);
lean_ctor_set(v_reuseFailAlloc_742_, 3, v_exprToStructIdEntries_677_);
lean_ctor_set(v_reuseFailAlloc_742_, 4, v_forbiddenNatModules_678_);
lean_ctor_set(v_reuseFailAlloc_742_, 5, v_natStructs_679_);
lean_ctor_set(v_reuseFailAlloc_742_, 6, v_natTypeIdOf_680_);
lean_ctor_set(v_reuseFailAlloc_742_, 7, v_exprToNatStructId_681_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0___boxed(lean_object* v_a_754_, lean_object* v_p_755_, lean_object* v_one_756_, lean_object* v_s_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0(v_a_754_, v_p_755_, v_one_756_, v_s_757_);
lean_dec(v_one_756_);
lean_dec(v_a_754_);
return v_res_758_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(lean_object* v_one_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v_p_765_; lean_object* v___f_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_763_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0);
v___x_764_ = lean_box(0);
lean_inc(v_one_759_);
v_p_765_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_p_765_, 0, v___x_763_);
lean_ctor_set(v_p_765_, 1, v_one_759_);
lean_ctor_set(v_p_765_, 2, v___x_764_);
lean_inc(v_a_760_);
v___f_766_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_766_, 0, v_a_760_);
lean_closure_set(v___f_766_, 1, v_p_765_);
lean_closure_set(v___f_766_, 2, v_one_759_);
v___x_767_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_768_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_767_, v___f_766_, v_a_761_);
return v___x_768_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_one_759_ = stack[0].m_obj;
lean_object* v_a_760_ = stack[1].m_obj;
lean_object* v_a_761_ = stack[2].m_obj;
lean_object* v_res_769_;
v_res_769_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_one_759_, v_a_760_, v_a_761_);
stack->m_obj
 = v_res_769_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___boxed(lean_object* v_one_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_one_770_, v_a_771_, v_a_772_);
lean_dec(v_a_772_);
lean_dec(v_a_771_);
return v_res_774_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne(lean_object* v_one_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_one_775_, v_a_776_, v_a_777_);
return v___x_788_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_0interp(lean_interpreter_value* stack)
{
lean_object* v_one_775_ = stack[0].m_obj;
lean_object* v_a_776_ = stack[1].m_obj;
lean_object* v_a_777_ = stack[2].m_obj;
lean_object* v_a_778_ = stack[3].m_obj;
lean_object* v_a_779_ = stack[4].m_obj;
lean_object* v_a_780_ = stack[5].m_obj;
lean_object* v_a_781_ = stack[6].m_obj;
lean_object* v_a_782_ = stack[7].m_obj;
lean_object* v_a_783_ = stack[8].m_obj;
lean_object* v_a_784_ = stack[9].m_obj;
lean_object* v_a_785_ = stack[10].m_obj;
lean_object* v_a_786_ = stack[11].m_obj;
lean_object* v_res_789_;
v_res_789_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne(v_one_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
stack->m_obj
 = v_res_789_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___boxed(lean_object* v_one_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne(v_one_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
lean_dec(v_a_793_);
lean_dec(v_a_792_);
lean_dec(v_a_791_);
return v_res_803_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(lean_object* v_isCharInst_x3f_804_){
_start:
{
if (lean_obj_tag(v_isCharInst_x3f_804_) == 0)
{
uint8_t v___x_805_; 
v___x_805_ = 0;
return v___x_805_;
}
else
{
lean_object* v_val_806_; lean_object* v_snd_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v_val_806_ = lean_ctor_get(v_isCharInst_x3f_804_, 0);
v_snd_807_ = lean_ctor_get(v_val_806_, 1);
v___x_808_ = lean_unsigned_to_nat(1u);
v___x_809_ = lean_nat_dec_eq(v_snd_807_, v___x_808_);
if (v___x_809_ == 0)
{
uint8_t v___x_810_; 
v___x_810_ = 1;
return v___x_810_;
}
else
{
uint8_t v___x_811_; 
v___x_811_ = 0;
return v___x_811_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_isCharInst_x3f_804_ = stack[0].m_obj;
uint8_t v_res_812_;
v_res_812_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(v_isCharInst_x3f_804_);
stack->m_num = v_res_812_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst___boxed(lean_object* v_isCharInst_x3f_813_){
_start:
{
uint8_t v_res_814_; lean_object* v_r_815_; 
v_res_814_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(v_isCharInst_x3f_813_);
lean_dec(v_isCharInst_x3f_813_);
v_r_815_ = lean_box(v_res_814_);
return v_r_815_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___redArg(lean_object* v_type_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_817_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v_a_825_; uint8_t v_lia_826_; 
v_a_825_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_a_825_);
lean_dec_ref_known(v___x_824_, 1);
v_lia_826_ = lean_ctor_get_uint8(v_a_825_, sizeof(void*)*14 + 23);
lean_dec(v_a_825_);
if (v_lia_826_ == 0)
{
lean_dec_ref(v_type_816_);
goto v___jp_820_;
}
else
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg(v_type_816_, v_a_818_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_837_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_837_ == 0)
{
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_837_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_837_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
uint8_t v___x_832_; 
v___x_832_ = lean_unbox(v_a_828_);
lean_dec(v_a_828_);
if (v___x_832_ == 0)
{
lean_del_object(v___x_830_);
goto v___jp_820_;
}
else
{
lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_833_ = lean_box(v_lia_826_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_833_);
v___x_835_ = v___x_830_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
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
else
{
return v___x_827_;
}
}
}
else
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
lean_dec_ref(v_type_816_);
v_a_838_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_824_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_824_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
v___jp_820_:
{
uint8_t v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_821_ = 0;
v___x_822_ = lean_box(v___x_821_);
v___x_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
return v___x_823_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_816_ = stack[0].m_obj;
lean_object* v_a_817_ = stack[1].m_obj;
lean_object* v_a_818_ = stack[2].m_obj;
lean_object* v_res_846_;
v_res_846_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___redArg(v_type_816_, v_a_817_, v_a_818_);
stack->m_obj
 = v_res_846_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___redArg___boxed(lean_object* v_type_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___redArg(v_type_847_, v_a_848_, v_a_849_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
return v_res_851_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(lean_object* v_type_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___redArg(v_type_852_, v_a_855_, v_a_860_);
return v___x_864_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_852_ = stack[0].m_obj;
lean_object* v_a_853_ = stack[1].m_obj;
lean_object* v_a_854_ = stack[2].m_obj;
lean_object* v_a_855_ = stack[3].m_obj;
lean_object* v_a_856_ = stack[4].m_obj;
lean_object* v_a_857_ = stack[5].m_obj;
lean_object* v_a_858_ = stack[6].m_obj;
lean_object* v_a_859_ = stack[7].m_obj;
lean_object* v_a_860_ = stack[8].m_obj;
lean_object* v_a_861_ = stack[9].m_obj;
lean_object* v_a_862_ = stack[10].m_obj;
lean_object* v_res_865_;
v_res_865_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(v_type_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_);
stack->m_obj
 = v_res_865_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___boxed(lean_object* v_type_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(v_type_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
lean_dec(v_a_872_);
lean_dec_ref(v_a_871_);
lean_dec(v_a_870_);
lean_dec_ref(v_a_869_);
lean_dec(v_a_868_);
lean_dec(v_a_867_);
return v_res_878_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(lean_object* v_ringId_x3f_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
if (lean_obj_tag(v_ringId_x3f_879_) == 1)
{
lean_object* v_val_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_918_; 
v_val_891_ = lean_ctor_get(v_ringId_x3f_879_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v_ringId_x3f_879_);
if (v_isSharedCheck_918_ == 0)
{
v___x_893_ = v_ringId_x3f_879_;
v_isShared_894_ = v_isSharedCheck_918_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_val_891_);
lean_dec(v_ringId_x3f_879_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_918_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
uint8_t v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_895_ = 0;
v___x_896_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_896_, 0, v_val_891_);
lean_ctor_set_uint8(v___x_896_, sizeof(void*)*1, v___x_895_);
v___x_897_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___x_896_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
lean_dec_ref_known(v___x_896_, 1);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_909_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_909_ == 0)
{
v___x_900_ = v___x_897_;
v_isShared_901_ = v_isSharedCheck_909_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_897_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_909_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v_commRingInst_902_; lean_object* v___x_904_; 
v_commRingInst_902_ = lean_ctor_get(v_a_898_, 5);
lean_inc_ref(v_commRingInst_902_);
lean_dec(v_a_898_);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 0, v_commRingInst_902_);
v___x_904_ = v___x_893_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_commRingInst_902_);
v___x_904_ = v_reuseFailAlloc_908_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
lean_object* v___x_906_; 
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v___x_904_);
v___x_906_ = v___x_900_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_904_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
else
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
lean_del_object(v___x_893_);
v_a_910_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_897_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_897_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; 
lean_dec(v_ringId_x3f_879_);
v___x_919_ = lean_box(0);
v___x_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
return v___x_920_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_ringId_x3f_879_ = stack[0].m_obj;
lean_object* v_a_880_ = stack[1].m_obj;
lean_object* v_a_881_ = stack[2].m_obj;
lean_object* v_a_882_ = stack[3].m_obj;
lean_object* v_a_883_ = stack[4].m_obj;
lean_object* v_a_884_ = stack[5].m_obj;
lean_object* v_a_885_ = stack[6].m_obj;
lean_object* v_a_886_ = stack[7].m_obj;
lean_object* v_a_887_ = stack[8].m_obj;
lean_object* v_a_888_ = stack[9].m_obj;
lean_object* v_a_889_ = stack[10].m_obj;
lean_object* v_res_921_;
v_res_921_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(v_ringId_x3f_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
stack->m_obj
 = v_res_921_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f___boxed(lean_object* v_ringId_x3f_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(v_ringId_x3f_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_);
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
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(lean_object* v_u_949_, lean_object* v_type_950_, lean_object* v_commRingInst_x3f_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
if (lean_obj_tag(v_commRingInst_x3f_951_) == 1)
{
lean_object* v_val_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_971_; 
v_val_958_ = lean_ctor_get(v_commRingInst_x3f_951_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v_commRingInst_x3f_951_);
if (v_isSharedCheck_971_ == 0)
{
v___x_960_ = v_commRingInst_x3f_951_;
v_isShared_961_ = v_isSharedCheck_971_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_val_958_);
lean_dec(v_commRingInst_x3f_951_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_971_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_962_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4));
v___x_963_ = lean_box(0);
v___x_964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_964_, 0, v_u_949_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = l_Lean_mkConst(v___x_962_, v___x_964_);
v___x_966_ = l_Lean_mkAppB(v___x_965_, v_type_950_, v_val_958_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 0, v___x_966_);
v___x_968_ = v___x_960_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_966_);
v___x_968_ = v_reuseFailAlloc_970_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
lean_object* v___x_969_; 
v___x_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
return v___x_969_;
}
}
}
else
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
lean_dec(v_commRingInst_x3f_951_);
v___x_972_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6));
v___x_973_ = lean_box(0);
v___x_974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_974_, 0, v_u_949_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = l_Lean_mkConst(v___x_972_, v___x_974_);
v___x_976_ = l_Lean_Expr_app___override(v___x_975_, v_type_950_);
v___x_977_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_976_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
return v___x_977_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_949_ = stack[0].m_obj;
lean_object* v_type_950_ = stack[1].m_obj;
lean_object* v_commRingInst_x3f_951_ = stack[2].m_obj;
lean_object* v_a_952_ = stack[3].m_obj;
lean_object* v_a_953_ = stack[4].m_obj;
lean_object* v_a_954_ = stack[5].m_obj;
lean_object* v_a_955_ = stack[6].m_obj;
lean_object* v_a_956_ = stack[7].m_obj;
lean_object* v_res_978_;
v_res_978_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_u_949_, v_type_950_, v_commRingInst_x3f_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
stack->m_obj
 = v_res_978_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___boxed(lean_object* v_u_979_, lean_object* v_type_980_, lean_object* v_commRingInst_x3f_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_u_979_, v_type_980_, v_commRingInst_x3f_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
return v_res_988_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f(lean_object* v_u_989_, lean_object* v_type_990_, lean_object* v_commRingInst_x3f_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_u_989_, v_type_990_, v_commRingInst_x3f_991_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_);
return v___x_1003_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_989_ = stack[0].m_obj;
lean_object* v_type_990_ = stack[1].m_obj;
lean_object* v_commRingInst_x3f_991_ = stack[2].m_obj;
lean_object* v_a_992_ = stack[3].m_obj;
lean_object* v_a_993_ = stack[4].m_obj;
lean_object* v_a_994_ = stack[5].m_obj;
lean_object* v_a_995_ = stack[6].m_obj;
lean_object* v_a_996_ = stack[7].m_obj;
lean_object* v_a_997_ = stack[8].m_obj;
lean_object* v_a_998_ = stack[9].m_obj;
lean_object* v_a_999_ = stack[10].m_obj;
lean_object* v_a_1000_ = stack[11].m_obj;
lean_object* v_a_1001_ = stack[12].m_obj;
lean_object* v_res_1004_;
v_res_1004_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f(v_u_989_, v_type_990_, v_commRingInst_x3f_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_);
stack->m_obj
 = v_res_1004_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___boxed(lean_object* v_u_1005_, lean_object* v_type_1006_, lean_object* v_commRingInst_x3f_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f(v_u_1005_, v_type_1006_, v_commRingInst_x3f_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
lean_dec(v_a_1013_);
lean_dec_ref(v_a_1012_);
lean_dec(v_a_1011_);
lean_dec_ref(v_a_1010_);
lean_dec(v_a_1009_);
lean_dec(v_a_1008_);
return v_res_1019_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(lean_object* v_u_1031_, lean_object* v_type_1032_, lean_object* v_ringInst_x3f_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
if (lean_obj_tag(v_ringInst_x3f_1033_) == 1)
{
lean_object* v_val_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1053_; 
v_val_1040_ = lean_ctor_get(v_ringInst_x3f_1033_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_ringInst_x3f_1033_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1042_ = v_ringInst_x3f_1033_;
v_isShared_1043_ = v_isSharedCheck_1053_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_val_1040_);
lean_dec(v_ringInst_x3f_1033_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1053_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1044_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1));
v___x_1045_ = lean_box(0);
v___x_1046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1046_, 0, v_u_1031_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = l_Lean_mkConst(v___x_1044_, v___x_1046_);
v___x_1048_ = l_Lean_mkAppB(v___x_1047_, v_type_1032_, v_val_1040_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v___x_1048_);
v___x_1050_ = v___x_1042_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
return v___x_1051_;
}
}
}
else
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
lean_dec(v_ringInst_x3f_1033_);
v___x_1054_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3));
v___x_1055_ = lean_box(0);
v___x_1056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1056_, 0, v_u_1031_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = l_Lean_mkConst(v___x_1054_, v___x_1056_);
v___x_1058_ = l_Lean_Expr_app___override(v___x_1057_, v_type_1032_);
v___x_1059_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1058_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
return v___x_1059_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1031_ = stack[0].m_obj;
lean_object* v_type_1032_ = stack[1].m_obj;
lean_object* v_ringInst_x3f_1033_ = stack[2].m_obj;
lean_object* v_a_1034_ = stack[3].m_obj;
lean_object* v_a_1035_ = stack[4].m_obj;
lean_object* v_a_1036_ = stack[5].m_obj;
lean_object* v_a_1037_ = stack[6].m_obj;
lean_object* v_a_1038_ = stack[7].m_obj;
lean_object* v_res_1060_;
v_res_1060_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_u_1031_, v_type_1032_, v_ringInst_x3f_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
stack->m_obj
 = v_res_1060_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___boxed(lean_object* v_u_1061_, lean_object* v_type_1062_, lean_object* v_ringInst_x3f_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_u_1061_, v_type_1062_, v_ringInst_x3f_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
lean_dec(v_a_1064_);
return v_res_1070_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f(lean_object* v_u_1071_, lean_object* v_type_1072_, lean_object* v_ringInst_x3f_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_u_1071_, v_type_1072_, v_ringInst_x3f_1073_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
return v___x_1085_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1071_ = stack[0].m_obj;
lean_object* v_type_1072_ = stack[1].m_obj;
lean_object* v_ringInst_x3f_1073_ = stack[2].m_obj;
lean_object* v_a_1074_ = stack[3].m_obj;
lean_object* v_a_1075_ = stack[4].m_obj;
lean_object* v_a_1076_ = stack[5].m_obj;
lean_object* v_a_1077_ = stack[6].m_obj;
lean_object* v_a_1078_ = stack[7].m_obj;
lean_object* v_a_1079_ = stack[8].m_obj;
lean_object* v_a_1080_ = stack[9].m_obj;
lean_object* v_a_1081_ = stack[10].m_obj;
lean_object* v_a_1082_ = stack[11].m_obj;
lean_object* v_a_1083_ = stack[12].m_obj;
lean_object* v_res_1086_;
v_res_1086_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f(v_u_1071_, v_type_1072_, v_ringInst_x3f_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
stack->m_obj
 = v_res_1086_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___boxed(lean_object* v_u_1087_, lean_object* v_type_1088_, lean_object* v_ringInst_x3f_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f(v_u_1087_, v_type_1088_, v_ringInst_x3f_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
lean_dec(v_a_1095_);
lean_dec_ref(v_a_1094_);
lean_dec(v_a_1093_);
lean_dec_ref(v_a_1092_);
lean_dec(v_a_1091_);
lean_dec(v_a_1090_);
return v_res_1101_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(lean_object* v_u_1113_, lean_object* v_type_1114_, lean_object* v_ringInst_x3f_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
if (lean_obj_tag(v_ringInst_x3f_1115_) == 1)
{
lean_object* v_val_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1135_; 
v_val_1122_ = lean_ctor_get(v_ringInst_x3f_1115_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v_ringInst_x3f_1115_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1124_ = v_ringInst_x3f_1115_;
v_isShared_1125_ = v_isSharedCheck_1135_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_val_1122_);
lean_dec(v_ringInst_x3f_1115_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1135_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1126_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1));
v___x_1127_ = lean_box(0);
v___x_1128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1128_, 0, v_u_1113_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = l_Lean_mkConst(v___x_1126_, v___x_1128_);
v___x_1130_ = l_Lean_mkAppB(v___x_1129_, v_type_1114_, v_val_1122_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v___x_1130_);
v___x_1132_ = v___x_1124_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1133_; 
v___x_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
return v___x_1133_;
}
}
}
else
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
lean_dec(v_ringInst_x3f_1115_);
v___x_1136_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__3));
v___x_1137_ = lean_box(0);
v___x_1138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1138_, 0, v_u_1113_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
v___x_1139_ = l_Lean_mkConst(v___x_1136_, v___x_1138_);
v___x_1140_ = l_Lean_Expr_app___override(v___x_1139_, v_type_1114_);
v___x_1141_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1140_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
return v___x_1141_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1113_ = stack[0].m_obj;
lean_object* v_type_1114_ = stack[1].m_obj;
lean_object* v_ringInst_x3f_1115_ = stack[2].m_obj;
lean_object* v_a_1116_ = stack[3].m_obj;
lean_object* v_a_1117_ = stack[4].m_obj;
lean_object* v_a_1118_ = stack[5].m_obj;
lean_object* v_a_1119_ = stack[6].m_obj;
lean_object* v_a_1120_ = stack[7].m_obj;
lean_object* v_res_1142_;
v_res_1142_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_u_1113_, v_type_1114_, v_ringInst_x3f_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
stack->m_obj
 = v_res_1142_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___boxed(lean_object* v_u_1143_, lean_object* v_type_1144_, lean_object* v_ringInst_x3f_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_u_1143_, v_type_1144_, v_ringInst_x3f_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
lean_dec(v_a_1150_);
lean_dec_ref(v_a_1149_);
lean_dec(v_a_1148_);
lean_dec_ref(v_a_1147_);
lean_dec(v_a_1146_);
return v_res_1152_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f(lean_object* v_u_1153_, lean_object* v_type_1154_, lean_object* v_ringInst_x3f_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_u_1153_, v_type_1154_, v_ringInst_x3f_1155_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
return v___x_1167_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1153_ = stack[0].m_obj;
lean_object* v_type_1154_ = stack[1].m_obj;
lean_object* v_ringInst_x3f_1155_ = stack[2].m_obj;
lean_object* v_a_1156_ = stack[3].m_obj;
lean_object* v_a_1157_ = stack[4].m_obj;
lean_object* v_a_1158_ = stack[5].m_obj;
lean_object* v_a_1159_ = stack[6].m_obj;
lean_object* v_a_1160_ = stack[7].m_obj;
lean_object* v_a_1161_ = stack[8].m_obj;
lean_object* v_a_1162_ = stack[9].m_obj;
lean_object* v_a_1163_ = stack[10].m_obj;
lean_object* v_a_1164_ = stack[11].m_obj;
lean_object* v_a_1165_ = stack[12].m_obj;
lean_object* v_res_1168_;
v_res_1168_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f(v_u_1153_, v_type_1154_, v_ringInst_x3f_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
stack->m_obj
 = v_res_1168_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___boxed(lean_object* v_u_1169_, lean_object* v_type_1170_, lean_object* v_ringInst_x3f_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f(v_u_1169_, v_type_1170_, v_ringInst_x3f_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
lean_dec(v_a_1181_);
lean_dec_ref(v_a_1180_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
lean_dec(v_a_1175_);
lean_dec_ref(v_a_1174_);
lean_dec(v_a_1173_);
lean_dec(v_a_1172_);
return v_res_1183_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(lean_object* v_u_1191_, lean_object* v_type_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1204_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__1));
v___x_1205_ = lean_box(0);
v___x_1206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1206_, 0, v_u_1191_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
lean_inc_ref(v___x_1206_);
v___x_1207_ = l_Lean_mkConst(v___x_1204_, v___x_1206_);
lean_inc_ref(v_type_1192_);
v___x_1208_ = l_Lean_Expr_app___override(v___x_1207_, v_type_1192_);
v___x_1209_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1208_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1291_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1212_ = v___x_1209_;
v_isShared_1213_ = v_isSharedCheck_1291_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1209_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1291_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
if (lean_obj_tag(v_a_1210_) == 1)
{
lean_object* v_val_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1286_; 
lean_del_object(v___x_1212_);
v_val_1214_ = lean_ctor_get(v_a_1210_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_a_1210_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1216_ = v_a_1210_;
v_isShared_1217_ = v_isSharedCheck_1286_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_val_1214_);
lean_dec(v_a_1210_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1286_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__3));
v___x_1219_ = l_Lean_mkConst(v___x_1218_, v___x_1206_);
lean_inc_ref(v_type_1192_);
v___x_1220_ = l_Lean_mkAppB(v___x_1219_, v_type_1192_, v_val_1214_);
v___x_1221_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_1220_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1277_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1224_ = v___x_1221_;
v_isShared_1225_ = v_isSharedCheck_1277_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1221_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1277_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = lean_unsigned_to_nat(1u);
v___x_1234_ = l_Lean_Meta_mkNumeral(v_type_1192_, v___x_1233_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; lean_object* v___x_1236_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc_n(v_a_1235_, 2);
lean_dec_ref_known(v___x_1234_, 1);
lean_inc(v_a_1222_);
v___x_1236_ = l_Lean_Meta_isDefEqD(v_a_1222_, v_a_1235_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; uint8_t v___x_1238_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_a_1237_);
lean_dec_ref_known(v___x_1236_, 1);
v___x_1238_ = lean_unbox(v_a_1237_);
lean_dec(v_a_1237_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; lean_object* v_a_1240_; lean_object* v___x_1241_; 
lean_inc(v_a_1222_);
v___x_1239_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_a_1222_, v_a_1235_);
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_a_1240_);
lean_dec_ref(v___x_1239_);
v___x_1241_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1197_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; uint8_t v_verbose_1243_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___x_1241_, 1);
v_verbose_1243_ = lean_ctor_get_uint8(v_a_1242_, 0);
lean_dec(v_a_1242_);
if (v_verbose_1243_ == 0)
{
lean_dec(v_a_1240_);
goto v___jp_1226_;
}
else
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Lean_Meta_Sym_reportIssue(v_a_1240_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_dec_ref_known(v___x_1244_, 1);
goto v___jp_1226_;
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_del_object(v___x_1224_);
lean_dec(v_a_1222_);
lean_del_object(v___x_1216_);
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1244_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1244_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
lean_dec(v_a_1240_);
lean_del_object(v___x_1224_);
lean_dec(v_a_1222_);
lean_del_object(v___x_1216_);
v_a_1253_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___x_1241_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1241_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
else
{
lean_dec(v_a_1235_);
goto v___jp_1226_;
}
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
lean_dec(v_a_1235_);
lean_del_object(v___x_1224_);
lean_dec(v_a_1222_);
lean_del_object(v___x_1216_);
v_a_1261_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1236_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1236_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_del_object(v___x_1224_);
lean_dec(v_a_1222_);
lean_del_object(v___x_1216_);
v_a_1269_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1234_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1234_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
v___jp_1226_:
{
lean_object* v___x_1228_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v_a_1222_);
v___x_1228_ = v___x_1216_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1222_);
v___x_1228_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
lean_object* v___x_1230_; 
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v___x_1228_);
v___x_1230_ = v___x_1224_;
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
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
lean_del_object(v___x_1216_);
lean_dec_ref(v_type_1192_);
v_a_1278_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1221_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1221_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
}
else
{
lean_object* v___x_1287_; lean_object* v___x_1289_; 
lean_dec(v_a_1210_);
lean_dec_ref_known(v___x_1206_, 2);
lean_dec_ref(v_type_1192_);
v___x_1287_ = lean_box(0);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 0, v___x_1287_);
v___x_1289_ = v___x_1212_;
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
lean_dec_ref_known(v___x_1206_, 2);
lean_dec_ref(v_type_1192_);
return v___x_1209_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1191_ = stack[0].m_obj;
lean_object* v_type_1192_ = stack[1].m_obj;
lean_object* v_a_1193_ = stack[2].m_obj;
lean_object* v_a_1194_ = stack[3].m_obj;
lean_object* v_a_1195_ = stack[4].m_obj;
lean_object* v_a_1196_ = stack[5].m_obj;
lean_object* v_a_1197_ = stack[6].m_obj;
lean_object* v_a_1198_ = stack[7].m_obj;
lean_object* v_a_1199_ = stack[8].m_obj;
lean_object* v_a_1200_ = stack[9].m_obj;
lean_object* v_a_1201_ = stack[10].m_obj;
lean_object* v_a_1202_ = stack[11].m_obj;
lean_object* v_res_1292_;
v_res_1292_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(v_u_1191_, v_type_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_);
stack->m_obj
 = v_res_1292_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___boxed(lean_object* v_u_1293_, lean_object* v_type_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(v_u_1293_, v_type_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
lean_dec(v_a_1296_);
lean_dec(v_a_1295_);
return v_res_1306_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3(void){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__2));
v___x_1314_ = l_Lean_stringToMessageData(v___x_1313_);
return v___x_1314_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(lean_object* v_u_1315_, lean_object* v_type_1316_, lean_object* v_semiringInst_x3f_1317_, lean_object* v_leInst_x3f_1318_, lean_object* v_ltInst_x3f_1319_, lean_object* v_preorderInst_x3f_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_){
_start:
{
if (lean_obj_tag(v_semiringInst_x3f_1317_) == 1)
{
if (lean_obj_tag(v_leInst_x3f_1318_) == 1)
{
if (lean_obj_tag(v_ltInst_x3f_1319_) == 1)
{
if (lean_obj_tag(v_preorderInst_x3f_1320_) == 1)
{
lean_object* v_val_1331_; lean_object* v_val_1332_; lean_object* v_val_1333_; lean_object* v_val_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v_isOrdType_1339_; lean_object* v___x_1340_; 
v_val_1331_ = lean_ctor_get(v_semiringInst_x3f_1317_, 0);
lean_inc(v_val_1331_);
lean_dec_ref_known(v_semiringInst_x3f_1317_, 1);
v_val_1332_ = lean_ctor_get(v_leInst_x3f_1318_, 0);
lean_inc(v_val_1332_);
lean_dec_ref_known(v_leInst_x3f_1318_, 1);
v_val_1333_ = lean_ctor_get(v_ltInst_x3f_1319_, 0);
lean_inc(v_val_1333_);
lean_dec_ref_known(v_ltInst_x3f_1319_, 1);
v_val_1334_ = lean_ctor_get(v_preorderInst_x3f_1320_, 0);
lean_inc(v_val_1334_);
lean_dec_ref_known(v_preorderInst_x3f_1320_, 1);
v___x_1335_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__1));
v___x_1336_ = lean_box(0);
v___x_1337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1337_, 0, v_u_1315_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
v___x_1338_ = l_Lean_mkConst(v___x_1335_, v___x_1337_);
v_isOrdType_1339_ = l_Lean_mkApp5(v___x_1338_, v_type_1316_, v_val_1331_, v_val_1332_, v_val_1333_, v_val_1334_);
lean_inc_ref(v_isOrdType_1339_);
v___x_1340_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_isOrdType_1339_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
if (lean_obj_tag(v_a_1341_) == 1)
{
lean_dec_ref(v_isOrdType_1339_);
return v___x_1340_;
}
else
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
lean_dec_ref_known(v___x_1340_, 1);
v___x_1342_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3);
v___x_1343_ = l_Lean_indentExpr(v_isOrdType_1339_);
v___x_1344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1342_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
v___x_1345_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1321_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; uint8_t v_verbose_1347_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref_known(v___x_1345_, 1);
v_verbose_1347_ = lean_ctor_get_uint8(v_a_1346_, 0);
lean_dec(v_a_1346_);
if (v_verbose_1347_ == 0)
{
lean_dec_ref_known(v___x_1344_, 2);
goto v___jp_1328_;
}
else
{
lean_object* v___x_1348_; 
v___x_1348_ = l_Lean_Meta_Sym_reportIssue(v___x_1344_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_dec_ref_known(v___x_1348_, 1);
goto v___jp_1328_;
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1348_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1348_);
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
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec_ref_known(v___x_1344_, 2);
v_a_1357_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1345_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1345_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
}
else
{
lean_dec_ref(v_isOrdType_1339_);
return v___x_1340_;
}
}
else
{
lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1372_; 
lean_dec_ref_known(v_leInst_x3f_1318_, 1);
lean_dec_ref_known(v_semiringInst_x3f_1317_, 1);
lean_dec(v_preorderInst_x3f_1320_);
lean_dec_ref(v_type_1316_);
lean_dec(v_u_1315_);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_ltInst_x3f_1319_);
if (v_isSharedCheck_1372_ == 0)
{
lean_object* v_unused_1373_; 
v_unused_1373_ = lean_ctor_get(v_ltInst_x3f_1319_, 0);
lean_dec(v_unused_1373_);
v___x_1366_ = v_ltInst_x3f_1319_;
v_isShared_1367_ = v_isSharedCheck_1372_;
goto v_resetjp_1365_;
}
else
{
lean_dec(v_ltInst_x3f_1319_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1372_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1368_ = lean_box(0);
if (v_isShared_1367_ == 0)
{
lean_ctor_set_tag(v___x_1366_, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1368_);
v___x_1370_ = v___x_1366_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1368_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
else
{
lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1381_; 
lean_dec_ref_known(v_semiringInst_x3f_1317_, 1);
lean_dec(v_preorderInst_x3f_1320_);
lean_dec(v_ltInst_x3f_1319_);
lean_dec_ref(v_type_1316_);
lean_dec(v_u_1315_);
v_isSharedCheck_1381_ = !lean_is_exclusive(v_leInst_x3f_1318_);
if (v_isSharedCheck_1381_ == 0)
{
lean_object* v_unused_1382_; 
v_unused_1382_ = lean_ctor_get(v_leInst_x3f_1318_, 0);
lean_dec(v_unused_1382_);
v___x_1375_ = v_leInst_x3f_1318_;
v_isShared_1376_ = v_isSharedCheck_1381_;
goto v_resetjp_1374_;
}
else
{
lean_dec(v_leInst_x3f_1318_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1381_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1377_ = lean_box(0);
if (v_isShared_1376_ == 0)
{
lean_ctor_set_tag(v___x_1375_, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1377_);
v___x_1379_ = v___x_1375_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
else
{
lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1390_; 
lean_dec(v_preorderInst_x3f_1320_);
lean_dec(v_ltInst_x3f_1319_);
lean_dec(v_leInst_x3f_1318_);
lean_dec_ref(v_type_1316_);
lean_dec(v_u_1315_);
v_isSharedCheck_1390_ = !lean_is_exclusive(v_semiringInst_x3f_1317_);
if (v_isSharedCheck_1390_ == 0)
{
lean_object* v_unused_1391_; 
v_unused_1391_ = lean_ctor_get(v_semiringInst_x3f_1317_, 0);
lean_dec(v_unused_1391_);
v___x_1384_ = v_semiringInst_x3f_1317_;
v_isShared_1385_ = v_isSharedCheck_1390_;
goto v_resetjp_1383_;
}
else
{
lean_dec(v_semiringInst_x3f_1317_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1390_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; lean_object* v___x_1388_; 
v___x_1386_ = lean_box(0);
if (v_isShared_1385_ == 0)
{
lean_ctor_set_tag(v___x_1384_, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1386_);
v___x_1388_ = v___x_1384_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
else
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
lean_dec(v_preorderInst_x3f_1320_);
lean_dec(v_ltInst_x3f_1319_);
lean_dec(v_leInst_x3f_1318_);
lean_dec(v_semiringInst_x3f_1317_);
lean_dec_ref(v_type_1316_);
lean_dec(v_u_1315_);
v___x_1392_ = lean_box(0);
v___x_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
return v___x_1393_;
}
v___jp_1328_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = lean_box(0);
v___x_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
return v___x_1330_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1315_ = stack[0].m_obj;
lean_object* v_type_1316_ = stack[1].m_obj;
lean_object* v_semiringInst_x3f_1317_ = stack[2].m_obj;
lean_object* v_leInst_x3f_1318_ = stack[3].m_obj;
lean_object* v_ltInst_x3f_1319_ = stack[4].m_obj;
lean_object* v_preorderInst_x3f_1320_ = stack[5].m_obj;
lean_object* v_a_1321_ = stack[6].m_obj;
lean_object* v_a_1322_ = stack[7].m_obj;
lean_object* v_a_1323_ = stack[8].m_obj;
lean_object* v_a_1324_ = stack[9].m_obj;
lean_object* v_a_1325_ = stack[10].m_obj;
lean_object* v_a_1326_ = stack[11].m_obj;
lean_object* v_res_1394_;
v_res_1394_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_u_1315_, v_type_1316_, v_semiringInst_x3f_1317_, v_leInst_x3f_1318_, v_ltInst_x3f_1319_, v_preorderInst_x3f_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
stack->m_obj
 = v_res_1394_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___boxed(lean_object* v_u_1395_, lean_object* v_type_1396_, lean_object* v_semiringInst_x3f_1397_, lean_object* v_leInst_x3f_1398_, lean_object* v_ltInst_x3f_1399_, lean_object* v_preorderInst_x3f_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_u_1395_, v_type_1396_, v_semiringInst_x3f_1397_, v_leInst_x3f_1398_, v_ltInst_x3f_1399_, v_preorderInst_x3f_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_);
lean_dec(v_a_1406_);
lean_dec_ref(v_a_1405_);
lean_dec(v_a_1404_);
lean_dec_ref(v_a_1403_);
lean_dec(v_a_1402_);
lean_dec_ref(v_a_1401_);
return v_res_1408_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f(lean_object* v_u_1409_, lean_object* v_type_1410_, lean_object* v_semiringInst_x3f_1411_, lean_object* v_leInst_x3f_1412_, lean_object* v_ltInst_x3f_1413_, lean_object* v_preorderInst_x3f_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_u_1409_, v_type_1410_, v_semiringInst_x3f_1411_, v_leInst_x3f_1412_, v_ltInst_x3f_1413_, v_preorderInst_x3f_1414_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_);
return v___x_1426_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1409_ = stack[0].m_obj;
lean_object* v_type_1410_ = stack[1].m_obj;
lean_object* v_semiringInst_x3f_1411_ = stack[2].m_obj;
lean_object* v_leInst_x3f_1412_ = stack[3].m_obj;
lean_object* v_ltInst_x3f_1413_ = stack[4].m_obj;
lean_object* v_preorderInst_x3f_1414_ = stack[5].m_obj;
lean_object* v_a_1415_ = stack[6].m_obj;
lean_object* v_a_1416_ = stack[7].m_obj;
lean_object* v_a_1417_ = stack[8].m_obj;
lean_object* v_a_1418_ = stack[9].m_obj;
lean_object* v_a_1419_ = stack[10].m_obj;
lean_object* v_a_1420_ = stack[11].m_obj;
lean_object* v_a_1421_ = stack[12].m_obj;
lean_object* v_a_1422_ = stack[13].m_obj;
lean_object* v_a_1423_ = stack[14].m_obj;
lean_object* v_a_1424_ = stack[15].m_obj;
lean_object* v_res_1427_;
v_res_1427_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f(v_u_1409_, v_type_1410_, v_semiringInst_x3f_1411_, v_leInst_x3f_1412_, v_ltInst_x3f_1413_, v_preorderInst_x3f_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_);
stack->m_obj
 = v_res_1427_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___boxed(lean_object** _args){
lean_object* v_u_1428_ = _args[0];
lean_object* v_type_1429_ = _args[1];
lean_object* v_semiringInst_x3f_1430_ = _args[2];
lean_object* v_leInst_x3f_1431_ = _args[3];
lean_object* v_ltInst_x3f_1432_ = _args[4];
lean_object* v_preorderInst_x3f_1433_ = _args[5];
lean_object* v_a_1434_ = _args[6];
lean_object* v_a_1435_ = _args[7];
lean_object* v_a_1436_ = _args[8];
lean_object* v_a_1437_ = _args[9];
lean_object* v_a_1438_ = _args[10];
lean_object* v_a_1439_ = _args[11];
lean_object* v_a_1440_ = _args[12];
lean_object* v_a_1441_ = _args[13];
lean_object* v_a_1442_ = _args[14];
lean_object* v_a_1443_ = _args[15];
lean_object* v_a_1444_ = _args[16];
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f(v_u_1428_, v_type_1429_, v_semiringInst_x3f_1430_, v_leInst_x3f_1431_, v_ltInst_x3f_1432_, v_preorderInst_x3f_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_);
lean_dec(v_a_1443_);
lean_dec_ref(v_a_1442_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec(v_a_1439_);
lean_dec_ref(v_a_1438_);
lean_dec(v_a_1437_);
lean_dec_ref(v_a_1436_);
lean_dec(v_a_1435_);
lean_dec(v_a_1434_);
return v_res_1445_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(lean_object* v_u_1456_, lean_object* v_type_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_){
_start:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v_natModuleType_1468_; lean_object* v___x_1469_; 
v___x_1464_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1));
v___x_1465_ = lean_box(0);
v___x_1466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1466_, 0, v_u_1456_);
lean_ctor_set(v___x_1466_, 1, v___x_1465_);
lean_inc_ref(v___x_1466_);
v___x_1467_ = l_Lean_mkConst(v___x_1464_, v___x_1466_);
lean_inc_ref(v_type_1457_);
v_natModuleType_1468_ = l_Lean_Expr_app___override(v___x_1467_, v_type_1457_);
v___x_1469_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_natModuleType_1468_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1483_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1472_ = v___x_1469_;
v_isShared_1473_ = v_isSharedCheck_1483_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1469_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1483_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
if (lean_obj_tag(v_a_1470_) == 1)
{
lean_object* v_val_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
lean_del_object(v___x_1472_);
v_val_1474_ = lean_ctor_get(v_a_1470_, 0);
lean_inc(v_val_1474_);
lean_dec_ref_known(v_a_1470_, 1);
v___x_1475_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3));
v___x_1476_ = l_Lean_mkConst(v___x_1475_, v___x_1466_);
v___x_1477_ = l_Lean_mkAppB(v___x_1476_, v_type_1457_, v_val_1474_);
v___x_1478_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1477_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_);
return v___x_1478_;
}
else
{
lean_object* v___x_1479_; lean_object* v___x_1481_; 
lean_dec(v_a_1470_);
lean_dec_ref_known(v___x_1466_, 2);
lean_dec_ref(v_type_1457_);
v___x_1479_ = lean_box(0);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 0, v___x_1479_);
v___x_1481_ = v___x_1472_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1479_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1466_, 2);
lean_dec_ref(v_type_1457_);
return v___x_1469_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1456_ = stack[0].m_obj;
lean_object* v_type_1457_ = stack[1].m_obj;
lean_object* v_a_1458_ = stack[2].m_obj;
lean_object* v_a_1459_ = stack[3].m_obj;
lean_object* v_a_1460_ = stack[4].m_obj;
lean_object* v_a_1461_ = stack[5].m_obj;
lean_object* v_a_1462_ = stack[6].m_obj;
lean_object* v_res_1484_;
v_res_1484_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_u_1456_, v_type_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_);
stack->m_obj
 = v_res_1484_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___boxed(lean_object* v_u_1485_, lean_object* v_type_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_u_1485_, v_type_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_);
lean_dec(v_a_1491_);
lean_dec_ref(v_a_1490_);
lean_dec(v_a_1489_);
lean_dec_ref(v_a_1488_);
lean_dec(v_a_1487_);
return v_res_1493_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f(lean_object* v_u_1494_, lean_object* v_type_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_u_1494_, v_type_1495_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
return v___x_1507_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1494_ = stack[0].m_obj;
lean_object* v_type_1495_ = stack[1].m_obj;
lean_object* v_a_1496_ = stack[2].m_obj;
lean_object* v_a_1497_ = stack[3].m_obj;
lean_object* v_a_1498_ = stack[4].m_obj;
lean_object* v_a_1499_ = stack[5].m_obj;
lean_object* v_a_1500_ = stack[6].m_obj;
lean_object* v_a_1501_ = stack[7].m_obj;
lean_object* v_a_1502_ = stack[8].m_obj;
lean_object* v_a_1503_ = stack[9].m_obj;
lean_object* v_a_1504_ = stack[10].m_obj;
lean_object* v_a_1505_ = stack[11].m_obj;
lean_object* v_res_1508_;
v_res_1508_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f(v_u_1494_, v_type_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
stack->m_obj
 = v_res_1508_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___boxed(lean_object* v_u_1509_, lean_object* v_type_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f(v_u_1509_, v_type_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
lean_dec(v_a_1520_);
lean_dec_ref(v_a_1519_);
lean_dec(v_a_1518_);
lean_dec_ref(v_a_1517_);
lean_dec(v_a_1516_);
lean_dec_ref(v_a_1515_);
lean_dec(v_a_1514_);
lean_dec_ref(v_a_1513_);
lean_dec(v_a_1512_);
lean_dec(v_a_1511_);
return v_res_1522_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(lean_object* v_declName_1523_, lean_object* v_u_1524_, lean_object* v_type_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1532_ = lean_box(0);
v___x_1533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1533_, 0, v_u_1524_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = l_Lean_mkConst(v_declName_1523_, v___x_1533_);
v___x_1535_ = l_Lean_Expr_app___override(v___x_1534_, v_type_1525_);
v___x_1536_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1535_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_);
return v___x_1536_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1523_ = stack[0].m_obj;
lean_object* v_u_1524_ = stack[1].m_obj;
lean_object* v_type_1525_ = stack[2].m_obj;
lean_object* v_a_1526_ = stack[3].m_obj;
lean_object* v_a_1527_ = stack[4].m_obj;
lean_object* v_a_1528_ = stack[5].m_obj;
lean_object* v_a_1529_ = stack[6].m_obj;
lean_object* v_a_1530_ = stack[7].m_obj;
lean_object* v_res_1537_;
v_res_1537_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v_declName_1523_, v_u_1524_, v_type_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_);
stack->m_obj
 = v_res_1537_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg___boxed(lean_object* v_declName_1538_, lean_object* v_u_1539_, lean_object* v_type_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v_declName_1538_, v_u_1539_, v_type_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_);
lean_dec(v_a_1545_);
lean_dec_ref(v_a_1544_);
lean_dec(v_a_1543_);
lean_dec_ref(v_a_1542_);
lean_dec(v_a_1541_);
return v_res_1547_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f(lean_object* v_declName_1548_, lean_object* v_u_1549_, lean_object* v_type_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v_declName_1548_, v_u_1549_, v_type_1550_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_);
return v___x_1562_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1548_ = stack[0].m_obj;
lean_object* v_u_1549_ = stack[1].m_obj;
lean_object* v_type_1550_ = stack[2].m_obj;
lean_object* v_a_1551_ = stack[3].m_obj;
lean_object* v_a_1552_ = stack[4].m_obj;
lean_object* v_a_1553_ = stack[5].m_obj;
lean_object* v_a_1554_ = stack[6].m_obj;
lean_object* v_a_1555_ = stack[7].m_obj;
lean_object* v_a_1556_ = stack[8].m_obj;
lean_object* v_a_1557_ = stack[9].m_obj;
lean_object* v_a_1558_ = stack[10].m_obj;
lean_object* v_a_1559_ = stack[11].m_obj;
lean_object* v_a_1560_ = stack[12].m_obj;
lean_object* v_res_1563_;
v_res_1563_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f(v_declName_1548_, v_u_1549_, v_type_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_);
stack->m_obj
 = v_res_1563_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___boxed(lean_object* v_declName_1564_, lean_object* v_u_1565_, lean_object* v_type_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f(v_declName_1564_, v_u_1565_, v_type_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
lean_dec(v_a_1576_);
lean_dec_ref(v_a_1575_);
lean_dec(v_a_1574_);
lean_dec_ref(v_a_1573_);
lean_dec(v_a_1572_);
lean_dec_ref(v_a_1571_);
lean_dec(v_a_1570_);
lean_dec_ref(v_a_1569_);
lean_dec(v_a_1568_);
lean_dec(v_a_1567_);
return v_res_1578_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(lean_object* v_declName_1579_, lean_object* v_u_1580_, lean_object* v_type_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1589_ = lean_box(0);
v___x_1590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1590_, 0, v_u_1580_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = l_Lean_mkConst(v_declName_1579_, v___x_1590_);
v___x_1592_ = l_Lean_Expr_app___override(v___x_1591_, v_type_1581_);
v___x_1593_ = l_Lean_Meta_Sym_synthInstance(v___x_1592_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
return v___x_1593_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1579_ = stack[0].m_obj;
lean_object* v_u_1580_ = stack[1].m_obj;
lean_object* v_type_1581_ = stack[2].m_obj;
lean_object* v_a_1582_ = stack[3].m_obj;
lean_object* v_a_1583_ = stack[4].m_obj;
lean_object* v_a_1584_ = stack[5].m_obj;
lean_object* v_a_1585_ = stack[6].m_obj;
lean_object* v_a_1586_ = stack[7].m_obj;
lean_object* v_a_1587_ = stack[8].m_obj;
lean_object* v_res_1594_;
v_res_1594_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v_declName_1579_, v_u_1580_, v_type_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
stack->m_obj
 = v_res_1594_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg___boxed(lean_object* v_declName_1595_, lean_object* v_u_1596_, lean_object* v_type_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v_declName_1595_, v_u_1596_, v_type_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_);
lean_dec(v_a_1603_);
lean_dec_ref(v_a_1602_);
lean_dec(v_a_1601_);
lean_dec_ref(v_a_1600_);
lean_dec(v_a_1599_);
lean_dec_ref(v_a_1598_);
return v_res_1605_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(lean_object* v_declName_1606_, lean_object* v_u_1607_, lean_object* v_type_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v_declName_1606_, v_u_1607_, v_type_1608_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_);
return v___x_1620_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1606_ = stack[0].m_obj;
lean_object* v_u_1607_ = stack[1].m_obj;
lean_object* v_type_1608_ = stack[2].m_obj;
lean_object* v_a_1609_ = stack[3].m_obj;
lean_object* v_a_1610_ = stack[4].m_obj;
lean_object* v_a_1611_ = stack[5].m_obj;
lean_object* v_a_1612_ = stack[6].m_obj;
lean_object* v_a_1613_ = stack[7].m_obj;
lean_object* v_a_1614_ = stack[8].m_obj;
lean_object* v_a_1615_ = stack[9].m_obj;
lean_object* v_a_1616_ = stack[10].m_obj;
lean_object* v_a_1617_ = stack[11].m_obj;
lean_object* v_a_1618_ = stack[12].m_obj;
lean_object* v_res_1621_;
v_res_1621_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(v_declName_1606_, v_u_1607_, v_type_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_);
stack->m_obj
 = v_res_1621_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___boxed(lean_object* v_declName_1622_, lean_object* v_u_1623_, lean_object* v_type_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(v_declName_1622_, v_u_1623_, v_type_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_);
lean_dec(v_a_1634_);
lean_dec_ref(v_a_1633_);
lean_dec(v_a_1632_);
lean_dec_ref(v_a_1631_);
lean_dec(v_a_1630_);
lean_dec_ref(v_a_1629_);
lean_dec(v_a_1628_);
lean_dec_ref(v_a_1627_);
lean_dec(v_a_1626_);
lean_dec(v_a_1625_);
return v_res_1636_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(lean_object* v_declName_1637_, lean_object* v_u_1638_, lean_object* v_type_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1647_ = lean_box(0);
lean_inc_n(v_u_1638_, 2);
v___x_1648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1648_, 0, v_u_1638_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
v___x_1649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1649_, 0, v_u_1638_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1650_, 0, v_u_1638_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
v___x_1651_ = l_Lean_mkConst(v_declName_1637_, v___x_1650_);
lean_inc_ref_n(v_type_1639_, 2);
v___x_1652_ = l_Lean_mkApp3(v___x_1651_, v_type_1639_, v_type_1639_, v_type_1639_);
v___x_1653_ = l_Lean_Meta_Sym_synthInstance(v___x_1652_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_);
return v___x_1653_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1637_ = stack[0].m_obj;
lean_object* v_u_1638_ = stack[1].m_obj;
lean_object* v_type_1639_ = stack[2].m_obj;
lean_object* v_a_1640_ = stack[3].m_obj;
lean_object* v_a_1641_ = stack[4].m_obj;
lean_object* v_a_1642_ = stack[5].m_obj;
lean_object* v_a_1643_ = stack[6].m_obj;
lean_object* v_a_1644_ = stack[7].m_obj;
lean_object* v_a_1645_ = stack[8].m_obj;
lean_object* v_res_1654_;
v_res_1654_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v_declName_1637_, v_u_1638_, v_type_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_);
stack->m_obj
 = v_res_1654_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg___boxed(lean_object* v_declName_1655_, lean_object* v_u_1656_, lean_object* v_type_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v_declName_1655_, v_u_1656_, v_type_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_);
lean_dec(v_a_1663_);
lean_dec_ref(v_a_1662_);
lean_dec(v_a_1661_);
lean_dec_ref(v_a_1660_);
lean_dec(v_a_1659_);
lean_dec_ref(v_a_1658_);
return v_res_1665_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(lean_object* v_declName_1666_, lean_object* v_u_1667_, lean_object* v_type_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v_declName_1666_, v_u_1667_, v_type_1668_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_);
return v___x_1680_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1666_ = stack[0].m_obj;
lean_object* v_u_1667_ = stack[1].m_obj;
lean_object* v_type_1668_ = stack[2].m_obj;
lean_object* v_a_1669_ = stack[3].m_obj;
lean_object* v_a_1670_ = stack[4].m_obj;
lean_object* v_a_1671_ = stack[5].m_obj;
lean_object* v_a_1672_ = stack[6].m_obj;
lean_object* v_a_1673_ = stack[7].m_obj;
lean_object* v_a_1674_ = stack[8].m_obj;
lean_object* v_a_1675_ = stack[9].m_obj;
lean_object* v_a_1676_ = stack[10].m_obj;
lean_object* v_a_1677_ = stack[11].m_obj;
lean_object* v_a_1678_ = stack[12].m_obj;
lean_object* v_res_1681_;
v_res_1681_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(v_declName_1666_, v_u_1667_, v_type_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_);
stack->m_obj
 = v_res_1681_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___boxed(lean_object* v_declName_1682_, lean_object* v_u_1683_, lean_object* v_type_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(v_declName_1682_, v_u_1683_, v_type_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_);
lean_dec(v_a_1694_);
lean_dec_ref(v_a_1693_);
lean_dec(v_a_1692_);
lean_dec_ref(v_a_1691_);
lean_dec(v_a_1690_);
lean_dec_ref(v_a_1689_);
lean_dec(v_a_1688_);
lean_dec_ref(v_a_1687_);
lean_dec(v_a_1686_);
lean_dec(v_a_1685_);
return v_res_1696_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2(void){
_start:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1700_ = lean_unsigned_to_nat(0u);
v___x_1701_ = l_Lean_Level_ofNat(v___x_1700_);
return v___x_1701_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(lean_object* v_u_1702_, lean_object* v_type_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_){
_start:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1711_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_1712_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_1713_ = lean_box(0);
lean_inc(v_u_1702_);
v___x_1714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1714_, 0, v_u_1702_);
lean_ctor_set(v___x_1714_, 1, v___x_1713_);
v___x_1715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1715_, 0, v_u_1702_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
v___x_1716_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1712_);
lean_ctor_set(v___x_1716_, 1, v___x_1715_);
v___x_1717_ = l_Lean_mkConst(v___x_1711_, v___x_1716_);
v___x_1718_ = l_Lean_Int_mkType;
lean_inc_ref(v_type_1703_);
v___x_1719_ = l_Lean_mkApp3(v___x_1717_, v___x_1718_, v_type_1703_, v_type_1703_);
v___x_1720_ = l_Lean_Meta_Sym_synthInstance(v___x_1719_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_);
return v___x_1720_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1702_ = stack[0].m_obj;
lean_object* v_type_1703_ = stack[1].m_obj;
lean_object* v_a_1704_ = stack[2].m_obj;
lean_object* v_a_1705_ = stack[3].m_obj;
lean_object* v_a_1706_ = stack[4].m_obj;
lean_object* v_a_1707_ = stack[5].m_obj;
lean_object* v_a_1708_ = stack[6].m_obj;
lean_object* v_a_1709_ = stack[7].m_obj;
lean_object* v_res_1721_;
v_res_1721_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(v_u_1702_, v_type_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_);
stack->m_obj
 = v_res_1721_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___boxed(lean_object* v_u_1722_, lean_object* v_type_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(v_u_1722_, v_type_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_);
lean_dec(v_a_1729_);
lean_dec_ref(v_a_1728_);
lean_dec(v_a_1727_);
lean_dec_ref(v_a_1726_);
lean_dec(v_a_1725_);
lean_dec_ref(v_a_1724_);
return v_res_1731_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(lean_object* v_u_1732_, lean_object* v_type_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(v_u_1732_, v_type_1733_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
return v___x_1745_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1732_ = stack[0].m_obj;
lean_object* v_type_1733_ = stack[1].m_obj;
lean_object* v_a_1734_ = stack[2].m_obj;
lean_object* v_a_1735_ = stack[3].m_obj;
lean_object* v_a_1736_ = stack[4].m_obj;
lean_object* v_a_1737_ = stack[5].m_obj;
lean_object* v_a_1738_ = stack[6].m_obj;
lean_object* v_a_1739_ = stack[7].m_obj;
lean_object* v_a_1740_ = stack[8].m_obj;
lean_object* v_a_1741_ = stack[9].m_obj;
lean_object* v_a_1742_ = stack[10].m_obj;
lean_object* v_a_1743_ = stack[11].m_obj;
lean_object* v_res_1746_;
v_res_1746_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(v_u_1732_, v_type_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
stack->m_obj
 = v_res_1746_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___boxed(lean_object* v_u_1747_, lean_object* v_type_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(v_u_1747_, v_type_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_);
lean_dec(v_a_1758_);
lean_dec_ref(v_a_1757_);
lean_dec(v_a_1756_);
lean_dec_ref(v_a_1755_);
lean_dec(v_a_1754_);
lean_dec_ref(v_a_1753_);
lean_dec(v_a_1752_);
lean_dec_ref(v_a_1751_);
lean_dec(v_a_1750_);
lean_dec(v_a_1749_);
return v_res_1760_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(lean_object* v_u_1761_, lean_object* v_type_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1770_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_1771_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_1772_ = lean_box(0);
lean_inc(v_u_1761_);
v___x_1773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1773_, 0, v_u_1761_);
lean_ctor_set(v___x_1773_, 1, v___x_1772_);
v___x_1774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1774_, 0, v_u_1761_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
v___x_1775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1771_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = l_Lean_mkConst(v___x_1770_, v___x_1775_);
v___x_1777_ = l_Lean_Nat_mkType;
lean_inc_ref(v_type_1762_);
v___x_1778_ = l_Lean_mkApp3(v___x_1776_, v___x_1777_, v_type_1762_, v_type_1762_);
v___x_1779_ = l_Lean_Meta_Sym_synthInstance(v___x_1778_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_);
return v___x_1779_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1761_ = stack[0].m_obj;
lean_object* v_type_1762_ = stack[1].m_obj;
lean_object* v_a_1763_ = stack[2].m_obj;
lean_object* v_a_1764_ = stack[3].m_obj;
lean_object* v_a_1765_ = stack[4].m_obj;
lean_object* v_a_1766_ = stack[5].m_obj;
lean_object* v_a_1767_ = stack[6].m_obj;
lean_object* v_a_1768_ = stack[7].m_obj;
lean_object* v_res_1780_;
v_res_1780_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_u_1761_, v_type_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_);
stack->m_obj
 = v_res_1780_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg___boxed(lean_object* v_u_1781_, lean_object* v_type_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_u_1781_, v_type_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
lean_dec(v_a_1788_);
lean_dec_ref(v_a_1787_);
lean_dec(v_a_1786_);
lean_dec_ref(v_a_1785_);
lean_dec(v_a_1784_);
lean_dec_ref(v_a_1783_);
return v_res_1790_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(lean_object* v_u_1791_, lean_object* v_type_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_u_1791_, v_type_1792_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_);
return v___x_1804_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1791_ = stack[0].m_obj;
lean_object* v_type_1792_ = stack[1].m_obj;
lean_object* v_a_1793_ = stack[2].m_obj;
lean_object* v_a_1794_ = stack[3].m_obj;
lean_object* v_a_1795_ = stack[4].m_obj;
lean_object* v_a_1796_ = stack[5].m_obj;
lean_object* v_a_1797_ = stack[6].m_obj;
lean_object* v_a_1798_ = stack[7].m_obj;
lean_object* v_a_1799_ = stack[8].m_obj;
lean_object* v_a_1800_ = stack[9].m_obj;
lean_object* v_a_1801_ = stack[10].m_obj;
lean_object* v_a_1802_ = stack[11].m_obj;
lean_object* v_res_1805_;
v_res_1805_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(v_u_1791_, v_type_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_);
stack->m_obj
 = v_res_1805_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___boxed(lean_object* v_u_1806_, lean_object* v_type_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(v_u_1806_, v_type_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_);
lean_dec(v_a_1817_);
lean_dec_ref(v_a_1816_);
lean_dec(v_a_1815_);
lean_dec_ref(v_a_1814_);
lean_dec(v_a_1813_);
lean_dec_ref(v_a_1812_);
lean_dec(v_a_1811_);
lean_dec_ref(v_a_1810_);
lean_dec(v_a_1809_);
lean_dec(v_a_1808_);
return v_res_1819_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(lean_object* v_leInst_x3f_1820_, lean_object* v_parentInst_x3f_1821_, lean_object* v_childInst_x3f_1822_, lean_object* v_toFieldName_1823_, lean_object* v_u_1824_, lean_object* v_type_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_1820_) == 1)
{
if (lean_obj_tag(v_parentInst_x3f_1821_) == 1)
{
if (lean_obj_tag(v_childInst_x3f_1822_) == 1)
{
lean_object* v_val_1836_; lean_object* v_val_1837_; lean_object* v_val_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v_toField_1842_; lean_object* v___x_1843_; 
v_val_1836_ = lean_ctor_get(v_leInst_x3f_1820_, 0);
lean_inc(v_val_1836_);
lean_dec_ref_known(v_leInst_x3f_1820_, 1);
v_val_1837_ = lean_ctor_get(v_parentInst_x3f_1821_, 0);
lean_inc_n(v_val_1837_, 2);
lean_dec_ref_known(v_parentInst_x3f_1821_, 1);
v_val_1838_ = lean_ctor_get(v_childInst_x3f_1822_, 0);
v___x_1839_ = lean_box(0);
v___x_1840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1840_, 0, v_u_1824_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
v___x_1841_ = l_Lean_mkConst(v_toFieldName_1823_, v___x_1840_);
lean_inc(v_val_1838_);
v_toField_1842_ = l_Lean_mkApp3(v___x_1841_, v_type_1825_, v_val_1836_, v_val_1838_);
lean_inc_ref(v_toField_1842_);
v___x_1843_ = l_Lean_Meta_isDefEqD(v_val_1837_, v_toField_1842_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1874_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1846_ = v___x_1843_;
v_isShared_1847_ = v_isSharedCheck_1874_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1843_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1874_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
uint8_t v___x_1848_; 
v___x_1848_ = lean_unbox(v_a_1844_);
lean_dec(v_a_1844_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; lean_object* v_a_1850_; lean_object* v___x_1851_; 
lean_del_object(v___x_1846_);
lean_dec_ref_known(v_childInst_x3f_1822_, 1);
v___x_1849_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_val_1837_, v_toField_1842_);
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_a_1850_);
lean_dec_ref(v___x_1849_);
v___x_1851_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1826_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; uint8_t v_verbose_1853_; 
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
lean_inc(v_a_1852_);
lean_dec_ref_known(v___x_1851_, 1);
v_verbose_1853_ = lean_ctor_get_uint8(v_a_1852_, 0);
lean_dec(v_a_1852_);
if (v_verbose_1853_ == 0)
{
lean_dec(v_a_1850_);
goto v___jp_1833_;
}
else
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Lean_Meta_Sym_reportIssue(v_a_1850_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_dec_ref_known(v___x_1854_, 1);
goto v___jp_1833_;
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1854_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1854_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_dec(v_a_1850_);
v_a_1863_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1851_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1851_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
else
{
lean_object* v___x_1872_; 
lean_dec_ref(v_toField_1842_);
lean_dec(v_val_1837_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v_childInst_x3f_1822_);
v___x_1872_ = v___x_1846_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_childInst_x3f_1822_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
lean_dec_ref(v_toField_1842_);
lean_dec(v_val_1837_);
lean_dec_ref_known(v_childInst_x3f_1822_, 1);
v_a_1875_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1843_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1843_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
else
{
lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1890_; 
lean_dec_ref_known(v_leInst_x3f_1820_, 1);
lean_dec_ref(v_type_1825_);
lean_dec(v_u_1824_);
lean_dec(v_toFieldName_1823_);
lean_dec(v_childInst_x3f_1822_);
v_isSharedCheck_1890_ = !lean_is_exclusive(v_parentInst_x3f_1821_);
if (v_isSharedCheck_1890_ == 0)
{
lean_object* v_unused_1891_; 
v_unused_1891_ = lean_ctor_get(v_parentInst_x3f_1821_, 0);
lean_dec(v_unused_1891_);
v___x_1884_ = v_parentInst_x3f_1821_;
v_isShared_1885_ = v_isSharedCheck_1890_;
goto v_resetjp_1883_;
}
else
{
lean_dec(v_parentInst_x3f_1821_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1890_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; lean_object* v___x_1888_; 
v___x_1886_ = lean_box(0);
if (v_isShared_1885_ == 0)
{
lean_ctor_set_tag(v___x_1884_, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1886_);
v___x_1888_ = v___x_1884_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
else
{
lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1899_; 
lean_dec_ref(v_type_1825_);
lean_dec(v_u_1824_);
lean_dec(v_toFieldName_1823_);
lean_dec(v_childInst_x3f_1822_);
lean_dec(v_parentInst_x3f_1821_);
v_isSharedCheck_1899_ = !lean_is_exclusive(v_leInst_x3f_1820_);
if (v_isSharedCheck_1899_ == 0)
{
lean_object* v_unused_1900_; 
v_unused_1900_ = lean_ctor_get(v_leInst_x3f_1820_, 0);
lean_dec(v_unused_1900_);
v___x_1893_ = v_leInst_x3f_1820_;
v_isShared_1894_ = v_isSharedCheck_1899_;
goto v_resetjp_1892_;
}
else
{
lean_dec(v_leInst_x3f_1820_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1899_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1895_; lean_object* v___x_1897_; 
v___x_1895_ = lean_box(0);
if (v_isShared_1894_ == 0)
{
lean_ctor_set_tag(v___x_1893_, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1895_);
v___x_1897_ = v___x_1893_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v___x_1895_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
else
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
lean_dec_ref(v_type_1825_);
lean_dec(v_u_1824_);
lean_dec(v_toFieldName_1823_);
lean_dec(v_childInst_x3f_1822_);
lean_dec(v_parentInst_x3f_1821_);
lean_dec(v_leInst_x3f_1820_);
v___x_1901_ = lean_box(0);
v___x_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
return v___x_1902_;
}
v___jp_1833_:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = lean_box(0);
v___x_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1834_);
return v___x_1835_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_leInst_x3f_1820_ = stack[0].m_obj;
lean_object* v_parentInst_x3f_1821_ = stack[1].m_obj;
lean_object* v_childInst_x3f_1822_ = stack[2].m_obj;
lean_object* v_toFieldName_1823_ = stack[3].m_obj;
lean_object* v_u_1824_ = stack[4].m_obj;
lean_object* v_type_1825_ = stack[5].m_obj;
lean_object* v_a_1826_ = stack[6].m_obj;
lean_object* v_a_1827_ = stack[7].m_obj;
lean_object* v_a_1828_ = stack[8].m_obj;
lean_object* v_a_1829_ = stack[9].m_obj;
lean_object* v_a_1830_ = stack[10].m_obj;
lean_object* v_a_1831_ = stack[11].m_obj;
lean_object* v_res_1903_;
v_res_1903_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_leInst_x3f_1820_, v_parentInst_x3f_1821_, v_childInst_x3f_1822_, v_toFieldName_1823_, v_u_1824_, v_type_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_);
stack->m_obj
 = v_res_1903_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg___boxed(lean_object* v_leInst_x3f_1904_, lean_object* v_parentInst_x3f_1905_, lean_object* v_childInst_x3f_1906_, lean_object* v_toFieldName_1907_, lean_object* v_u_1908_, lean_object* v_type_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_leInst_x3f_1904_, v_parentInst_x3f_1905_, v_childInst_x3f_1906_, v_toFieldName_1907_, v_u_1908_, v_type_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
lean_dec(v_a_1915_);
lean_dec_ref(v_a_1914_);
lean_dec(v_a_1913_);
lean_dec_ref(v_a_1912_);
lean_dec(v_a_1911_);
lean_dec_ref(v_a_1910_);
return v_res_1917_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f(lean_object* v_leInst_x3f_1918_, lean_object* v_parentInst_x3f_1919_, lean_object* v_childInst_x3f_1920_, lean_object* v_toFieldName_1921_, lean_object* v_u_1922_, lean_object* v_type_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
lean_object* v___x_1935_; 
v___x_1935_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_leInst_x3f_1918_, v_parentInst_x3f_1919_, v_childInst_x3f_1920_, v_toFieldName_1921_, v_u_1922_, v_type_1923_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
return v___x_1935_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_leInst_x3f_1918_ = stack[0].m_obj;
lean_object* v_parentInst_x3f_1919_ = stack[1].m_obj;
lean_object* v_childInst_x3f_1920_ = stack[2].m_obj;
lean_object* v_toFieldName_1921_ = stack[3].m_obj;
lean_object* v_u_1922_ = stack[4].m_obj;
lean_object* v_type_1923_ = stack[5].m_obj;
lean_object* v_a_1924_ = stack[6].m_obj;
lean_object* v_a_1925_ = stack[7].m_obj;
lean_object* v_a_1926_ = stack[8].m_obj;
lean_object* v_a_1927_ = stack[9].m_obj;
lean_object* v_a_1928_ = stack[10].m_obj;
lean_object* v_a_1929_ = stack[11].m_obj;
lean_object* v_a_1930_ = stack[12].m_obj;
lean_object* v_a_1931_ = stack[13].m_obj;
lean_object* v_a_1932_ = stack[14].m_obj;
lean_object* v_a_1933_ = stack[15].m_obj;
lean_object* v_res_1936_;
v_res_1936_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f(v_leInst_x3f_1918_, v_parentInst_x3f_1919_, v_childInst_x3f_1920_, v_toFieldName_1921_, v_u_1922_, v_type_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
stack->m_obj
 = v_res_1936_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___boxed(lean_object** _args){
lean_object* v_leInst_x3f_1937_ = _args[0];
lean_object* v_parentInst_x3f_1938_ = _args[1];
lean_object* v_childInst_x3f_1939_ = _args[2];
lean_object* v_toFieldName_1940_ = _args[3];
lean_object* v_u_1941_ = _args[4];
lean_object* v_type_1942_ = _args[5];
lean_object* v_a_1943_ = _args[6];
lean_object* v_a_1944_ = _args[7];
lean_object* v_a_1945_ = _args[8];
lean_object* v_a_1946_ = _args[9];
lean_object* v_a_1947_ = _args[10];
lean_object* v_a_1948_ = _args[11];
lean_object* v_a_1949_ = _args[12];
lean_object* v_a_1950_ = _args[13];
lean_object* v_a_1951_ = _args[14];
lean_object* v_a_1952_ = _args[15];
lean_object* v_a_1953_ = _args[16];
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f(v_leInst_x3f_1937_, v_parentInst_x3f_1938_, v_childInst_x3f_1939_, v_toFieldName_1940_, v_u_1941_, v_type_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
lean_dec(v_a_1948_);
lean_dec_ref(v_a_1947_);
lean_dec(v_a_1946_);
lean_dec_ref(v_a_1945_);
lean_dec(v_a_1944_);
lean_dec(v_a_1943_);
return v_res_1954_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(lean_object* v_parentInst_1955_, lean_object* v_inst_1956_, lean_object* v_toFieldName_1957_, lean_object* v_u_1958_, lean_object* v_type_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v_toField_1968_; lean_object* v___x_1969_; 
v___x_1965_ = lean_box(0);
v___x_1966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1966_, 0, v_u_1958_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
v___x_1967_ = l_Lean_mkConst(v_toFieldName_1957_, v___x_1966_);
v_toField_1968_ = l_Lean_mkAppB(v___x_1967_, v_type_1959_, v_inst_1956_);
v___x_1969_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_parentInst_1955_, v_toField_1968_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_);
return v___x_1969_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_parentInst_1955_ = stack[0].m_obj;
lean_object* v_inst_1956_ = stack[1].m_obj;
lean_object* v_toFieldName_1957_ = stack[2].m_obj;
lean_object* v_u_1958_ = stack[3].m_obj;
lean_object* v_type_1959_ = stack[4].m_obj;
lean_object* v_a_1960_ = stack[5].m_obj;
lean_object* v_a_1961_ = stack[6].m_obj;
lean_object* v_a_1962_ = stack[7].m_obj;
lean_object* v_a_1963_ = stack[8].m_obj;
lean_object* v_res_1970_;
v_res_1970_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_parentInst_1955_, v_inst_1956_, v_toFieldName_1957_, v_u_1958_, v_type_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_);
stack->m_obj
 = v_res_1970_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg___boxed(lean_object* v_parentInst_1971_, lean_object* v_inst_1972_, lean_object* v_toFieldName_1973_, lean_object* v_u_1974_, lean_object* v_type_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_parentInst_1971_, v_inst_1972_, v_toFieldName_1973_, v_u_1974_, v_type_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_);
lean_dec(v_a_1979_);
lean_dec_ref(v_a_1978_);
lean_dec(v_a_1977_);
lean_dec_ref(v_a_1976_);
return v_res_1981_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq(lean_object* v_parentInst_1982_, lean_object* v_inst_1983_, lean_object* v_toFieldName_1984_, lean_object* v_u_1985_, lean_object* v_type_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_parentInst_1982_, v_inst_1983_, v_toFieldName_1984_, v_u_1985_, v_type_1986_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
return v___x_1998_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_parentInst_1982_ = stack[0].m_obj;
lean_object* v_inst_1983_ = stack[1].m_obj;
lean_object* v_toFieldName_1984_ = stack[2].m_obj;
lean_object* v_u_1985_ = stack[3].m_obj;
lean_object* v_type_1986_ = stack[4].m_obj;
lean_object* v_a_1987_ = stack[5].m_obj;
lean_object* v_a_1988_ = stack[6].m_obj;
lean_object* v_a_1989_ = stack[7].m_obj;
lean_object* v_a_1990_ = stack[8].m_obj;
lean_object* v_a_1991_ = stack[9].m_obj;
lean_object* v_a_1992_ = stack[10].m_obj;
lean_object* v_a_1993_ = stack[11].m_obj;
lean_object* v_a_1994_ = stack[12].m_obj;
lean_object* v_a_1995_ = stack[13].m_obj;
lean_object* v_a_1996_ = stack[14].m_obj;
lean_object* v_res_1999_;
v_res_1999_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq(v_parentInst_1982_, v_inst_1983_, v_toFieldName_1984_, v_u_1985_, v_type_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
stack->m_obj
 = v_res_1999_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___boxed(lean_object* v_parentInst_2000_, lean_object* v_inst_2001_, lean_object* v_toFieldName_2002_, lean_object* v_u_2003_, lean_object* v_type_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq(v_parentInst_2000_, v_inst_2001_, v_toFieldName_2002_, v_u_2003_, v_type_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
lean_dec(v_a_2014_);
lean_dec_ref(v_a_2013_);
lean_dec(v_a_2012_);
lean_dec_ref(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec(v_a_2008_);
lean_dec_ref(v_a_2007_);
lean_dec(v_a_2006_);
lean_dec(v_a_2005_);
return v_res_2016_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(lean_object* v_parentInst_2017_, lean_object* v_inst_2018_, lean_object* v_toFieldName_2019_, lean_object* v_toHeteroName_2020_, lean_object* v_u_2021_, lean_object* v_type_2022_, lean_object* v_extraType_x3f_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_){
_start:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v_toField_2032_; 
v___x_2029_ = lean_box(0);
v___x_2030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2030_, 0, v_u_2021_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
lean_inc_ref(v___x_2030_);
v___x_2031_ = l_Lean_mkConst(v_toFieldName_2019_, v___x_2030_);
lean_inc_ref(v_type_2022_);
v_toField_2032_ = l_Lean_mkAppB(v___x_2031_, v_type_2022_, v_inst_2018_);
if (lean_obj_tag(v_extraType_x3f_2023_) == 0)
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2033_ = l_Lean_mkConst(v_toHeteroName_2020_, v___x_2030_);
v___x_2034_ = l_Lean_mkAppB(v___x_2033_, v_type_2022_, v_toField_2032_);
v___x_2035_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_parentInst_2017_, v___x_2034_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_);
return v___x_2035_;
}
else
{
lean_object* v_val_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v_val_2036_ = lean_ctor_get(v_extraType_x3f_2023_, 0);
lean_inc(v_val_2036_);
lean_dec_ref_known(v_extraType_x3f_2023_, 1);
v___x_2037_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_2038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
lean_ctor_set(v___x_2038_, 1, v___x_2030_);
v___x_2039_ = l_Lean_mkConst(v_toHeteroName_2020_, v___x_2038_);
v___x_2040_ = l_Lean_mkApp3(v___x_2039_, v_val_2036_, v_type_2022_, v_toField_2032_);
v___x_2041_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_parentInst_2017_, v___x_2040_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_);
return v___x_2041_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_parentInst_2017_ = stack[0].m_obj;
lean_object* v_inst_2018_ = stack[1].m_obj;
lean_object* v_toFieldName_2019_ = stack[2].m_obj;
lean_object* v_toHeteroName_2020_ = stack[3].m_obj;
lean_object* v_u_2021_ = stack[4].m_obj;
lean_object* v_type_2022_ = stack[5].m_obj;
lean_object* v_extraType_x3f_2023_ = stack[6].m_obj;
lean_object* v_a_2024_ = stack[7].m_obj;
lean_object* v_a_2025_ = stack[8].m_obj;
lean_object* v_a_2026_ = stack[9].m_obj;
lean_object* v_a_2027_ = stack[10].m_obj;
lean_object* v_res_2042_;
v_res_2042_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_parentInst_2017_, v_inst_2018_, v_toFieldName_2019_, v_toHeteroName_2020_, v_u_2021_, v_type_2022_, v_extraType_x3f_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_);
stack->m_obj
 = v_res_2042_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg___boxed(lean_object* v_parentInst_2043_, lean_object* v_inst_2044_, lean_object* v_toFieldName_2045_, lean_object* v_toHeteroName_2046_, lean_object* v_u_2047_, lean_object* v_type_2048_, lean_object* v_extraType_x3f_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_parentInst_2043_, v_inst_2044_, v_toFieldName_2045_, v_toHeteroName_2046_, v_u_2047_, v_type_2048_, v_extraType_x3f_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_);
lean_dec(v_a_2053_);
lean_dec_ref(v_a_2052_);
lean_dec(v_a_2051_);
lean_dec_ref(v_a_2050_);
return v_res_2055_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq(lean_object* v_parentInst_2056_, lean_object* v_inst_2057_, lean_object* v_toFieldName_2058_, lean_object* v_toHeteroName_2059_, lean_object* v_u_2060_, lean_object* v_type_2061_, lean_object* v_extraType_x3f_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_){
_start:
{
lean_object* v___x_2074_; 
v___x_2074_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_parentInst_2056_, v_inst_2057_, v_toFieldName_2058_, v_toHeteroName_2059_, v_u_2060_, v_type_2061_, v_extraType_x3f_2062_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
return v___x_2074_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_parentInst_2056_ = stack[0].m_obj;
lean_object* v_inst_2057_ = stack[1].m_obj;
lean_object* v_toFieldName_2058_ = stack[2].m_obj;
lean_object* v_toHeteroName_2059_ = stack[3].m_obj;
lean_object* v_u_2060_ = stack[4].m_obj;
lean_object* v_type_2061_ = stack[5].m_obj;
lean_object* v_extraType_x3f_2062_ = stack[6].m_obj;
lean_object* v_a_2063_ = stack[7].m_obj;
lean_object* v_a_2064_ = stack[8].m_obj;
lean_object* v_a_2065_ = stack[9].m_obj;
lean_object* v_a_2066_ = stack[10].m_obj;
lean_object* v_a_2067_ = stack[11].m_obj;
lean_object* v_a_2068_ = stack[12].m_obj;
lean_object* v_a_2069_ = stack[13].m_obj;
lean_object* v_a_2070_ = stack[14].m_obj;
lean_object* v_a_2071_ = stack[15].m_obj;
lean_object* v_a_2072_ = stack[16].m_obj;
lean_object* v_res_2075_;
v_res_2075_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq(v_parentInst_2056_, v_inst_2057_, v_toFieldName_2058_, v_toHeteroName_2059_, v_u_2060_, v_type_2061_, v_extraType_x3f_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
stack->m_obj
 = v_res_2075_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___boxed(lean_object** _args){
lean_object* v_parentInst_2076_ = _args[0];
lean_object* v_inst_2077_ = _args[1];
lean_object* v_toFieldName_2078_ = _args[2];
lean_object* v_toHeteroName_2079_ = _args[3];
lean_object* v_u_2080_ = _args[4];
lean_object* v_type_2081_ = _args[5];
lean_object* v_extraType_x3f_2082_ = _args[6];
lean_object* v_a_2083_ = _args[7];
lean_object* v_a_2084_ = _args[8];
lean_object* v_a_2085_ = _args[9];
lean_object* v_a_2086_ = _args[10];
lean_object* v_a_2087_ = _args[11];
lean_object* v_a_2088_ = _args[12];
lean_object* v_a_2089_ = _args[13];
lean_object* v_a_2090_ = _args[14];
lean_object* v_a_2091_ = _args[15];
lean_object* v_a_2092_ = _args[16];
lean_object* v_a_2093_ = _args[17];
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq(v_parentInst_2076_, v_inst_2077_, v_toFieldName_2078_, v_toHeteroName_2079_, v_u_2080_, v_type_2081_, v_extraType_x3f_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_);
lean_dec(v_a_2092_);
lean_dec_ref(v_a_2091_);
lean_dec(v_a_2090_);
lean_dec_ref(v_a_2089_);
lean_dec(v_a_2088_);
lean_dec_ref(v_a_2087_);
lean_dec(v_a_2086_);
lean_dec_ref(v_a_2085_);
lean_dec(v_a_2084_);
lean_dec(v_a_2083_);
return v_res_2094_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(lean_object* v_u_2099_, lean_object* v_type_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v_smulType_2116_; lean_object* v___x_2117_; 
v___x_2108_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_2109_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_2110_ = lean_box(0);
lean_inc(v_u_2099_);
v___x_2111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2111_, 0, v_u_2099_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
v___x_2112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2112_, 0, v_u_2099_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
v___x_2113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2109_);
lean_ctor_set(v___x_2113_, 1, v___x_2112_);
lean_inc_ref(v___x_2113_);
v___x_2114_ = l_Lean_mkConst(v___x_2108_, v___x_2113_);
v___x_2115_ = l_Lean_Int_mkType;
lean_inc_ref_n(v_type_2100_, 2);
v_smulType_2116_ = l_Lean_mkApp3(v___x_2114_, v___x_2115_, v_type_2100_, v_type_2100_);
v___x_2117_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_smulType_2116_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2154_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2120_ = v___x_2117_;
v_isShared_2121_ = v_isSharedCheck_2154_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2117_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2154_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
if (lean_obj_tag(v_a_2118_) == 1)
{
lean_object* v_val_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2149_; 
lean_del_object(v___x_2120_);
v_val_2122_ = lean_ctor_get(v_a_2118_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v_a_2118_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2124_ = v_a_2118_;
v_isShared_2125_ = v_isSharedCheck_2149_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_val_2122_);
lean_dec(v_a_2118_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2149_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2126_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_2127_ = l_Lean_mkConst(v___x_2126_, v___x_2113_);
lean_inc_ref(v_type_2100_);
v___x_2128_ = l_Lean_mkApp4(v___x_2127_, v___x_2115_, v_type_2100_, v_type_2100_, v_val_2122_);
v___x_2129_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2128_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2140_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2132_ = v___x_2129_;
v_isShared_2133_ = v_isSharedCheck_2140_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2129_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2140_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v_a_2130_);
v___x_2135_ = v___x_2124_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
lean_object* v___x_2137_; 
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 0, v___x_2135_);
v___x_2137_ = v___x_2132_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2135_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
else
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_del_object(v___x_2124_);
v_a_2141_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v___x_2129_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2129_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
}
else
{
lean_object* v___x_2150_; lean_object* v___x_2152_; 
lean_dec(v_a_2118_);
lean_dec_ref_known(v___x_2113_, 2);
lean_dec_ref(v_type_2100_);
v___x_2150_ = lean_box(0);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 0, v___x_2150_);
v___x_2152_ = v___x_2120_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2113_, 2);
lean_dec_ref(v_type_2100_);
return v___x_2117_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_2099_ = stack[0].m_obj;
lean_object* v_type_2100_ = stack[1].m_obj;
lean_object* v_a_2101_ = stack[2].m_obj;
lean_object* v_a_2102_ = stack[3].m_obj;
lean_object* v_a_2103_ = stack[4].m_obj;
lean_object* v_a_2104_ = stack[5].m_obj;
lean_object* v_a_2105_ = stack[6].m_obj;
lean_object* v_a_2106_ = stack[7].m_obj;
lean_object* v_res_2155_;
v_res_2155_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(v_u_2099_, v_type_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
stack->m_obj
 = v_res_2155_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___boxed(lean_object* v_u_2156_, lean_object* v_type_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(v_u_2156_, v_type_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_);
lean_dec(v_a_2163_);
lean_dec_ref(v_a_2162_);
lean_dec(v_a_2161_);
lean_dec_ref(v_a_2160_);
lean_dec(v_a_2159_);
lean_dec_ref(v_a_2158_);
return v_res_2165_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f(lean_object* v_u_2166_, lean_object* v_type_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_){
_start:
{
lean_object* v___x_2179_; 
v___x_2179_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(v_u_2166_, v_type_2167_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
return v___x_2179_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_2166_ = stack[0].m_obj;
lean_object* v_type_2167_ = stack[1].m_obj;
lean_object* v_a_2168_ = stack[2].m_obj;
lean_object* v_a_2169_ = stack[3].m_obj;
lean_object* v_a_2170_ = stack[4].m_obj;
lean_object* v_a_2171_ = stack[5].m_obj;
lean_object* v_a_2172_ = stack[6].m_obj;
lean_object* v_a_2173_ = stack[7].m_obj;
lean_object* v_a_2174_ = stack[8].m_obj;
lean_object* v_a_2175_ = stack[9].m_obj;
lean_object* v_a_2176_ = stack[10].m_obj;
lean_object* v_a_2177_ = stack[11].m_obj;
lean_object* v_res_2180_;
v_res_2180_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f(v_u_2166_, v_type_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
stack->m_obj
 = v_res_2180_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___boxed(lean_object* v_u_2181_, lean_object* v_type_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f(v_u_2181_, v_type_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_);
lean_dec(v_a_2192_);
lean_dec_ref(v_a_2191_);
lean_dec(v_a_2190_);
lean_dec_ref(v_a_2189_);
lean_dec(v_a_2188_);
lean_dec_ref(v_a_2187_);
lean_dec(v_a_2186_);
lean_dec_ref(v_a_2185_);
lean_dec(v_a_2184_);
lean_dec(v_a_2183_);
return v_res_2194_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(lean_object* v_u_2195_, lean_object* v_type_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_){
_start:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v_smulType_2212_; lean_object* v___x_2213_; 
v___x_2204_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_2205_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_2206_ = lean_box(0);
lean_inc(v_u_2195_);
v___x_2207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2207_, 0, v_u_2195_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
v___x_2208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2208_, 0, v_u_2195_);
lean_ctor_set(v___x_2208_, 1, v___x_2207_);
v___x_2209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2205_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
lean_inc_ref(v___x_2209_);
v___x_2210_ = l_Lean_mkConst(v___x_2204_, v___x_2209_);
v___x_2211_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2196_, 2);
v_smulType_2212_ = l_Lean_mkApp3(v___x_2210_, v___x_2211_, v_type_2196_, v_type_2196_);
v___x_2213_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_smulType_2212_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2250_; 
v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2216_ = v___x_2213_;
v_isShared_2217_ = v_isSharedCheck_2250_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2213_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2250_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
if (lean_obj_tag(v_a_2214_) == 1)
{
lean_object* v_val_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2245_; 
lean_del_object(v___x_2216_);
v_val_2218_ = lean_ctor_get(v_a_2214_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v_a_2214_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2220_ = v_a_2214_;
v_isShared_2221_ = v_isSharedCheck_2245_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_val_2218_);
lean_dec(v_a_2214_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2245_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2222_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_2223_ = l_Lean_mkConst(v___x_2222_, v___x_2209_);
lean_inc_ref(v_type_2196_);
v___x_2224_ = l_Lean_mkApp4(v___x_2223_, v___x_2211_, v_type_2196_, v_type_2196_, v_val_2218_);
v___x_2225_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2224_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2236_; 
v_a_2226_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2228_ = v___x_2225_;
v_isShared_2229_ = v_isSharedCheck_2236_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2225_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2236_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 0, v_a_2226_);
v___x_2231_ = v___x_2220_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
lean_object* v___x_2233_; 
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 0, v___x_2231_);
v___x_2233_ = v___x_2228_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2231_);
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
else
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
lean_del_object(v___x_2220_);
v_a_2237_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2239_ = v___x_2225_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2225_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
}
else
{
lean_object* v___x_2246_; lean_object* v___x_2248_; 
lean_dec(v_a_2214_);
lean_dec_ref_known(v___x_2209_, 2);
lean_dec_ref(v_type_2196_);
v___x_2246_ = lean_box(0);
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 0, v___x_2246_);
v___x_2248_ = v___x_2216_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v___x_2246_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2209_, 2);
lean_dec_ref(v_type_2196_);
return v___x_2213_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_2195_ = stack[0].m_obj;
lean_object* v_type_2196_ = stack[1].m_obj;
lean_object* v_a_2197_ = stack[2].m_obj;
lean_object* v_a_2198_ = stack[3].m_obj;
lean_object* v_a_2199_ = stack[4].m_obj;
lean_object* v_a_2200_ = stack[5].m_obj;
lean_object* v_a_2201_ = stack[6].m_obj;
lean_object* v_a_2202_ = stack[7].m_obj;
lean_object* v_res_2251_;
v_res_2251_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(v_u_2195_, v_type_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
stack->m_obj
 = v_res_2251_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg___boxed(lean_object* v_u_2252_, lean_object* v_type_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(v_u_2252_, v_type_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_);
lean_dec(v_a_2259_);
lean_dec_ref(v_a_2258_);
lean_dec(v_a_2257_);
lean_dec_ref(v_a_2256_);
lean_dec(v_a_2255_);
lean_dec_ref(v_a_2254_);
return v_res_2261_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f(lean_object* v_u_2262_, lean_object* v_type_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_){
_start:
{
lean_object* v___x_2275_; 
v___x_2275_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(v_u_2262_, v_type_2263_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
return v___x_2275_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_2262_ = stack[0].m_obj;
lean_object* v_type_2263_ = stack[1].m_obj;
lean_object* v_a_2264_ = stack[2].m_obj;
lean_object* v_a_2265_ = stack[3].m_obj;
lean_object* v_a_2266_ = stack[4].m_obj;
lean_object* v_a_2267_ = stack[5].m_obj;
lean_object* v_a_2268_ = stack[6].m_obj;
lean_object* v_a_2269_ = stack[7].m_obj;
lean_object* v_a_2270_ = stack[8].m_obj;
lean_object* v_a_2271_ = stack[9].m_obj;
lean_object* v_a_2272_ = stack[10].m_obj;
lean_object* v_a_2273_ = stack[11].m_obj;
lean_object* v_res_2276_;
v_res_2276_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f(v_u_2262_, v_type_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
stack->m_obj
 = v_res_2276_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___boxed(lean_object* v_u_2277_, lean_object* v_type_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f(v_u_2277_, v_type_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_);
lean_dec(v_a_2288_);
lean_dec_ref(v_a_2287_);
lean_dec(v_a_2286_);
lean_dec_ref(v_a_2285_);
lean_dec(v_a_2284_);
lean_dec_ref(v_a_2283_);
lean_dec(v_a_2282_);
lean_dec_ref(v_a_2281_);
lean_dec(v_a_2280_);
lean_dec(v_a_2279_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2291_, lean_object* v_x_2292_, lean_object* v_x_2293_, lean_object* v_x_2294_){
_start:
{
lean_object* v_ks_2295_; lean_object* v_vs_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2322_; 
v_ks_2295_ = lean_ctor_get(v_x_2291_, 0);
v_vs_2296_ = lean_ctor_get(v_x_2291_, 1);
v_isSharedCheck_2322_ = !lean_is_exclusive(v_x_2291_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2298_ = v_x_2291_;
v_isShared_2299_ = v_isSharedCheck_2322_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_vs_2296_);
lean_inc(v_ks_2295_);
lean_dec(v_x_2291_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2322_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2300_; uint8_t v___x_2301_; 
v___x_2300_ = lean_array_get_size(v_ks_2295_);
v___x_2301_ = lean_nat_dec_lt(v_x_2292_, v___x_2300_);
if (v___x_2301_ == 0)
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2305_; 
lean_dec(v_x_2292_);
v___x_2302_ = lean_array_push(v_ks_2295_, v_x_2293_);
v___x_2303_ = lean_array_push(v_vs_2296_, v_x_2294_);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 1, v___x_2303_);
lean_ctor_set(v___x_2298_, 0, v___x_2302_);
v___x_2305_ = v___x_2298_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2302_);
lean_ctor_set(v_reuseFailAlloc_2306_, 1, v___x_2303_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
else
{
lean_object* v_k_x27_2307_; size_t v___x_2308_; size_t v___x_2309_; uint8_t v___x_2310_; 
v_k_x27_2307_ = lean_array_fget_borrowed(v_ks_2295_, v_x_2292_);
v___x_2308_ = lean_ptr_addr(v_x_2293_);
v___x_2309_ = lean_ptr_addr(v_k_x27_2307_);
v___x_2310_ = lean_usize_dec_eq(v___x_2308_, v___x_2309_);
if (v___x_2310_ == 0)
{
lean_object* v___x_2312_; 
if (v_isShared_2299_ == 0)
{
v___x_2312_ = v___x_2298_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_ks_2295_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v_vs_2296_);
v___x_2312_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = lean_unsigned_to_nat(1u);
v___x_2314_ = lean_nat_add(v_x_2292_, v___x_2313_);
lean_dec(v_x_2292_);
v_x_2291_ = v___x_2312_;
v_x_2292_ = v___x_2314_;
goto _start;
}
}
else
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2320_; 
v___x_2317_ = lean_array_fset(v_ks_2295_, v_x_2292_, v_x_2293_);
v___x_2318_ = lean_array_fset(v_vs_2296_, v_x_2292_, v_x_2294_);
lean_dec(v_x_2292_);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 1, v___x_2318_);
lean_ctor_set(v___x_2298_, 0, v___x_2317_);
v___x_2320_ = v___x_2298_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v___x_2317_);
lean_ctor_set(v_reuseFailAlloc_2321_, 1, v___x_2318_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2323_, lean_object* v_k_2324_, lean_object* v_v_2325_){
_start:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2326_ = lean_unsigned_to_nat(0u);
v___x_2327_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2323_, v___x_2326_, v_k_2324_, v_v_2325_);
return v___x_2327_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2328_; 
v___x_2328_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2328_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(lean_object* v_x_2329_, size_t v_x_2330_, size_t v_x_2331_, lean_object* v_x_2332_, lean_object* v_x_2333_){
_start:
{
if (lean_obj_tag(v_x_2329_) == 0)
{
lean_object* v_es_2334_; size_t v___x_2335_; size_t v___x_2336_; lean_object* v_j_2337_; lean_object* v___x_2338_; uint8_t v___x_2339_; 
v_es_2334_ = lean_ctor_get(v_x_2329_, 0);
v___x_2335_ = ((size_t)31ULL);
v___x_2336_ = lean_usize_land(v_x_2330_, v___x_2335_);
v_j_2337_ = lean_usize_to_nat(v___x_2336_);
v___x_2338_ = lean_array_get_size(v_es_2334_);
v___x_2339_ = lean_nat_dec_lt(v_j_2337_, v___x_2338_);
if (v___x_2339_ == 0)
{
lean_dec(v_j_2337_);
lean_dec(v_x_2333_);
lean_dec_ref(v_x_2332_);
return v_x_2329_;
}
else
{
lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2380_; 
lean_inc_ref(v_es_2334_);
v_isSharedCheck_2380_ = !lean_is_exclusive(v_x_2329_);
if (v_isSharedCheck_2380_ == 0)
{
lean_object* v_unused_2381_; 
v_unused_2381_ = lean_ctor_get(v_x_2329_, 0);
lean_dec(v_unused_2381_);
v___x_2341_ = v_x_2329_;
v_isShared_2342_ = v_isSharedCheck_2380_;
goto v_resetjp_2340_;
}
else
{
lean_dec(v_x_2329_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2380_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v_v_2343_; lean_object* v___x_2344_; lean_object* v_xs_x27_2345_; lean_object* v___y_2347_; 
v_v_2343_ = lean_array_fget(v_es_2334_, v_j_2337_);
v___x_2344_ = lean_box(0);
v_xs_x27_2345_ = lean_array_fset(v_es_2334_, v_j_2337_, v___x_2344_);
switch(lean_obj_tag(v_v_2343_))
{
case 0:
{
lean_object* v_key_2352_; lean_object* v_val_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2365_; 
v_key_2352_ = lean_ctor_get(v_v_2343_, 0);
v_val_2353_ = lean_ctor_get(v_v_2343_, 1);
v_isSharedCheck_2365_ = !lean_is_exclusive(v_v_2343_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2355_ = v_v_2343_;
v_isShared_2356_ = v_isSharedCheck_2365_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_val_2353_);
lean_inc(v_key_2352_);
lean_dec(v_v_2343_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2365_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
size_t v___x_2357_; size_t v___x_2358_; uint8_t v___x_2359_; 
v___x_2357_ = lean_ptr_addr(v_x_2332_);
v___x_2358_ = lean_ptr_addr(v_key_2352_);
v___x_2359_ = lean_usize_dec_eq(v___x_2357_, v___x_2358_);
if (v___x_2359_ == 0)
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
lean_del_object(v___x_2355_);
v___x_2360_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2352_, v_val_2353_, v_x_2332_, v_x_2333_);
v___x_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2360_);
v___y_2347_ = v___x_2361_;
goto v___jp_2346_;
}
else
{
lean_object* v___x_2363_; 
lean_dec(v_val_2353_);
lean_dec(v_key_2352_);
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 1, v_x_2333_);
lean_ctor_set(v___x_2355_, 0, v_x_2332_);
v___x_2363_ = v___x_2355_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_x_2332_);
lean_ctor_set(v_reuseFailAlloc_2364_, 1, v_x_2333_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
v___y_2347_ = v___x_2363_;
goto v___jp_2346_;
}
}
}
}
case 1:
{
lean_object* v_node_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2378_; 
v_node_2366_ = lean_ctor_get(v_v_2343_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v_v_2343_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2368_ = v_v_2343_;
v_isShared_2369_ = v_isSharedCheck_2378_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_node_2366_);
lean_dec(v_v_2343_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2378_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
size_t v___x_2370_; size_t v___x_2371_; size_t v___x_2372_; size_t v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2376_; 
v___x_2370_ = ((size_t)5ULL);
v___x_2371_ = lean_usize_shift_right(v_x_2330_, v___x_2370_);
v___x_2372_ = ((size_t)1ULL);
v___x_2373_ = lean_usize_add(v_x_2331_, v___x_2372_);
v___x_2374_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_node_2366_, v___x_2371_, v___x_2373_, v_x_2332_, v_x_2333_);
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 0, v___x_2374_);
v___x_2376_ = v___x_2368_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2374_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
v___y_2347_ = v___x_2376_;
goto v___jp_2346_;
}
}
}
default: 
{
lean_object* v___x_2379_; 
v___x_2379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2379_, 0, v_x_2332_);
lean_ctor_set(v___x_2379_, 1, v_x_2333_);
v___y_2347_ = v___x_2379_;
goto v___jp_2346_;
}
}
v___jp_2346_:
{
lean_object* v___x_2348_; lean_object* v___x_2350_; 
v___x_2348_ = lean_array_fset(v_xs_x27_2345_, v_j_2337_, v___y_2347_);
lean_dec(v_j_2337_);
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 0, v___x_2348_);
v___x_2350_ = v___x_2341_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
}
else
{
lean_object* v_ks_2382_; lean_object* v_vs_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2401_; 
v_ks_2382_ = lean_ctor_get(v_x_2329_, 0);
v_vs_2383_ = lean_ctor_get(v_x_2329_, 1);
v_isSharedCheck_2401_ = !lean_is_exclusive(v_x_2329_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2385_ = v_x_2329_;
v_isShared_2386_ = v_isSharedCheck_2401_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_vs_2383_);
lean_inc(v_ks_2382_);
lean_dec(v_x_2329_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2401_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2388_; 
if (v_isShared_2386_ == 0)
{
v___x_2388_ = v___x_2385_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_ks_2382_);
lean_ctor_set(v_reuseFailAlloc_2400_, 1, v_vs_2383_);
v___x_2388_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_object* v_newNode_2389_; size_t v___x_2390_; uint8_t v___x_2391_; 
v_newNode_2389_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1___redArg(v___x_2388_, v_x_2332_, v_x_2333_);
v___x_2390_ = ((size_t)7ULL);
v___x_2391_ = lean_usize_dec_le(v___x_2390_, v_x_2331_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2392_; lean_object* v___x_2393_; uint8_t v___x_2394_; 
v___x_2392_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2389_);
v___x_2393_ = lean_unsigned_to_nat(4u);
v___x_2394_ = lean_nat_dec_lt(v___x_2392_, v___x_2393_);
lean_dec(v___x_2392_);
if (v___x_2394_ == 0)
{
lean_object* v_ks_2395_; lean_object* v_vs_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v_ks_2395_ = lean_ctor_get(v_newNode_2389_, 0);
lean_inc_ref(v_ks_2395_);
v_vs_2396_ = lean_ctor_get(v_newNode_2389_, 1);
lean_inc_ref(v_vs_2396_);
lean_dec_ref(v_newNode_2389_);
v___x_2397_ = lean_unsigned_to_nat(0u);
v___x_2398_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0);
v___x_2399_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(v_x_2331_, v_ks_2395_, v_vs_2396_, v___x_2397_, v___x_2398_);
lean_dec_ref(v_vs_2396_);
lean_dec_ref(v_ks_2395_);
return v___x_2399_;
}
else
{
return v_newNode_2389_;
}
}
else
{
return v_newNode_2389_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2329_ = stack[0].m_obj;
size_t v_x_2330_ = stack[1].m_num;
size_t v_x_2331_ = stack[2].m_num;
lean_object* v_x_2332_ = stack[3].m_obj;
lean_object* v_x_2333_ = stack[4].m_obj;
lean_object* v_res_2402_;
v_res_2402_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_x_2329_, v_x_2330_, v_x_2331_, v_x_2332_, v_x_2333_);
stack->m_obj
 = v_res_2402_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(size_t v_depth_2403_, lean_object* v_keys_2404_, lean_object* v_vals_2405_, lean_object* v_i_2406_, lean_object* v_entries_2407_){
_start:
{
lean_object* v___x_2408_; uint8_t v___x_2409_; 
v___x_2408_ = lean_array_get_size(v_keys_2404_);
v___x_2409_ = lean_nat_dec_lt(v_i_2406_, v___x_2408_);
if (v___x_2409_ == 0)
{
lean_dec(v_i_2406_);
return v_entries_2407_;
}
else
{
lean_object* v_k_2410_; lean_object* v_v_2411_; size_t v___x_2412_; size_t v___x_2413_; size_t v___x_2414_; uint64_t v___x_2415_; size_t v_h_2416_; size_t v___x_2417_; lean_object* v___x_2418_; size_t v___x_2419_; size_t v___x_2420_; size_t v___x_2421_; size_t v_h_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v_k_2410_ = lean_array_fget_borrowed(v_keys_2404_, v_i_2406_);
v_v_2411_ = lean_array_fget_borrowed(v_vals_2405_, v_i_2406_);
v___x_2412_ = lean_ptr_addr(v_k_2410_);
v___x_2413_ = ((size_t)3ULL);
v___x_2414_ = lean_usize_shift_right(v___x_2412_, v___x_2413_);
v___x_2415_ = lean_usize_to_uint64(v___x_2414_);
v_h_2416_ = lean_uint64_to_usize(v___x_2415_);
v___x_2417_ = ((size_t)5ULL);
v___x_2418_ = lean_unsigned_to_nat(1u);
v___x_2419_ = ((size_t)1ULL);
v___x_2420_ = lean_usize_sub(v_depth_2403_, v___x_2419_);
v___x_2421_ = lean_usize_mul(v___x_2417_, v___x_2420_);
v_h_2422_ = lean_usize_shift_right(v_h_2416_, v___x_2421_);
v___x_2423_ = lean_nat_add(v_i_2406_, v___x_2418_);
lean_dec(v_i_2406_);
lean_inc(v_v_2411_);
lean_inc(v_k_2410_);
v___x_2424_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_entries_2407_, v_h_2422_, v_depth_2403_, v_k_2410_, v_v_2411_);
v_i_2406_ = v___x_2423_;
v_entries_2407_ = v___x_2424_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2403_ = stack[0].m_num;
lean_object* v_keys_2404_ = stack[1].m_obj;
lean_object* v_vals_2405_ = stack[2].m_obj;
lean_object* v_i_2406_ = stack[3].m_obj;
lean_object* v_entries_2407_ = stack[4].m_obj;
lean_object* v_res_2426_;
v_res_2426_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(v_depth_2403_, v_keys_2404_, v_vals_2405_, v_i_2406_, v_entries_2407_);
stack->m_obj
 = v_res_2426_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2427_, lean_object* v_keys_2428_, lean_object* v_vals_2429_, lean_object* v_i_2430_, lean_object* v_entries_2431_){
_start:
{
size_t v_depth_boxed_2432_; lean_object* v_res_2433_; 
v_depth_boxed_2432_ = lean_unbox_usize(v_depth_2427_);
lean_dec(v_depth_2427_);
v_res_2433_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2432_, v_keys_2428_, v_vals_2429_, v_i_2430_, v_entries_2431_);
lean_dec_ref(v_vals_2429_);
lean_dec_ref(v_keys_2428_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_2434_, lean_object* v_x_2435_, lean_object* v_x_2436_, lean_object* v_x_2437_, lean_object* v_x_2438_){
_start:
{
size_t v_x_527754__boxed_2439_; size_t v_x_527755__boxed_2440_; lean_object* v_res_2441_; 
v_x_527754__boxed_2439_ = lean_unbox_usize(v_x_2435_);
lean_dec(v_x_2435_);
v_x_527755__boxed_2440_ = lean_unbox_usize(v_x_2436_);
lean_dec(v_x_2436_);
v_res_2441_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_x_2434_, v_x_527754__boxed_2439_, v_x_527755__boxed_2440_, v_x_2437_, v_x_2438_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(lean_object* v_x_2442_, lean_object* v_x_2443_, lean_object* v_x_2444_){
_start:
{
size_t v___x_2445_; size_t v___x_2446_; size_t v___x_2447_; uint64_t v___x_2448_; size_t v___x_2449_; size_t v___x_2450_; lean_object* v___x_2451_; 
v___x_2445_ = lean_ptr_addr(v_x_2443_);
v___x_2446_ = ((size_t)3ULL);
v___x_2447_ = lean_usize_shift_right(v___x_2445_, v___x_2446_);
v___x_2448_ = lean_usize_to_uint64(v___x_2447_);
v___x_2449_ = lean_uint64_to_usize(v___x_2448_);
v___x_2450_ = ((size_t)1ULL);
v___x_2451_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_x_2442_, v___x_2449_, v___x_2450_, v_x_2443_, v_x_2444_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__0(lean_object* v_type_2452_, lean_object* v_s_2453_){
_start:
{
lean_object* v_structs_2454_; lean_object* v_typeIdOf_2455_; lean_object* v_exprToStructId_2456_; lean_object* v_exprToStructIdEntries_2457_; lean_object* v_forbiddenNatModules_2458_; lean_object* v_natStructs_2459_; lean_object* v_natTypeIdOf_2460_; lean_object* v_exprToNatStructId_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2470_; 
v_structs_2454_ = lean_ctor_get(v_s_2453_, 0);
v_typeIdOf_2455_ = lean_ctor_get(v_s_2453_, 1);
v_exprToStructId_2456_ = lean_ctor_get(v_s_2453_, 2);
v_exprToStructIdEntries_2457_ = lean_ctor_get(v_s_2453_, 3);
v_forbiddenNatModules_2458_ = lean_ctor_get(v_s_2453_, 4);
v_natStructs_2459_ = lean_ctor_get(v_s_2453_, 5);
v_natTypeIdOf_2460_ = lean_ctor_get(v_s_2453_, 6);
v_exprToNatStructId_2461_ = lean_ctor_get(v_s_2453_, 7);
v_isSharedCheck_2470_ = !lean_is_exclusive(v_s_2453_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2463_ = v_s_2453_;
v_isShared_2464_ = v_isSharedCheck_2470_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_exprToNatStructId_2461_);
lean_inc(v_natTypeIdOf_2460_);
lean_inc(v_natStructs_2459_);
lean_inc(v_forbiddenNatModules_2458_);
lean_inc(v_exprToStructIdEntries_2457_);
lean_inc(v_exprToStructId_2456_);
lean_inc(v_typeIdOf_2455_);
lean_inc(v_structs_2454_);
lean_dec(v_s_2453_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2470_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2468_; 
v___x_2465_ = lean_box(0);
v___x_2466_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_forbiddenNatModules_2458_, v_type_2452_, v___x_2465_);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 4, v___x_2466_);
v___x_2468_ = v___x_2463_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_structs_2454_);
lean_ctor_set(v_reuseFailAlloc_2469_, 1, v_typeIdOf_2455_);
lean_ctor_set(v_reuseFailAlloc_2469_, 2, v_exprToStructId_2456_);
lean_ctor_set(v_reuseFailAlloc_2469_, 3, v_exprToStructIdEntries_2457_);
lean_ctor_set(v_reuseFailAlloc_2469_, 4, v___x_2466_);
lean_ctor_set(v_reuseFailAlloc_2469_, 5, v_natStructs_2459_);
lean_ctor_set(v_reuseFailAlloc_2469_, 6, v_natTypeIdOf_2460_);
lean_ctor_set(v_reuseFailAlloc_2469_, 7, v_exprToNatStructId_2461_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2(lean_object* v_a_2471_, lean_object* v_00___2472_){
_start:
{
if (lean_obj_tag(v_a_2471_) == 0)
{
uint8_t v___x_2473_; 
v___x_2473_ = 0;
return v___x_2473_;
}
else
{
uint8_t v___x_2474_; 
v___x_2474_ = 1;
return v___x_2474_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2471_ = stack[0].m_obj;
lean_object* v_00___2472_ = stack[1].m_obj;
uint8_t v_res_2475_;
v_res_2475_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2(v_a_2471_, v_00___2472_);
stack->m_num = v_res_2475_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2___boxed(lean_object* v_a_2476_, lean_object* v_00___2477_){
_start:
{
uint8_t v_res_2478_; lean_object* v_r_2479_; 
v_res_2478_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2(v_a_2476_, v_00___2477_);
lean_dec(v_a_2476_);
v_r_2479_ = lean_box(v_res_2478_);
return v_r_2479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1(lean_object* v___x_2480_, lean_object* v_s_2481_){
_start:
{
lean_object* v_structs_2482_; lean_object* v_typeIdOf_2483_; lean_object* v_exprToStructId_2484_; lean_object* v_exprToStructIdEntries_2485_; lean_object* v_forbiddenNatModules_2486_; lean_object* v_natStructs_2487_; lean_object* v_natTypeIdOf_2488_; lean_object* v_exprToNatStructId_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2497_; 
v_structs_2482_ = lean_ctor_get(v_s_2481_, 0);
v_typeIdOf_2483_ = lean_ctor_get(v_s_2481_, 1);
v_exprToStructId_2484_ = lean_ctor_get(v_s_2481_, 2);
v_exprToStructIdEntries_2485_ = lean_ctor_get(v_s_2481_, 3);
v_forbiddenNatModules_2486_ = lean_ctor_get(v_s_2481_, 4);
v_natStructs_2487_ = lean_ctor_get(v_s_2481_, 5);
v_natTypeIdOf_2488_ = lean_ctor_get(v_s_2481_, 6);
v_exprToNatStructId_2489_ = lean_ctor_get(v_s_2481_, 7);
v_isSharedCheck_2497_ = !lean_is_exclusive(v_s_2481_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2491_ = v_s_2481_;
v_isShared_2492_ = v_isSharedCheck_2497_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_exprToNatStructId_2489_);
lean_inc(v_natTypeIdOf_2488_);
lean_inc(v_natStructs_2487_);
lean_inc(v_forbiddenNatModules_2486_);
lean_inc(v_exprToStructIdEntries_2485_);
lean_inc(v_exprToStructId_2484_);
lean_inc(v_typeIdOf_2483_);
lean_inc(v_structs_2482_);
lean_dec(v_s_2481_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2497_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2493_; lean_object* v___x_2495_; 
v___x_2493_ = lean_array_push(v_structs_2482_, v___x_2480_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 0, v___x_2493_);
v___x_2495_ = v___x_2491_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2493_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v_typeIdOf_2483_);
lean_ctor_set(v_reuseFailAlloc_2496_, 2, v_exprToStructId_2484_);
lean_ctor_set(v_reuseFailAlloc_2496_, 3, v_exprToStructIdEntries_2485_);
lean_ctor_set(v_reuseFailAlloc_2496_, 4, v_forbiddenNatModules_2486_);
lean_ctor_set(v_reuseFailAlloc_2496_, 5, v_natStructs_2487_);
lean_ctor_set(v_reuseFailAlloc_2496_, 6, v_natTypeIdOf_2488_);
lean_ctor_set(v_reuseFailAlloc_2496_, 7, v_exprToNatStructId_2489_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4(void){
_start:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2504_ = lean_unsigned_to_nat(32u);
v___x_2505_ = lean_mk_empty_array_with_capacity(v___x_2504_);
v___x_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2505_);
return v___x_2506_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5(void){
_start:
{
lean_object* v___x_2507_; 
v___x_2507_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2507_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6(void){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5);
v___x_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2508_);
return v___x_2509_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19(void){
_start:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2531_ = lean_unsigned_to_nat(0u);
v___x_2532_ = l_Lean_mkRawNatLit(v___x_2531_);
return v___x_2532_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42(void){
_start:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2566_ = l_Lean_Int_mkType;
v___x_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2566_);
return v___x_2567_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44(void){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2569_ = l_Lean_Nat_mkType;
v___x_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2569_);
return v___x_2570_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f(lean_object* v_type_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_){
_start:
{
lean_object* v___y_2631_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; uint8_t v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; uint8_t v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___f_2696_; lean_object* v___x_2697_; 
lean_inc_ref_n(v_type_2618_, 2);
v___f_2696_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__0), 2, 1);
lean_closure_set(v___f_2696_, 0, v_type_2618_);
v___x_2697_ = l_Lean_Meta_getDecLevel_x3f(v_type_2618_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_3614_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_2700_ = v___x_2697_;
v_isShared_2701_ = v_isSharedCheck_3614_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2697_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_3614_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
if (lean_obj_tag(v_a_2698_) == 1)
{
lean_object* v_val_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_3609_; 
lean_del_object(v___x_2700_);
v_val_2702_ = lean_ctor_get(v_a_2698_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v_a_2698_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_2704_ = v_a_2698_;
v_isShared_2705_ = v_isSharedCheck_3609_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_val_2702_);
lean_dec(v_a_2698_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_3609_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2706_; 
lean_inc_ref(v_type_2618_);
v___x_2706_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___redArg(v_type_2618_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
if (lean_obj_tag(v___x_2706_) == 0)
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_3608_; 
v_a_2707_ = lean_ctor_get(v___x_2706_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_2709_ = v___x_2706_;
v_isShared_2710_ = v_isSharedCheck_3608_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2706_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_3608_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2711_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1));
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
v___x_2712_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_2711_, v_val_2702_, v_type_2618_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_object* v_a_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v_a_2713_ = lean_ctor_get(v___x_2712_, 0);
lean_inc(v_a_2713_);
lean_dec_ref_known(v___x_2712_, 1);
v___x_2714_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__3));
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
v___x_2715_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_2714_, v_val_2702_, v_type_2618_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2717_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
lean_inc_n(v_a_2716_, 2);
lean_dec_ref_known(v___x_2715_, 1);
lean_inc(v_a_2713_);
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
v___x_2717_ = l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f(v_val_2702_, v_type_2618_, v_a_2716_, v_a_2713_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v_a_2718_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; uint8_t v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v_homomulFn_x3f_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; uint8_t v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v_ltFn_x3f_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; uint8_t v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v_leFn_x3f_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; uint8_t v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v_charInst_x3f_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___x_3230_; 
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_a_2718_);
lean_dec_ref_known(v___x_2717_, 1);
lean_inc(v_a_2713_);
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
v___x_3230_ = l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f(v_val_2702_, v_type_2618_, v_a_2713_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; lean_object* v___x_3232_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_a_3231_);
lean_dec_ref_known(v___x_3230_, 1);
lean_inc(v_a_2713_);
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
v___x_3232_ = l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f(v_val_2702_, v_type_2618_, v_a_2713_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v_a_3233_; lean_object* v___x_3234_; 
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
lean_inc(v_a_3233_);
lean_dec_ref_known(v___x_3232_, 1);
lean_inc(v_a_2713_);
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
v___x_3234_ = l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f(v_val_2702_, v_type_2618_, v_a_2713_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v_a_3235_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; uint8_t v___y_3257_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; uint8_t v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; uint8_t v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; uint8_t v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___x_3441_; 
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
lean_inc(v_a_3235_);
lean_dec_ref_known(v___x_3234_, 1);
v___x_3441_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2621_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v_a_3442_; uint8_t v___y_3444_; uint8_t v_ring_3529_; 
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_a_3442_);
lean_dec_ref_known(v___x_3441_, 1);
v_ring_3529_ = lean_ctor_get_uint8(v_a_3442_, sizeof(void*)*14 + 21);
lean_dec(v_a_3442_);
if (v_ring_3529_ == 0)
{
v___y_3444_ = v_ring_3529_;
goto v___jp_3443_;
}
else
{
lean_object* v___x_3530_; uint8_t v___x_3531_; 
v___x_3530_ = lean_box(0);
v___x_3531_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2(v_a_2707_, v___x_3530_);
if (v___x_3531_ == 0)
{
v___y_3444_ = v___x_3531_;
goto v___jp_3443_;
}
else
{
if (lean_obj_tag(v_a_3231_) == 0)
{
lean_object* v___x_3532_; lean_object* v___x_3533_; 
lean_dec(v_a_3235_);
lean_dec(v_a_3233_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v___x_3532_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3533_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3532_, v___f_2696_, v_a_2619_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3541_; 
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3541_ == 0)
{
lean_object* v_unused_3542_; 
v_unused_3542_ = lean_ctor_get(v___x_3533_, 0);
lean_dec(v_unused_3542_);
v___x_3535_ = v___x_3533_;
v_isShared_3536_ = v_isSharedCheck_3541_;
goto v_resetjp_3534_;
}
else
{
lean_dec(v___x_3533_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3541_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3537_; lean_object* v___x_3539_; 
v___x_3537_ = lean_box(0);
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 0, v___x_3537_);
v___x_3539_ = v___x_3535_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v___x_3537_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
else
{
lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3550_; 
v_a_3543_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3545_ = v___x_3533_;
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3533_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3548_; 
if (v_isShared_3546_ == 0)
{
v___x_3548_ = v___x_3545_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_a_3543_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
}
else
{
uint8_t v___x_3551_; 
v___x_3551_ = 0;
v___y_3444_ = v___x_3551_;
goto v___jp_3443_;
}
}
}
v___jp_3443_:
{
lean_object* v___x_3445_; 
lean_inc(v_a_2707_);
v___x_3445_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(v_a_2707_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v_a_3446_; lean_object* v___x_3447_; 
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
lean_inc_n(v_a_3446_, 2);
lean_dec_ref_known(v___x_3445_, 1);
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
v___x_3447_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_val_2702_, v_type_2618_, v_a_3446_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_object* v_a_3448_; lean_object* v___x_3449_; 
v_a_3448_ = lean_ctor_get(v___x_3447_, 0);
lean_inc_n(v_a_3448_, 2);
lean_dec_ref_known(v___x_3447_, 1);
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
v___x_3449_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_val_2702_, v_type_2618_, v_a_3448_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3504_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3452_ = v___x_3449_;
v_isShared_3453_ = v_isSharedCheck_3504_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3449_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3504_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
if (lean_obj_tag(v_a_3450_) == 1)
{
lean_object* v_val_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
lean_del_object(v___x_3452_);
v_val_3454_ = lean_ctor_get(v_a_3450_, 0);
lean_inc(v_val_3454_);
lean_dec_ref_known(v_a_3450_, 1);
v___x_3455_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
v___x_3456_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_3455_, v_val_2702_, v_type_2618_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
lean_inc_n(v_a_3457_, 2);
lean_dec_ref_known(v___x_3456_, 1);
v___x_3458_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__64));
v___x_3459_ = lean_box(0);
lean_inc_n(v_val_2702_, 3);
v___x_3460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3460_, 0, v_val_2702_);
lean_ctor_set(v___x_3460_, 1, v___x_3459_);
lean_inc_ref(v___x_3460_);
v___x_3461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3461_, 0, v_val_2702_);
lean_ctor_set(v___x_3461_, 1, v___x_3460_);
lean_inc_ref(v___x_3461_);
v___x_3462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3462_, 0, v_val_2702_);
lean_ctor_set(v___x_3462_, 1, v___x_3461_);
lean_inc_ref(v___x_3462_);
v___x_3463_ = l_Lean_mkConst(v___x_3458_, v___x_3462_);
lean_inc_ref_n(v_type_2618_, 3);
v___x_3464_ = l_Lean_mkApp4(v___x_3463_, v_type_2618_, v_type_2618_, v_type_2618_, v_a_3457_);
v___x_3465_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3464_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
if (lean_obj_tag(v___x_3465_) == 0)
{
if (lean_obj_tag(v_a_2713_) == 1)
{
if (lean_obj_tag(v_a_3231_) == 1)
{
lean_object* v_a_3466_; lean_object* v_val_3467_; lean_object* v_val_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; 
v_a_3466_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_a_3466_);
lean_dec_ref_known(v___x_3465_, 1);
v_val_3467_ = lean_ctor_get(v_a_2713_, 0);
v_val_3468_ = lean_ctor_get(v_a_3231_, 0);
v___x_3469_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__66));
lean_inc_ref(v___x_3460_);
v___x_3470_ = l_Lean_mkConst(v___x_3469_, v___x_3460_);
lean_inc(v_val_3468_);
lean_inc(v_val_3467_);
lean_inc(v_a_3457_);
lean_inc_ref(v_type_2618_);
v___x_3471_ = l_Lean_mkApp4(v___x_3470_, v_type_2618_, v_a_3457_, v_val_3467_, v_val_3468_);
v___x_3472_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_3471_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v_a_3473_; 
v_a_3473_ = lean_ctor_get(v___x_3472_, 0);
lean_inc(v_a_3473_);
lean_dec_ref_known(v___x_3472_, 1);
if (lean_obj_tag(v_a_3473_) == 0)
{
lean_dec_ref_known(v_a_3231_, 1);
v___y_3399_ = v_a_2619_;
v___y_3400_ = v___x_3460_;
v___y_3401_ = v_a_2624_;
v___y_3402_ = v_a_3473_;
v___y_3403_ = v_a_2621_;
v___y_3404_ = v_a_2622_;
v___y_3405_ = v_a_2628_;
v___y_3406_ = v___x_3462_;
v___y_3407_ = v___y_3444_;
v___y_3408_ = v_a_3466_;
v___y_3409_ = v_a_2625_;
v___y_3410_ = v_a_2626_;
v___y_3411_ = v_a_2627_;
v___y_3412_ = v_a_2620_;
v___y_3413_ = v_a_3446_;
v___y_3414_ = v___x_3461_;
v___y_3415_ = v_val_3454_;
v___y_3416_ = v_a_3448_;
v___y_3417_ = v_a_2623_;
v___y_3418_ = v_a_3457_;
goto v___jp_3398_;
}
else
{
if (v___y_3444_ == 0)
{
v___y_3345_ = v_a_2619_;
v___y_3346_ = v___x_3460_;
v___y_3347_ = v_a_2624_;
v___y_3348_ = v_a_3473_;
v___y_3349_ = v_a_2621_;
v___y_3350_ = v_a_2622_;
v___y_3351_ = v_a_2628_;
v___y_3352_ = v___x_3462_;
v___y_3353_ = v___y_3444_;
v___y_3354_ = v_a_3466_;
v___y_3355_ = v_a_2625_;
v___y_3356_ = v_a_2626_;
v___y_3357_ = v_a_2627_;
v___y_3358_ = v_a_2620_;
v___y_3359_ = v_a_3446_;
v___y_3360_ = v___x_3461_;
v___y_3361_ = v_a_3448_;
v___y_3362_ = v_val_3454_;
v___y_3363_ = v_a_2623_;
v___y_3364_ = v_a_3457_;
v___y_3365_ = v_a_3231_;
goto v___jp_3344_;
}
else
{
lean_dec_ref_known(v_a_3231_, 1);
v___y_3399_ = v_a_2619_;
v___y_3400_ = v___x_3460_;
v___y_3401_ = v_a_2624_;
v___y_3402_ = v_a_3473_;
v___y_3403_ = v_a_2621_;
v___y_3404_ = v_a_2622_;
v___y_3405_ = v_a_2628_;
v___y_3406_ = v___x_3462_;
v___y_3407_ = v___y_3444_;
v___y_3408_ = v_a_3466_;
v___y_3409_ = v_a_2625_;
v___y_3410_ = v_a_2626_;
v___y_3411_ = v_a_2627_;
v___y_3412_ = v_a_2620_;
v___y_3413_ = v_a_3446_;
v___y_3414_ = v___x_3461_;
v___y_3415_ = v_val_3454_;
v___y_3416_ = v_a_3448_;
v___y_3417_ = v_a_2623_;
v___y_3418_ = v_a_3457_;
goto v___jp_3398_;
}
}
}
else
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3481_; 
lean_dec(v_a_3466_);
lean_dec_ref_known(v_a_3231_, 1);
lean_dec_ref_known(v_a_2713_, 1);
lean_dec_ref_known(v___x_3462_, 2);
lean_dec_ref_known(v___x_3461_, 2);
lean_dec_ref_known(v___x_3460_, 2);
lean_dec(v_a_3457_);
lean_dec(v_val_3454_);
lean_dec(v_a_3448_);
lean_dec(v_a_3446_);
lean_dec(v_a_3235_);
lean_dec(v_a_3233_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v___f_2696_);
lean_dec_ref(v_type_2618_);
v_a_3474_ = lean_ctor_get(v___x_3472_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3476_ = v___x_3472_;
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3472_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3479_; 
if (v_isShared_3477_ == 0)
{
v___x_3479_ = v___x_3476_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3474_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
}
else
{
lean_object* v_a_3482_; 
lean_dec(v_a_3231_);
v_a_3482_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_a_3482_);
lean_dec_ref_known(v___x_3465_, 1);
v___y_3421_ = v___y_3444_;
v___y_3422_ = v_a_3482_;
v___y_3423_ = v___x_3460_;
v___y_3424_ = v_a_3446_;
v___y_3425_ = v___x_3461_;
v___y_3426_ = v_a_3448_;
v___y_3427_ = v_val_3454_;
v___y_3428_ = v___x_3462_;
v___y_3429_ = v_a_3457_;
v___y_3430_ = v_a_2619_;
v___y_3431_ = v_a_2620_;
v___y_3432_ = v_a_2621_;
v___y_3433_ = v_a_2622_;
v___y_3434_ = v_a_2623_;
v___y_3435_ = v_a_2624_;
v___y_3436_ = v_a_2625_;
v___y_3437_ = v_a_2626_;
v___y_3438_ = v_a_2627_;
v___y_3439_ = v_a_2628_;
goto v___jp_3420_;
}
}
else
{
lean_object* v_a_3483_; 
lean_dec(v_a_3231_);
v_a_3483_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_a_3483_);
lean_dec_ref_known(v___x_3465_, 1);
v___y_3421_ = v___y_3444_;
v___y_3422_ = v_a_3483_;
v___y_3423_ = v___x_3460_;
v___y_3424_ = v_a_3446_;
v___y_3425_ = v___x_3461_;
v___y_3426_ = v_a_3448_;
v___y_3427_ = v_val_3454_;
v___y_3428_ = v___x_3462_;
v___y_3429_ = v_a_3457_;
v___y_3430_ = v_a_2619_;
v___y_3431_ = v_a_2620_;
v___y_3432_ = v_a_2621_;
v___y_3433_ = v_a_2622_;
v___y_3434_ = v_a_2623_;
v___y_3435_ = v_a_2624_;
v___y_3436_ = v_a_2625_;
v___y_3437_ = v_a_2626_;
v___y_3438_ = v_a_2627_;
v___y_3439_ = v_a_2628_;
goto v___jp_3420_;
}
}
else
{
lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3491_; 
lean_dec_ref_known(v___x_3462_, 2);
lean_dec_ref_known(v___x_3461_, 2);
lean_dec_ref_known(v___x_3460_, 2);
lean_dec(v_a_3457_);
lean_dec(v_val_3454_);
lean_dec(v_a_3448_);
lean_dec(v_a_3446_);
lean_dec(v_a_3235_);
lean_dec(v_a_3233_);
lean_dec(v_a_3231_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v___f_2696_);
lean_dec_ref(v_type_2618_);
v_a_3484_ = lean_ctor_get(v___x_3465_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3486_ = v___x_3465_;
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_dec(v___x_3465_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3489_; 
if (v_isShared_3487_ == 0)
{
v___x_3489_ = v___x_3486_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_a_3484_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
}
}
else
{
lean_object* v_a_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3499_; 
lean_dec(v_val_3454_);
lean_dec(v_a_3448_);
lean_dec(v_a_3446_);
lean_dec(v_a_3235_);
lean_dec(v_a_3233_);
lean_dec(v_a_3231_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v___f_2696_);
lean_dec_ref(v_type_2618_);
v_a_3492_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3499_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3494_ = v___x_3456_;
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_a_3492_);
lean_dec(v___x_3456_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3497_; 
if (v_isShared_3495_ == 0)
{
v___x_3497_ = v___x_3494_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_a_3492_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
}
}
else
{
lean_object* v___x_3500_; lean_object* v___x_3502_; 
lean_dec(v_a_3450_);
lean_dec(v_a_3448_);
lean_dec(v_a_3446_);
lean_dec(v_a_3235_);
lean_dec(v_a_3233_);
lean_dec(v_a_3231_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v___f_2696_);
lean_dec_ref(v_type_2618_);
v___x_3500_ = lean_box(0);
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 0, v___x_3500_);
v___x_3502_ = v___x_3452_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v___x_3500_);
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
lean_dec(v_a_3448_);
lean_dec(v_a_3446_);
lean_dec(v_a_3235_);
lean_dec(v_a_3233_);
lean_dec(v_a_3231_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v___f_2696_);
lean_dec_ref(v_type_2618_);
v_a_3505_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3449_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3449_);
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
else
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3520_; 
lean_dec(v_a_3446_);
lean_dec(v_a_3235_);
lean_dec(v_a_3233_);
lean_dec(v_a_3231_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v___f_2696_);
lean_dec_ref(v_type_2618_);
v_a_3513_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3515_ = v___x_3447_;
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3447_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3518_; 
if (v_isShared_3516_ == 0)
{
v___x_3518_ = v___x_3515_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_a_3513_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
}
}
}
}
else
{
lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3528_; 
lean_dec(v_a_3235_);
lean_dec(v_a_3233_);
lean_dec(v_a_3231_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v___f_2696_);
lean_dec_ref(v_type_2618_);
v_a_3521_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3523_ = v___x_3445_;
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v___x_3445_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3526_; 
if (v_isShared_3524_ == 0)
{
v___x_3526_ = v___x_3523_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_a_3521_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
}
}
else
{
lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3559_; 
lean_dec(v_a_3235_);
lean_dec(v_a_3233_);
lean_dec(v_a_3231_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v___f_2696_);
lean_dec_ref(v_type_2618_);
v_a_3552_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3559_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3554_ = v___x_3441_;
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_dec(v___x_3441_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3557_; 
if (v_isShared_3555_ == 0)
{
v___x_3557_ = v___x_3554_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_a_3552_);
v___x_3557_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
return v___x_3557_;
}
}
}
v___jp_3236_:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3258_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__50));
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
lean_inc(v___y_3241_);
lean_inc(v_a_2713_);
v___x_3259_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_a_2713_, v___y_3241_, v_a_3233_, v___x_3258_, v_val_2702_, v_type_2618_, v___y_3255_, v___y_3239_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3244_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v_a_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_a_3260_);
lean_dec_ref_known(v___x_3259_, 1);
v___x_3261_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__53));
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
lean_inc(v_a_2713_);
v___x_3262_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_a_2713_, v_a_3260_, v_a_3235_, v___x_3261_, v_val_2702_, v_type_2618_, v___y_3255_, v___y_3239_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3244_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_object* v_a_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
lean_inc(v_a_3263_);
lean_dec_ref_known(v___x_3262_, 1);
v___x_3264_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0));
v___x_3265_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1));
v___x_3266_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2));
v___x_3267_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__55));
lean_inc_n(v___y_3238_, 2);
v___x_3268_ = l_Lean_mkConst(v___x_3267_, v___y_3238_);
lean_inc_ref(v___y_3253_);
lean_inc_ref_n(v_type_2618_, 3);
v___x_3269_ = l_Lean_mkAppB(v___x_3268_, v_type_2618_, v___y_3253_);
v___x_3270_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__56));
v___x_3271_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58));
v___x_3272_ = l_Lean_mkConst(v___x_3271_, v___y_3238_);
lean_inc_ref(v___x_3269_);
v___x_3273_ = l_Lean_mkAppB(v___x_3272_, v_type_2618_, v___x_3269_);
lean_inc(v___y_3254_);
lean_inc(v_val_2702_);
v___x_3274_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_val_2702_, v_type_2618_, v___y_3254_, v___y_3239_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3244_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref_known(v___x_3274_, 1);
v___x_3276_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__60));
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
v___x_3277_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_3276_, v_val_2702_, v_type_2618_, v___y_3239_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3244_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; lean_object* v___x_3279_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_a_3278_);
lean_dec_ref_known(v___x_3277_, 1);
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
v___x_3279_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(v_val_2702_, v_type_2618_, v___y_3237_, v___y_3250_, v___y_3243_, v___y_3242_, v___y_3255_, v___y_3239_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3244_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_object* v_a_3280_; lean_object* v___x_3281_; 
v_a_3280_ = lean_ctor_get(v___x_3279_, 0);
lean_inc(v_a_3280_);
lean_dec_ref_known(v___x_3279_, 1);
lean_inc(v___y_3241_);
lean_inc(v_a_2716_);
lean_inc(v_a_2713_);
lean_inc(v_a_3275_);
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
v___x_3281_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_val_2702_, v_type_2618_, v_a_3275_, v_a_2713_, v_a_2716_, v___y_3241_, v___y_3255_, v___y_3239_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3244_);
if (lean_obj_tag(v___x_3281_) == 0)
{
if (lean_obj_tag(v_a_3275_) == 1)
{
lean_object* v_a_3282_; lean_object* v_val_3283_; lean_object* v___x_3284_; 
v_a_3282_ = lean_ctor_get(v___x_3281_, 0);
lean_inc(v_a_3282_);
lean_dec_ref_known(v___x_3281_, 1);
v_val_3283_ = lean_ctor_get(v_a_3275_, 0);
lean_inc(v_val_3283_);
lean_dec_ref_known(v_a_3275_, 1);
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
v___x_3284_ = l_Lean_Meta_Sym_Arith_getIsCharInst_x3f(v_val_2702_, v_type_2618_, v_val_3283_, v___y_3255_, v___y_3239_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3244_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v_a_3285_; 
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_a_3285_);
lean_dec_ref_known(v___x_3284_, 1);
v___y_2928_ = v___x_3273_;
v___y_2929_ = v_a_3278_;
v___y_2930_ = v___y_3238_;
v___y_2931_ = v___x_3270_;
v___y_2932_ = v___y_3241_;
v___y_2933_ = v___y_3240_;
v___y_2934_ = v_a_3263_;
v___y_2935_ = v___x_3266_;
v___y_2936_ = v___x_3269_;
v___y_2937_ = v___x_3265_;
v___y_2938_ = v___y_3257_;
v___y_2939_ = v___y_3245_;
v___y_2940_ = v___y_3246_;
v___y_2941_ = v_a_3282_;
v___y_2942_ = v_a_3280_;
v___y_2943_ = v___y_3251_;
v___y_2944_ = v___x_3264_;
v___y_2945_ = v___y_3252_;
v___y_2946_ = v___y_3254_;
v___y_2947_ = v___y_3253_;
v___y_2948_ = v___y_3256_;
v_charInst_x3f_2949_ = v_a_3285_;
v___y_2950_ = v___y_3237_;
v___y_2951_ = v___y_3250_;
v___y_2952_ = v___y_3243_;
v___y_2953_ = v___y_3242_;
v___y_2954_ = v___y_3255_;
v___y_2955_ = v___y_3239_;
v___y_2956_ = v___y_3247_;
v___y_2957_ = v___y_3248_;
v___y_2958_ = v___y_3249_;
v___y_2959_ = v___y_3244_;
goto v___jp_2927_;
}
else
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3293_; 
lean_dec(v_a_3282_);
lean_dec(v_a_3280_);
lean_dec(v_a_3278_);
lean_dec_ref(v___x_3273_);
lean_dec_ref(v___x_3269_);
lean_dec(v_a_3263_);
lean_dec_ref(v___y_3256_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec(v___y_3238_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_3286_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3288_ = v___x_3284_;
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3284_);
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
lean_object* v_a_3294_; lean_object* v___x_3295_; 
lean_dec(v_a_3275_);
v_a_3294_ = lean_ctor_get(v___x_3281_, 0);
lean_inc(v_a_3294_);
lean_dec_ref_known(v___x_3281_, 1);
v___x_3295_ = lean_box(0);
v___y_2928_ = v___x_3273_;
v___y_2929_ = v_a_3278_;
v___y_2930_ = v___y_3238_;
v___y_2931_ = v___x_3270_;
v___y_2932_ = v___y_3241_;
v___y_2933_ = v___y_3240_;
v___y_2934_ = v_a_3263_;
v___y_2935_ = v___x_3266_;
v___y_2936_ = v___x_3269_;
v___y_2937_ = v___x_3265_;
v___y_2938_ = v___y_3257_;
v___y_2939_ = v___y_3245_;
v___y_2940_ = v___y_3246_;
v___y_2941_ = v_a_3294_;
v___y_2942_ = v_a_3280_;
v___y_2943_ = v___y_3251_;
v___y_2944_ = v___x_3264_;
v___y_2945_ = v___y_3252_;
v___y_2946_ = v___y_3254_;
v___y_2947_ = v___y_3253_;
v___y_2948_ = v___y_3256_;
v_charInst_x3f_2949_ = v___x_3295_;
v___y_2950_ = v___y_3237_;
v___y_2951_ = v___y_3250_;
v___y_2952_ = v___y_3243_;
v___y_2953_ = v___y_3242_;
v___y_2954_ = v___y_3255_;
v___y_2955_ = v___y_3239_;
v___y_2956_ = v___y_3247_;
v___y_2957_ = v___y_3248_;
v___y_2958_ = v___y_3249_;
v___y_2959_ = v___y_3244_;
goto v___jp_2927_;
}
}
else
{
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3303_; 
lean_dec(v_a_3280_);
lean_dec(v_a_3278_);
lean_dec(v_a_3275_);
lean_dec_ref(v___x_3273_);
lean_dec_ref(v___x_3269_);
lean_dec(v_a_3263_);
lean_dec_ref(v___y_3256_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec(v___y_3238_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_3296_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3298_ = v___x_3281_;
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3281_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3301_; 
if (v_isShared_3299_ == 0)
{
v___x_3301_ = v___x_3298_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3296_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
}
}
}
}
else
{
lean_object* v_a_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3311_; 
lean_dec(v_a_3278_);
lean_dec(v_a_3275_);
lean_dec_ref(v___x_3273_);
lean_dec_ref(v___x_3269_);
lean_dec(v_a_3263_);
lean_dec_ref(v___y_3256_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec(v___y_3238_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_3304_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3311_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3311_ == 0)
{
v___x_3306_ = v___x_3279_;
v_isShared_3307_ = v_isSharedCheck_3311_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_a_3304_);
lean_dec(v___x_3279_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3311_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v___x_3309_; 
if (v_isShared_3307_ == 0)
{
v___x_3309_ = v___x_3306_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_a_3304_);
v___x_3309_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
return v___x_3309_;
}
}
}
}
else
{
lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3319_; 
lean_dec(v_a_3275_);
lean_dec_ref(v___x_3273_);
lean_dec_ref(v___x_3269_);
lean_dec(v_a_3263_);
lean_dec_ref(v___y_3256_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec(v___y_3238_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_3312_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3314_ = v___x_3277_;
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_dec(v___x_3277_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3317_; 
if (v_isShared_3315_ == 0)
{
v___x_3317_ = v___x_3314_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_a_3312_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
}
else
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3327_; 
lean_dec_ref(v___x_3273_);
lean_dec_ref(v___x_3269_);
lean_dec(v_a_3263_);
lean_dec_ref(v___y_3256_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec(v___y_3238_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_3320_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3322_ = v___x_3274_;
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3274_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3325_; 
if (v_isShared_3323_ == 0)
{
v___x_3325_ = v___x_3322_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3320_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
}
else
{
lean_object* v_a_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3335_; 
lean_dec_ref(v___y_3256_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec(v___y_3238_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_3328_ = lean_ctor_get(v___x_3262_, 0);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3262_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3330_ = v___x_3262_;
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_a_3328_);
lean_dec(v___x_3262_);
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
lean_object* v_a_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3343_; 
lean_dec_ref(v___y_3256_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec(v___y_3238_);
lean_dec(v_a_3235_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_3336_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3338_ = v___x_3259_;
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_a_3336_);
lean_dec(v___x_3259_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v___x_3341_; 
if (v_isShared_3339_ == 0)
{
v___x_3341_ = v___x_3338_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v_a_3336_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
}
}
v___jp_3344_:
{
lean_object* v___x_3366_; 
v___x_3366_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_3349_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_a_3367_; uint8_t v_ring_3368_; 
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
lean_inc(v_a_3367_);
lean_dec_ref_known(v___x_3366_, 1);
v_ring_3368_ = lean_ctor_get_uint8(v_a_3367_, sizeof(void*)*14 + 21);
lean_dec(v_a_3367_);
if (v_ring_3368_ == 0)
{
lean_dec_ref(v___f_2696_);
v___y_3237_ = v___y_3345_;
v___y_3238_ = v___y_3346_;
v___y_3239_ = v___y_3347_;
v___y_3240_ = v___y_3348_;
v___y_3241_ = v___y_3365_;
v___y_3242_ = v___y_3350_;
v___y_3243_ = v___y_3349_;
v___y_3244_ = v___y_3351_;
v___y_3245_ = v___y_3352_;
v___y_3246_ = v___y_3354_;
v___y_3247_ = v___y_3355_;
v___y_3248_ = v___y_3356_;
v___y_3249_ = v___y_3357_;
v___y_3250_ = v___y_3358_;
v___y_3251_ = v___y_3359_;
v___y_3252_ = v___y_3360_;
v___y_3253_ = v___y_3362_;
v___y_3254_ = v___y_3361_;
v___y_3255_ = v___y_3363_;
v___y_3256_ = v___y_3364_;
v___y_3257_ = v_ring_3368_;
goto v___jp_3236_;
}
else
{
lean_object* v___x_3369_; uint8_t v___x_3370_; 
v___x_3369_ = lean_box(0);
v___x_3370_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2(v_a_2707_, v___x_3369_);
if (v___x_3370_ == 0)
{
lean_dec_ref(v___f_2696_);
v___y_3237_ = v___y_3345_;
v___y_3238_ = v___y_3346_;
v___y_3239_ = v___y_3347_;
v___y_3240_ = v___y_3348_;
v___y_3241_ = v___y_3365_;
v___y_3242_ = v___y_3350_;
v___y_3243_ = v___y_3349_;
v___y_3244_ = v___y_3351_;
v___y_3245_ = v___y_3352_;
v___y_3246_ = v___y_3354_;
v___y_3247_ = v___y_3355_;
v___y_3248_ = v___y_3356_;
v___y_3249_ = v___y_3357_;
v___y_3250_ = v___y_3358_;
v___y_3251_ = v___y_3359_;
v___y_3252_ = v___y_3360_;
v___y_3253_ = v___y_3362_;
v___y_3254_ = v___y_3361_;
v___y_3255_ = v___y_3363_;
v___y_3256_ = v___y_3364_;
v___y_3257_ = v___x_3370_;
goto v___jp_3236_;
}
else
{
if (lean_obj_tag(v___y_3365_) == 0)
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
lean_dec_ref(v___y_3364_);
lean_dec_ref(v___y_3362_);
lean_dec(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3354_);
lean_dec(v___y_3352_);
lean_dec(v___y_3348_);
lean_dec(v___y_3346_);
lean_dec(v_a_3235_);
lean_dec(v_a_3233_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v___x_3371_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3372_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3371_, v___f_2696_, v___y_3345_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3380_; 
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3380_ == 0)
{
lean_object* v_unused_3381_; 
v_unused_3381_ = lean_ctor_get(v___x_3372_, 0);
lean_dec(v_unused_3381_);
v___x_3374_ = v___x_3372_;
v_isShared_3375_ = v_isSharedCheck_3380_;
goto v_resetjp_3373_;
}
else
{
lean_dec(v___x_3372_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3380_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3376_; lean_object* v___x_3378_; 
v___x_3376_ = lean_box(0);
if (v_isShared_3375_ == 0)
{
lean_ctor_set(v___x_3374_, 0, v___x_3376_);
v___x_3378_ = v___x_3374_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v___x_3376_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
else
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3389_; 
v_a_3382_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3384_ = v___x_3372_;
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3372_);
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
lean_dec_ref(v___f_2696_);
v___y_3237_ = v___y_3345_;
v___y_3238_ = v___y_3346_;
v___y_3239_ = v___y_3347_;
v___y_3240_ = v___y_3348_;
v___y_3241_ = v___y_3365_;
v___y_3242_ = v___y_3350_;
v___y_3243_ = v___y_3349_;
v___y_3244_ = v___y_3351_;
v___y_3245_ = v___y_3352_;
v___y_3246_ = v___y_3354_;
v___y_3247_ = v___y_3355_;
v___y_3248_ = v___y_3356_;
v___y_3249_ = v___y_3357_;
v___y_3250_ = v___y_3358_;
v___y_3251_ = v___y_3359_;
v___y_3252_ = v___y_3360_;
v___y_3253_ = v___y_3362_;
v___y_3254_ = v___y_3361_;
v___y_3255_ = v___y_3363_;
v___y_3256_ = v___y_3364_;
v___y_3257_ = v___y_3353_;
goto v___jp_3236_;
}
}
}
}
else
{
lean_object* v_a_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3397_; 
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
lean_dec_ref(v___y_3362_);
lean_dec(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3354_);
lean_dec(v___y_3352_);
lean_dec(v___y_3348_);
lean_dec(v___y_3346_);
lean_dec(v_a_3235_);
lean_dec(v_a_3233_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v___f_2696_);
lean_dec_ref(v_type_2618_);
v_a_3390_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3392_ = v___x_3366_;
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_a_3390_);
lean_dec(v___x_3366_);
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
lean_object* v___x_3419_; 
v___x_3419_ = lean_box(0);
v___y_3345_ = v___y_3399_;
v___y_3346_ = v___y_3400_;
v___y_3347_ = v___y_3401_;
v___y_3348_ = v___y_3402_;
v___y_3349_ = v___y_3403_;
v___y_3350_ = v___y_3404_;
v___y_3351_ = v___y_3405_;
v___y_3352_ = v___y_3406_;
v___y_3353_ = v___y_3407_;
v___y_3354_ = v___y_3408_;
v___y_3355_ = v___y_3409_;
v___y_3356_ = v___y_3410_;
v___y_3357_ = v___y_3411_;
v___y_3358_ = v___y_3412_;
v___y_3359_ = v___y_3413_;
v___y_3360_ = v___y_3414_;
v___y_3361_ = v___y_3416_;
v___y_3362_ = v___y_3415_;
v___y_3363_ = v___y_3417_;
v___y_3364_ = v___y_3418_;
v___y_3365_ = v___x_3419_;
goto v___jp_3344_;
}
v___jp_3420_:
{
lean_object* v___x_3440_; 
v___x_3440_ = lean_box(0);
v___y_3399_ = v___y_3430_;
v___y_3400_ = v___y_3423_;
v___y_3401_ = v___y_3435_;
v___y_3402_ = v___x_3440_;
v___y_3403_ = v___y_3432_;
v___y_3404_ = v___y_3433_;
v___y_3405_ = v___y_3439_;
v___y_3406_ = v___y_3428_;
v___y_3407_ = v___y_3421_;
v___y_3408_ = v___y_3422_;
v___y_3409_ = v___y_3436_;
v___y_3410_ = v___y_3437_;
v___y_3411_ = v___y_3438_;
v___y_3412_ = v___y_3431_;
v___y_3413_ = v___y_3424_;
v___y_3414_ = v___y_3425_;
v___y_3415_ = v___y_3427_;
v___y_3416_ = v___y_3426_;
v___y_3417_ = v___y_3434_;
v___y_3418_ = v___y_3429_;
goto v___jp_3398_;
}
}
else
{
lean_object* v_a_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3567_; 
lean_dec(v_a_3233_);
lean_dec(v_a_3231_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v___f_2696_);
lean_dec_ref(v_type_2618_);
v_a_3560_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3567_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3562_ = v___x_3234_;
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_a_3560_);
lean_dec(v___x_3234_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3565_; 
if (v_isShared_3563_ == 0)
{
v___x_3565_ = v___x_3562_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_a_3560_);
v___x_3565_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
return v___x_3565_;
}
}
}
}
else
{
lean_object* v_a_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3575_; 
lean_dec(v_a_3231_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v___f_2696_);
lean_dec_ref(v_type_2618_);
v_a_3568_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3570_ = v___x_3232_;
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_a_3568_);
lean_dec(v___x_3232_);
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
lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3583_; 
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v___f_2696_);
lean_dec_ref(v_type_2618_);
v_a_3576_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3578_ = v___x_3230_;
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___x_3230_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3581_; 
if (v_isShared_3579_ == 0)
{
v___x_3581_ = v___x_3578_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_a_3576_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
}
v___jp_2719_:
{
lean_object* v___x_2755_; 
v___x_2755_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v___y_2745_, v___y_2753_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; lean_object* v_structs_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; size_t v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___f_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc(v_a_2756_);
lean_dec_ref_known(v___x_2755_, 1);
v_structs_2757_ = lean_ctor_get(v_a_2756_, 0);
lean_inc_ref(v_structs_2757_);
lean_dec(v_a_2756_);
v___x_2758_ = lean_array_get_size(v_structs_2757_);
lean_dec_ref(v_structs_2757_);
v___x_2759_ = lean_unsigned_to_nat(32u);
v___x_2760_ = lean_mk_empty_array_with_capacity(v___x_2759_);
v___x_2761_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4);
v___x_2762_ = ((size_t)5ULL);
lean_inc(v___y_2725_);
v___x_2763_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2763_, 0, v___x_2761_);
lean_ctor_set(v___x_2763_, 1, v___x_2760_);
lean_ctor_set(v___x_2763_, 2, v___y_2725_);
lean_ctor_set(v___x_2763_, 3, v___y_2725_);
lean_ctor_set_usize(v___x_2763_, 4, v___x_2762_);
v___x_2764_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6);
v___x_2765_ = lean_box(0);
v___x_2766_ = lean_box(0);
lean_inc_ref_n(v___x_2763_, 7);
lean_inc(v___y_2736_);
lean_inc(v___y_2743_);
lean_inc(v___y_2722_);
lean_inc(v___y_2735_);
lean_inc(v___y_2739_);
v___x_2767_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v___x_2767_, 0, v___x_2758_);
lean_ctor_set(v___x_2767_, 1, v_a_2707_);
lean_ctor_set(v___x_2767_, 2, v_type_2618_);
lean_ctor_set(v___x_2767_, 3, v_val_2702_);
lean_ctor_set(v___x_2767_, 4, v___y_2738_);
lean_ctor_set(v___x_2767_, 5, v_a_2713_);
lean_ctor_set(v___x_2767_, 6, v_a_2716_);
lean_ctor_set(v___x_2767_, 7, v_a_2718_);
lean_ctor_set(v___x_2767_, 8, v___y_2726_);
lean_ctor_set(v___x_2767_, 9, v___y_2727_);
lean_ctor_set(v___x_2767_, 10, v___y_2728_);
lean_ctor_set(v___x_2767_, 11, v___y_2724_);
lean_ctor_set(v___x_2767_, 12, v___y_2739_);
lean_ctor_set(v___x_2767_, 13, v___y_2737_);
lean_ctor_set(v___x_2767_, 14, v___y_2735_);
lean_ctor_set(v___x_2767_, 15, v___y_2722_);
lean_ctor_set(v___x_2767_, 16, v___y_2743_);
lean_ctor_set(v___x_2767_, 17, v___y_2734_);
lean_ctor_set(v___x_2767_, 18, v___y_2723_);
lean_ctor_set(v___x_2767_, 19, v___y_2736_);
lean_ctor_set(v___x_2767_, 20, v___y_2741_);
lean_ctor_set(v___x_2767_, 21, v___y_2740_);
lean_ctor_set(v___x_2767_, 22, v___y_2733_);
lean_ctor_set(v___x_2767_, 23, v___y_2721_);
lean_ctor_set(v___x_2767_, 24, v___y_2732_);
lean_ctor_set(v___x_2767_, 25, v___y_2731_);
lean_ctor_set(v___x_2767_, 26, v___y_2742_);
lean_ctor_set(v___x_2767_, 27, v_homomulFn_x3f_2744_);
lean_ctor_set(v___x_2767_, 28, v___y_2720_);
lean_ctor_set(v___x_2767_, 29, v___y_2729_);
lean_ctor_set(v___x_2767_, 30, v___x_2763_);
lean_ctor_set(v___x_2767_, 31, v___x_2764_);
lean_ctor_set(v___x_2767_, 32, v___x_2763_);
lean_ctor_set(v___x_2767_, 33, v___x_2763_);
lean_ctor_set(v___x_2767_, 34, v___x_2763_);
lean_ctor_set(v___x_2767_, 35, v___x_2763_);
lean_ctor_set(v___x_2767_, 36, v___x_2765_);
lean_ctor_set(v___x_2767_, 37, v___x_2764_);
lean_ctor_set(v___x_2767_, 38, v___x_2763_);
lean_ctor_set(v___x_2767_, 39, v___x_2766_);
lean_ctor_set(v___x_2767_, 40, v___x_2763_);
lean_ctor_set(v___x_2767_, 41, v___x_2763_);
lean_ctor_set_uint8(v___x_2767_, sizeof(void*)*42, v___y_2730_);
v___f_2768_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1), 2, 1);
lean_closure_set(v___f_2768_, 0, v___x_2767_);
v___x_2769_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2770_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2769_, v___f_2768_, v___y_2745_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_dec_ref_known(v___x_2770_, 1);
if (lean_obj_tag(v___y_2736_) == 1)
{
if (lean_obj_tag(v___y_2739_) == 0)
{
lean_dec_ref_known(v___y_2736_, 1);
lean_dec(v___y_2743_);
lean_dec(v___y_2735_);
lean_dec(v___y_2722_);
v___y_2631_ = v___x_2758_;
goto v___jp_2630_;
}
else
{
lean_dec_ref_known(v___y_2739_, 1);
if (lean_obj_tag(v___y_2735_) == 0)
{
if (v___y_2730_ == 0)
{
if (lean_obj_tag(v___y_2722_) == 0)
{
lean_object* v_val_2771_; uint8_t v___x_2772_; 
v_val_2771_ = lean_ctor_get(v___y_2736_, 0);
lean_inc(v_val_2771_);
lean_dec_ref_known(v___y_2736_, 1);
v___x_2772_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(v___y_2743_);
lean_dec(v___y_2743_);
if (v___x_2772_ == 0)
{
lean_dec(v_val_2771_);
v___y_2631_ = v___x_2758_;
goto v___jp_2630_;
}
else
{
v___y_2672_ = v___y_2747_;
v___y_2673_ = v___y_2748_;
v___y_2674_ = v___y_2751_;
v___y_2675_ = v___y_2745_;
v___y_2676_ = v___y_2730_;
v___y_2677_ = v___y_2750_;
v___y_2678_ = v___y_2754_;
v___y_2679_ = v___y_2749_;
v___y_2680_ = v___y_2753_;
v___y_2681_ = v___y_2746_;
v___y_2682_ = v_val_2771_;
v___y_2683_ = v___x_2758_;
v___y_2684_ = v___y_2752_;
goto v___jp_2671_;
}
}
else
{
lean_object* v_val_2773_; 
lean_dec_ref_known(v___y_2722_, 1);
lean_dec(v___y_2743_);
v_val_2773_ = lean_ctor_get(v___y_2736_, 0);
lean_inc(v_val_2773_);
lean_dec_ref_known(v___y_2736_, 1);
v___y_2672_ = v___y_2747_;
v___y_2673_ = v___y_2748_;
v___y_2674_ = v___y_2751_;
v___y_2675_ = v___y_2745_;
v___y_2676_ = v___y_2730_;
v___y_2677_ = v___y_2750_;
v___y_2678_ = v___y_2754_;
v___y_2679_ = v___y_2749_;
v___y_2680_ = v___y_2753_;
v___y_2681_ = v___y_2746_;
v___y_2682_ = v_val_2773_;
v___y_2683_ = v___x_2758_;
v___y_2684_ = v___y_2752_;
goto v___jp_2671_;
}
}
else
{
lean_object* v_val_2774_; 
lean_dec(v___y_2743_);
lean_dec(v___y_2722_);
v_val_2774_ = lean_ctor_get(v___y_2736_, 0);
lean_inc(v_val_2774_);
lean_dec_ref_known(v___y_2736_, 1);
v___y_2646_ = v___y_2747_;
v___y_2647_ = v___y_2748_;
v___y_2648_ = v___y_2751_;
v___y_2649_ = v___y_2745_;
v___y_2650_ = v___y_2730_;
v___y_2651_ = v___y_2750_;
v___y_2652_ = v___y_2754_;
v___y_2653_ = v___y_2749_;
v___y_2654_ = v___y_2753_;
v___y_2655_ = v___y_2746_;
v___y_2656_ = v_val_2774_;
v___y_2657_ = v___x_2758_;
v___y_2658_ = v___y_2752_;
goto v___jp_2645_;
}
}
else
{
lean_object* v_val_2775_; 
lean_dec_ref_known(v___y_2735_, 1);
lean_dec(v___y_2743_);
lean_dec(v___y_2722_);
v_val_2775_ = lean_ctor_get(v___y_2736_, 0);
lean_inc(v_val_2775_);
lean_dec_ref_known(v___y_2736_, 1);
v___y_2646_ = v___y_2747_;
v___y_2647_ = v___y_2748_;
v___y_2648_ = v___y_2751_;
v___y_2649_ = v___y_2745_;
v___y_2650_ = v___y_2730_;
v___y_2651_ = v___y_2750_;
v___y_2652_ = v___y_2754_;
v___y_2653_ = v___y_2749_;
v___y_2654_ = v___y_2753_;
v___y_2655_ = v___y_2746_;
v___y_2656_ = v_val_2775_;
v___y_2657_ = v___x_2758_;
v___y_2658_ = v___y_2752_;
goto v___jp_2645_;
}
}
}
else
{
lean_dec(v___y_2743_);
lean_dec(v___y_2739_);
lean_dec(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec(v___y_2722_);
v___y_2631_ = v___x_2758_;
goto v___jp_2630_;
}
}
else
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2783_; 
lean_dec(v___y_2743_);
lean_dec(v___y_2739_);
lean_dec(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec(v___y_2722_);
v_a_2776_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2778_ = v___x_2770_;
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2770_);
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
lean_dec(v_homomulFn_x3f_2744_);
lean_dec(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_dec(v_a_2707_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_2784_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2755_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2755_);
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
v___jp_2792_:
{
lean_object* v___x_2827_; 
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
v___x_2827_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(v_val_2702_, v_type_2618_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; lean_object* v___x_2829_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2828_);
lean_dec_ref_known(v___x_2827_, 1);
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
v___x_2829_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(v_val_2702_, v_type_2618_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
if (lean_obj_tag(v___x_2829_) == 0)
{
if (lean_obj_tag(v___y_2810_) == 0)
{
lean_object* v_a_2830_; 
lean_dec(v___y_2805_);
lean_del_object(v___x_2704_);
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2830_);
lean_dec_ref_known(v___x_2829_, 1);
v___y_2720_ = v___y_2793_;
v___y_2721_ = v___y_2794_;
v___y_2722_ = v___y_2795_;
v___y_2723_ = v___y_2796_;
v___y_2724_ = v___y_2797_;
v___y_2725_ = v___y_2798_;
v___y_2726_ = v___y_2799_;
v___y_2727_ = v___y_2800_;
v___y_2728_ = v___y_2801_;
v___y_2729_ = v___y_2802_;
v___y_2730_ = v___y_2803_;
v___y_2731_ = v_a_2828_;
v___y_2732_ = v___y_2804_;
v___y_2733_ = v___y_2806_;
v___y_2734_ = v___y_2807_;
v___y_2735_ = v___y_2808_;
v___y_2736_ = v___y_2809_;
v___y_2737_ = v___y_2810_;
v___y_2738_ = v___y_2812_;
v___y_2739_ = v___y_2811_;
v___y_2740_ = v_ltFn_x3f_2816_;
v___y_2741_ = v___y_2814_;
v___y_2742_ = v_a_2830_;
v___y_2743_ = v___y_2815_;
v_homomulFn_x3f_2744_ = v___y_2813_;
v___y_2745_ = v___y_2817_;
v___y_2746_ = v___y_2818_;
v___y_2747_ = v___y_2819_;
v___y_2748_ = v___y_2820_;
v___y_2749_ = v___y_2821_;
v___y_2750_ = v___y_2822_;
v___y_2751_ = v___y_2823_;
v___y_2752_ = v___y_2824_;
v___y_2753_ = v___y_2825_;
v___y_2754_ = v___y_2826_;
goto v___jp_2719_;
}
else
{
lean_object* v_a_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
lean_dec(v___y_2813_);
v_a_2831_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2831_);
lean_dec_ref_known(v___x_2829_, 1);
v___x_2832_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__8));
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
v___x_2833_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_2832_, v_val_2702_, v_type_2618_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_a_2834_);
lean_dec_ref_known(v___x_2833_, 1);
v___x_2835_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__10));
v___x_2836_ = l_Lean_mkConst(v___x_2835_, v___y_2805_);
lean_inc_ref_n(v_type_2618_, 3);
v___x_2837_ = l_Lean_mkApp4(v___x_2836_, v_type_2618_, v_type_2618_, v_type_2618_, v_a_2834_);
v___x_2838_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2837_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2841_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_a_2839_);
lean_dec_ref_known(v___x_2838_, 1);
if (v_isShared_2705_ == 0)
{
lean_ctor_set(v___x_2704_, 0, v_a_2839_);
v___x_2841_ = v___x_2704_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_a_2839_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
v___y_2720_ = v___y_2793_;
v___y_2721_ = v___y_2794_;
v___y_2722_ = v___y_2795_;
v___y_2723_ = v___y_2796_;
v___y_2724_ = v___y_2797_;
v___y_2725_ = v___y_2798_;
v___y_2726_ = v___y_2799_;
v___y_2727_ = v___y_2800_;
v___y_2728_ = v___y_2801_;
v___y_2729_ = v___y_2802_;
v___y_2730_ = v___y_2803_;
v___y_2731_ = v_a_2828_;
v___y_2732_ = v___y_2804_;
v___y_2733_ = v___y_2806_;
v___y_2734_ = v___y_2807_;
v___y_2735_ = v___y_2808_;
v___y_2736_ = v___y_2809_;
v___y_2737_ = v___y_2810_;
v___y_2738_ = v___y_2812_;
v___y_2739_ = v___y_2811_;
v___y_2740_ = v_ltFn_x3f_2816_;
v___y_2741_ = v___y_2814_;
v___y_2742_ = v_a_2831_;
v___y_2743_ = v___y_2815_;
v_homomulFn_x3f_2744_ = v___x_2841_;
v___y_2745_ = v___y_2817_;
v___y_2746_ = v___y_2818_;
v___y_2747_ = v___y_2819_;
v___y_2748_ = v___y_2820_;
v___y_2749_ = v___y_2821_;
v___y_2750_ = v___y_2822_;
v___y_2751_ = v___y_2823_;
v___y_2752_ = v___y_2824_;
v___y_2753_ = v___y_2825_;
v___y_2754_ = v___y_2826_;
goto v___jp_2719_;
}
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
lean_dec_ref_known(v___y_2810_, 1);
lean_dec(v_a_2831_);
lean_dec(v_a_2828_);
lean_dec(v_ltFn_x3f_2816_);
lean_dec(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec(v___y_2809_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec_ref(v___y_2804_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_2843_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2838_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2838_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
lean_dec(v_a_2831_);
lean_dec_ref_known(v___y_2810_, 1);
lean_dec(v_a_2828_);
lean_dec(v_ltFn_x3f_2816_);
lean_dec(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec(v___y_2809_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_2851_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2853_ = v___x_2833_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2833_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_a_2851_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
}
else
{
lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2866_; 
lean_dec(v_a_2828_);
lean_dec(v_ltFn_x3f_2816_);
lean_dec(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec(v___y_2810_);
lean_dec(v___y_2809_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_2859_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2861_ = v___x_2829_;
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_a_2859_);
lean_dec(v___x_2829_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2864_; 
if (v_isShared_2862_ == 0)
{
v___x_2864_ = v___x_2861_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_a_2859_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
}
else
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2874_; 
lean_dec(v_ltFn_x3f_2816_);
lean_dec(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec(v___y_2810_);
lean_dec(v___y_2809_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_2867_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2869_ = v___x_2827_;
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2827_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
if (v_isShared_2870_ == 0)
{
v___x_2872_ = v___x_2869_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_a_2867_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
}
v___jp_2875_:
{
if (lean_obj_tag(v_a_2716_) == 1)
{
lean_object* v_val_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v_val_2910_ = lean_ctor_get(v_a_2716_, 0);
v___x_2911_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__12));
v___x_2912_ = l_Lean_mkConst(v___x_2911_, v___y_2880_);
lean_inc(v_val_2910_);
lean_inc_ref(v_type_2618_);
v___x_2913_ = l_Lean_mkAppB(v___x_2912_, v_type_2618_, v_val_2910_);
v___x_2914_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2913_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; lean_object* v___x_2917_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
lean_dec_ref_known(v___x_2914_, 1);
if (v_isShared_2710_ == 0)
{
lean_ctor_set_tag(v___x_2709_, 1);
lean_ctor_set(v___x_2709_, 0, v_a_2915_);
v___x_2917_ = v___x_2709_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2915_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
v___y_2793_ = v___y_2876_;
v___y_2794_ = v___y_2877_;
v___y_2795_ = v___y_2878_;
v___y_2796_ = v___y_2879_;
v___y_2797_ = v___y_2881_;
v___y_2798_ = v___y_2882_;
v___y_2799_ = v___y_2883_;
v___y_2800_ = v___y_2884_;
v___y_2801_ = v___y_2885_;
v___y_2802_ = v___y_2886_;
v___y_2803_ = v___y_2887_;
v___y_2804_ = v___y_2888_;
v___y_2805_ = v___y_2889_;
v___y_2806_ = v___y_2890_;
v___y_2807_ = v___y_2891_;
v___y_2808_ = v___y_2892_;
v___y_2809_ = v___y_2893_;
v___y_2810_ = v___y_2894_;
v___y_2811_ = v___y_2896_;
v___y_2812_ = v___y_2895_;
v___y_2813_ = v___y_2897_;
v___y_2814_ = v_leFn_x3f_2899_;
v___y_2815_ = v___y_2898_;
v_ltFn_x3f_2816_ = v___x_2917_;
v___y_2817_ = v___y_2900_;
v___y_2818_ = v___y_2901_;
v___y_2819_ = v___y_2902_;
v___y_2820_ = v___y_2903_;
v___y_2821_ = v___y_2904_;
v___y_2822_ = v___y_2905_;
v___y_2823_ = v___y_2906_;
v___y_2824_ = v___y_2907_;
v___y_2825_ = v___y_2908_;
v___y_2826_ = v___y_2909_;
goto v___jp_2792_;
}
}
else
{
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2926_; 
lean_dec_ref_known(v_a_2716_, 1);
lean_dec(v_leFn_x3f_2899_);
lean_dec(v___y_2898_);
lean_dec(v___y_2897_);
lean_dec(v___y_2896_);
lean_dec_ref(v___y_2895_);
lean_dec(v___y_2894_);
lean_dec(v___y_2893_);
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec_ref(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v_a_2718_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_2919_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2921_ = v___x_2914_;
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2914_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2924_; 
if (v_isShared_2922_ == 0)
{
v___x_2924_ = v___x_2921_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2919_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
}
else
{
lean_dec(v___y_2880_);
lean_del_object(v___x_2709_);
lean_inc(v___y_2897_);
v___y_2793_ = v___y_2876_;
v___y_2794_ = v___y_2877_;
v___y_2795_ = v___y_2878_;
v___y_2796_ = v___y_2879_;
v___y_2797_ = v___y_2881_;
v___y_2798_ = v___y_2882_;
v___y_2799_ = v___y_2883_;
v___y_2800_ = v___y_2884_;
v___y_2801_ = v___y_2885_;
v___y_2802_ = v___y_2886_;
v___y_2803_ = v___y_2887_;
v___y_2804_ = v___y_2888_;
v___y_2805_ = v___y_2889_;
v___y_2806_ = v___y_2890_;
v___y_2807_ = v___y_2891_;
v___y_2808_ = v___y_2892_;
v___y_2809_ = v___y_2893_;
v___y_2810_ = v___y_2894_;
v___y_2811_ = v___y_2896_;
v___y_2812_ = v___y_2895_;
v___y_2813_ = v___y_2897_;
v___y_2814_ = v_leFn_x3f_2899_;
v___y_2815_ = v___y_2898_;
v_ltFn_x3f_2816_ = v___y_2897_;
v___y_2817_ = v___y_2900_;
v___y_2818_ = v___y_2901_;
v___y_2819_ = v___y_2902_;
v___y_2820_ = v___y_2903_;
v___y_2821_ = v___y_2904_;
v___y_2822_ = v___y_2905_;
v___y_2823_ = v___y_2906_;
v___y_2824_ = v___y_2907_;
v___y_2825_ = v___y_2908_;
v___y_2826_ = v___y_2909_;
goto v___jp_2792_;
}
}
v___jp_2927_:
{
lean_object* v___x_2960_; 
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
v___x_2960_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_val_2702_, v_type_2618_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2961_);
lean_dec_ref_known(v___x_2960_, 1);
v___x_2962_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__14));
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
v___x_2963_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v___x_2962_, v_val_2702_, v_type_2618_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc_n(v_a_2964_, 2);
lean_dec_ref_known(v___x_2963_, 1);
v___x_2965_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__16));
lean_inc(v___y_2930_);
v___x_2966_ = l_Lean_mkConst(v___x_2965_, v___y_2930_);
lean_inc_ref(v_type_2618_);
v___x_2967_ = l_Lean_mkAppB(v___x_2966_, v_type_2618_, v_a_2964_);
v___x_2968_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_2967_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_a_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
lean_inc(v_a_2969_);
lean_dec_ref_known(v___x_2968_, 1);
v___x_2970_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__18));
lean_inc(v___y_2930_);
v___x_2971_ = l_Lean_mkConst(v___x_2970_, v___y_2930_);
v___x_2972_ = lean_unsigned_to_nat(0u);
v___x_2973_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19);
lean_inc_ref(v_type_2618_);
v___x_2974_ = l_Lean_mkAppB(v___x_2971_, v_type_2618_, v___x_2973_);
v___x_2975_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2974_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_2975_) == 0)
{
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_3197_; 
v_a_2976_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_2978_ = v___x_2975_;
v_isShared_2979_ = v_isSharedCheck_3197_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2975_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_3197_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
if (lean_obj_tag(v_a_2976_) == 1)
{
lean_object* v_val_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_3192_; 
lean_del_object(v___x_2978_);
v_val_2980_ = lean_ctor_get(v_a_2976_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v_a_2976_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_2982_ = v_a_2976_;
v_isShared_2983_ = v_isSharedCheck_3192_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_val_2980_);
lean_dec(v_a_2976_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_3192_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2984_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__21));
lean_inc(v___y_2930_);
v___x_2985_ = l_Lean_mkConst(v___x_2984_, v___y_2930_);
lean_inc_ref(v_type_2618_);
v___x_2986_ = l_Lean_mkApp3(v___x_2985_, v_type_2618_, v___x_2973_, v_val_2980_);
v___x_2987_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2986_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v_a_2988_; lean_object* v___x_2989_; 
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
lean_inc_n(v_a_2988_, 2);
lean_dec_ref_known(v___x_2987_, 1);
lean_inc(v_a_2969_);
v___x_2989_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_a_2969_, v_a_2988_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v___x_2990_; lean_object* v___x_2991_; 
lean_dec_ref_known(v___x_2989_, 1);
v___x_2990_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__23));
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
v___x_2991_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_2990_, v_val_2702_, v_type_2618_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
lean_inc_n(v_a_2992_, 2);
lean_dec_ref_known(v___x_2991_, 1);
v___x_2993_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__25));
lean_inc(v___y_2939_);
v___x_2994_ = l_Lean_mkConst(v___x_2993_, v___y_2939_);
lean_inc_ref_n(v_type_2618_, 3);
v___x_2995_ = l_Lean_mkApp4(v___x_2994_, v_type_2618_, v_type_2618_, v_type_2618_, v_a_2992_);
v___x_2996_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2995_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_object* v_a_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_a_2997_);
lean_dec_ref_known(v___x_2996_, 1);
v___x_2998_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__27));
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
v___x_2999_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v___x_2998_, v_val_2702_, v_type_2618_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc_n(v_a_3000_, 2);
lean_dec_ref_known(v___x_2999_, 1);
v___x_3001_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__29));
lean_inc(v___y_2930_);
v___x_3002_ = l_Lean_mkConst(v___x_3001_, v___y_2930_);
lean_inc_ref(v_type_2618_);
v___x_3003_ = l_Lean_mkAppB(v___x_3002_, v_type_2618_, v_a_3000_);
v___x_3004_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3003_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v___x_3006_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
lean_dec_ref_known(v___x_3004_, 1);
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
v___x_3006_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(v_val_2702_, v_type_2618_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc_n(v_a_3007_, 2);
lean_dec_ref_known(v___x_3006_, 1);
v___x_3008_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_3009_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_3010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3009_);
lean_ctor_set(v___x_3010_, 1, v___y_2945_);
v___x_3011_ = l_Lean_mkConst(v___x_3008_, v___x_3010_);
v___x_3012_ = l_Lean_Int_mkType;
lean_inc_ref_n(v_type_2618_, 2);
lean_inc_ref(v___x_3011_);
v___x_3013_ = l_Lean_mkApp4(v___x_3011_, v___x_3012_, v_type_2618_, v_type_2618_, v_a_3007_);
v___x_3014_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3013_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; lean_object* v___x_3016_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_a_3015_);
lean_dec_ref_known(v___x_3014_, 1);
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
v___x_3016_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_val_2702_, v_type_2618_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc_n(v_a_3017_, 2);
lean_dec_ref_known(v___x_3016_, 1);
v___x_3018_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2618_, 2);
v___x_3019_ = l_Lean_mkApp4(v___x_3011_, v___x_3018_, v_type_2618_, v_type_2618_, v_a_3017_);
v___x_3020_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3019_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc(v_a_3021_);
lean_dec_ref_known(v___x_3020_, 1);
v___x_3022_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__30));
v___x_3023_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__31));
lean_inc_ref(v___y_2937_);
lean_inc_ref(v___y_2944_);
v___x_3024_ = l_Lean_Name_mkStr4(v___y_2944_, v___y_2937_, v___x_3022_, v___x_3023_);
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
lean_inc_ref(v___y_2928_);
v___x_3025_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_a_2964_, v___y_2928_, v___x_3024_, v_val_2702_, v_type_2618_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
lean_dec_ref_known(v___x_3025_, 1);
v___x_3026_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__32));
lean_inc_ref(v___y_2937_);
lean_inc_ref(v___y_2944_);
v___x_3027_ = l_Lean_Name_mkStr4(v___y_2944_, v___y_2937_, v___x_3022_, v___x_3026_);
v___x_3028_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__34));
v___x_3029_ = lean_box(0);
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
v___x_3030_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v___y_2948_, v___y_2928_, v___x_3027_, v___x_3028_, v_val_2702_, v_type_2618_, v___x_3029_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
lean_dec_ref_known(v___x_3030_, 1);
v___x_3031_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__35));
lean_inc_ref(v___y_2931_);
lean_inc_ref(v___y_2937_);
lean_inc_ref(v___y_2944_);
v___x_3032_ = l_Lean_Name_mkStr4(v___y_2944_, v___y_2937_, v___y_2931_, v___x_3031_);
v___x_3033_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__37));
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
lean_inc_ref(v___y_2936_);
v___x_3034_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_2992_, v___y_2936_, v___x_3032_, v___x_3033_, v_val_2702_, v_type_2618_, v___x_3029_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
lean_dec_ref_known(v___x_3034_, 1);
v___x_3035_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__38));
lean_inc_ref(v___y_2931_);
lean_inc_ref(v___y_2937_);
lean_inc_ref(v___y_2944_);
v___x_3036_ = l_Lean_Name_mkStr4(v___y_2944_, v___y_2937_, v___y_2931_, v___x_3035_);
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
v___x_3037_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_a_3000_, v___y_2936_, v___x_3036_, v_val_2702_, v_type_2618_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
lean_dec_ref_known(v___x_3037_, 1);
v___x_3038_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__39));
lean_inc_ref(v___y_2935_);
lean_inc_ref(v___y_2937_);
lean_inc_ref(v___y_2944_);
v___x_3039_ = l_Lean_Name_mkStr4(v___y_2944_, v___y_2937_, v___y_2935_, v___x_3038_);
v___x_3040_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__41));
v___x_3041_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42);
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
lean_inc_ref(v___y_2947_);
v___x_3042_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_3007_, v___y_2947_, v___x_3039_, v___x_3040_, v_val_2702_, v_type_2618_, v___x_3041_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
lean_dec_ref_known(v___x_3042_, 1);
v___x_3043_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__43));
lean_inc_ref(v___y_2935_);
lean_inc_ref(v___y_2937_);
lean_inc_ref(v___y_2944_);
v___x_3044_ = l_Lean_Name_mkStr4(v___y_2944_, v___y_2937_, v___y_2935_, v___x_3043_);
v___x_3045_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44);
lean_inc_ref(v_type_2618_);
lean_inc(v_val_2702_);
lean_inc_ref(v___y_2947_);
v___x_3046_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_3017_, v___y_2947_, v___x_3044_, v___x_3040_, v_val_2702_, v_type_2618_, v___x_3045_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_dec_ref_known(v___x_3046_, 1);
if (lean_obj_tag(v_a_2713_) == 1)
{
lean_object* v_val_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v_val_3047_ = lean_ctor_get(v_a_2713_, 0);
v___x_3048_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__46));
lean_inc(v___y_2930_);
v___x_3049_ = l_Lean_mkConst(v___x_3048_, v___y_2930_);
lean_inc(v_val_3047_);
lean_inc_ref(v_type_2618_);
v___x_3050_ = l_Lean_mkAppB(v___x_3049_, v_type_2618_, v_val_3047_);
v___x_3051_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3050_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_object* v_a_3052_; lean_object* v___x_3054_; 
v_a_3052_ = lean_ctor_get(v___x_3051_, 0);
lean_inc(v_a_3052_);
lean_dec_ref_known(v___x_3051_, 1);
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 0, v_a_3052_);
v___x_3054_ = v___x_2982_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3052_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
v___y_2876_ = v_a_2997_;
v___y_2877_ = v_a_3015_;
v___y_2878_ = v___y_2929_;
v___y_2879_ = v_a_2988_;
v___y_2880_ = v___y_2930_;
v___y_2881_ = v_a_2961_;
v___y_2882_ = v___x_2972_;
v___y_2883_ = v___y_2932_;
v___y_2884_ = v___y_2933_;
v___y_2885_ = v___y_2934_;
v___y_2886_ = v_a_3005_;
v___y_2887_ = v___y_2938_;
v___y_2888_ = v_a_3021_;
v___y_2889_ = v___y_2939_;
v___y_2890_ = v___y_2940_;
v___y_2891_ = v_a_2969_;
v___y_2892_ = v___y_2941_;
v___y_2893_ = v___y_2942_;
v___y_2894_ = v___y_2943_;
v___y_2895_ = v___y_2947_;
v___y_2896_ = v___y_2946_;
v___y_2897_ = v___x_3029_;
v___y_2898_ = v_charInst_x3f_2949_;
v_leFn_x3f_2899_ = v___x_3054_;
v___y_2900_ = v___y_2950_;
v___y_2901_ = v___y_2951_;
v___y_2902_ = v___y_2952_;
v___y_2903_ = v___y_2953_;
v___y_2904_ = v___y_2954_;
v___y_2905_ = v___y_2955_;
v___y_2906_ = v___y_2956_;
v___y_2907_ = v___y_2957_;
v___y_2908_ = v___y_2958_;
v___y_2909_ = v___y_2959_;
goto v___jp_2875_;
}
}
else
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_dec_ref_known(v_a_2713_, 1);
lean_dec(v_a_3021_);
lean_dec(v_a_3015_);
lean_dec(v_a_3005_);
lean_dec(v_a_2997_);
lean_dec(v_a_2988_);
lean_del_object(v___x_2982_);
lean_dec(v_a_2969_);
lean_dec(v_a_2961_);
lean_dec(v_charInst_x3f_2949_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_3056_ = lean_ctor_get(v___x_3051_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_3051_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3051_);
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
lean_del_object(v___x_2982_);
v___y_2876_ = v_a_2997_;
v___y_2877_ = v_a_3015_;
v___y_2878_ = v___y_2929_;
v___y_2879_ = v_a_2988_;
v___y_2880_ = v___y_2930_;
v___y_2881_ = v_a_2961_;
v___y_2882_ = v___x_2972_;
v___y_2883_ = v___y_2932_;
v___y_2884_ = v___y_2933_;
v___y_2885_ = v___y_2934_;
v___y_2886_ = v_a_3005_;
v___y_2887_ = v___y_2938_;
v___y_2888_ = v_a_3021_;
v___y_2889_ = v___y_2939_;
v___y_2890_ = v___y_2940_;
v___y_2891_ = v_a_2969_;
v___y_2892_ = v___y_2941_;
v___y_2893_ = v___y_2942_;
v___y_2894_ = v___y_2943_;
v___y_2895_ = v___y_2947_;
v___y_2896_ = v___y_2946_;
v___y_2897_ = v___x_3029_;
v___y_2898_ = v_charInst_x3f_2949_;
v_leFn_x3f_2899_ = v___x_3029_;
v___y_2900_ = v___y_2950_;
v___y_2901_ = v___y_2951_;
v___y_2902_ = v___y_2952_;
v___y_2903_ = v___y_2953_;
v___y_2904_ = v___y_2954_;
v___y_2905_ = v___y_2955_;
v___y_2906_ = v___y_2956_;
v___y_2907_ = v___y_2957_;
v___y_2908_ = v___y_2958_;
v___y_2909_ = v___y_2959_;
goto v___jp_2875_;
}
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
lean_dec(v_a_3021_);
lean_dec(v_a_3015_);
lean_dec(v_a_3005_);
lean_dec(v_a_2997_);
lean_dec(v_a_2988_);
lean_del_object(v___x_2982_);
lean_dec(v_a_2969_);
lean_dec(v_a_2961_);
lean_dec(v_charInst_x3f_2949_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_3064_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_3046_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_3046_);
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
lean_dec(v_a_3021_);
lean_dec(v_a_3017_);
lean_dec(v_a_3015_);
lean_dec(v_a_3005_);
lean_dec(v_a_2997_);
lean_dec(v_a_2988_);
lean_del_object(v___x_2982_);
lean_dec(v_a_2969_);
lean_dec(v_a_2961_);
lean_dec(v_charInst_x3f_2949_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_3072_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3074_ = v___x_3042_;
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_3042_);
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
lean_dec(v_a_3021_);
lean_dec(v_a_3017_);
lean_dec(v_a_3015_);
lean_dec(v_a_3007_);
lean_dec(v_a_3005_);
lean_dec(v_a_2997_);
lean_dec(v_a_2988_);
lean_del_object(v___x_2982_);
lean_dec(v_a_2969_);
lean_dec(v_a_2961_);
lean_dec(v_charInst_x3f_2949_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_3080_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3037_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3037_);
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
lean_dec(v_a_3021_);
lean_dec(v_a_3017_);
lean_dec(v_a_3015_);
lean_dec(v_a_3007_);
lean_dec(v_a_3005_);
lean_dec(v_a_3000_);
lean_dec(v_a_2997_);
lean_dec(v_a_2988_);
lean_del_object(v___x_2982_);
lean_dec(v_a_2969_);
lean_dec(v_a_2961_);
lean_dec(v_charInst_x3f_2949_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_3088_ = lean_ctor_get(v___x_3034_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3090_ = v___x_3034_;
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_3034_);
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
lean_dec(v_a_3021_);
lean_dec(v_a_3017_);
lean_dec(v_a_3015_);
lean_dec(v_a_3007_);
lean_dec(v_a_3005_);
lean_dec(v_a_3000_);
lean_dec(v_a_2997_);
lean_dec(v_a_2992_);
lean_dec(v_a_2988_);
lean_del_object(v___x_2982_);
lean_dec(v_a_2969_);
lean_dec(v_a_2961_);
lean_dec(v_charInst_x3f_2949_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_3096_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___x_3030_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3030_);
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
lean_dec(v_a_3021_);
lean_dec(v_a_3017_);
lean_dec(v_a_3015_);
lean_dec(v_a_3007_);
lean_dec(v_a_3005_);
lean_dec(v_a_3000_);
lean_dec(v_a_2997_);
lean_dec(v_a_2992_);
lean_dec(v_a_2988_);
lean_del_object(v___x_2982_);
lean_dec(v_a_2969_);
lean_dec(v_a_2961_);
lean_dec(v_charInst_x3f_2949_);
lean_dec_ref(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_3104_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3025_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3025_);
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
lean_dec(v_a_3017_);
lean_dec(v_a_3015_);
lean_dec(v_a_3007_);
lean_dec(v_a_3005_);
lean_dec(v_a_3000_);
lean_dec(v_a_2997_);
lean_dec(v_a_2992_);
lean_dec(v_a_2988_);
lean_del_object(v___x_2982_);
lean_dec(v_a_2969_);
lean_dec(v_a_2964_);
lean_dec(v_a_2961_);
lean_dec(v_charInst_x3f_2949_);
lean_dec_ref(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_3112_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_3020_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3020_);
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
lean_dec(v_a_3015_);
lean_dec_ref(v___x_3011_);
lean_dec(v_a_3007_);
lean_dec(v_a_3005_);
lean_dec(v_a_3000_);
lean_dec(v_a_2997_);
lean_dec(v_a_2992_);
lean_dec(v_a_2988_);
lean_del_object(v___x_2982_);
lean_dec(v_a_2969_);
lean_dec(v_a_2964_);
lean_dec(v_a_2961_);
lean_dec(v_charInst_x3f_2949_);
lean_dec_ref(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_3120_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3016_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3016_);
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
lean_dec_ref(v___x_3011_);
lean_dec(v_a_3007_);
lean_dec(v_a_3005_);
lean_dec(v_a_3000_);
lean_dec(v_a_2997_);
lean_dec(v_a_2992_);
lean_dec(v_a_2988_);
lean_del_object(v___x_2982_);
lean_dec(v_a_2969_);
lean_dec(v_a_2964_);
lean_dec(v_a_2961_);
lean_dec(v_charInst_x3f_2949_);
lean_dec_ref(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_3128_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3130_ = v___x_3014_;
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3014_);
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
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
lean_dec(v_a_3005_);
lean_dec(v_a_3000_);
lean_dec(v_a_2997_);
lean_dec(v_a_2992_);
lean_dec(v_a_2988_);
lean_del_object(v___x_2982_);
lean_dec(v_a_2969_);
lean_dec(v_a_2964_);
lean_dec(v_a_2961_);
lean_dec(v_charInst_x3f_2949_);
lean_dec_ref(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_3136_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3006_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3006_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
lean_dec(v_a_3000_);
lean_dec(v_a_2997_);
lean_dec(v_a_2992_);
lean_dec(v_a_2988_);
lean_del_object(v___x_2982_);
lean_dec(v_a_2969_);
lean_dec(v_a_2964_);
lean_dec(v_a_2961_);
lean_dec(v_charInst_x3f_2949_);
lean_dec_ref(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_3144_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3004_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3004_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
else
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_dec(v_a_2997_);
lean_dec(v_a_2992_);
lean_dec(v_a_2988_);
lean_del_object(v___x_2982_);
lean_dec(v_a_2969_);
lean_dec(v_a_2964_);
lean_dec(v_a_2961_);
lean_dec(v_charInst_x3f_2949_);
lean_dec_ref(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_3152_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_2999_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_2999_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
lean_dec(v_a_2992_);
lean_dec(v_a_2988_);
lean_del_object(v___x_2982_);
lean_dec(v_a_2969_);
lean_dec(v_a_2964_);
lean_dec(v_a_2961_);
lean_dec(v_charInst_x3f_2949_);
lean_dec_ref(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_3160_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_2996_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_2996_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
else
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
lean_dec(v_a_2988_);
lean_del_object(v___x_2982_);
lean_dec(v_a_2969_);
lean_dec(v_a_2964_);
lean_dec(v_a_2961_);
lean_dec(v_charInst_x3f_2949_);
lean_dec_ref(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_3168_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_2991_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_2991_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_a_3168_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
else
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3183_; 
lean_dec(v_a_2988_);
lean_del_object(v___x_2982_);
lean_dec(v_a_2969_);
lean_dec(v_a_2964_);
lean_dec(v_a_2961_);
lean_dec(v_charInst_x3f_2949_);
lean_dec_ref(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_3176_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3178_ = v___x_2989_;
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_2989_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3181_; 
if (v_isShared_3179_ == 0)
{
v___x_3181_ = v___x_3178_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_a_3176_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
}
}
else
{
lean_object* v_a_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3191_; 
lean_del_object(v___x_2982_);
lean_dec(v_a_2969_);
lean_dec(v_a_2964_);
lean_dec(v_a_2961_);
lean_dec(v_charInst_x3f_2949_);
lean_dec_ref(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_3184_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3186_ = v___x_2987_;
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_a_3184_);
lean_dec(v___x_2987_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3189_; 
if (v_isShared_3187_ == 0)
{
v___x_3189_ = v___x_3186_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_a_3184_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
}
}
else
{
lean_object* v___x_3193_; lean_object* v___x_3195_; 
lean_dec(v_a_2976_);
lean_dec(v_a_2969_);
lean_dec(v_a_2964_);
lean_dec(v_a_2961_);
lean_dec(v_charInst_x3f_2949_);
lean_dec_ref(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v___x_3193_ = lean_box(0);
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 0, v___x_3193_);
v___x_3195_ = v___x_2978_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v___x_3193_);
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
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
lean_dec(v_a_2969_);
lean_dec(v_a_2964_);
lean_dec(v_a_2961_);
lean_dec(v_charInst_x3f_2949_);
lean_dec_ref(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_3198_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___x_2975_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_2975_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
if (v_isShared_3201_ == 0)
{
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
else
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3213_; 
lean_dec(v_a_2964_);
lean_dec(v_a_2961_);
lean_dec(v_charInst_x3f_2949_);
lean_dec_ref(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_3206_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3208_ = v___x_2968_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_2968_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3211_; 
if (v_isShared_3209_ == 0)
{
v___x_3211_ = v___x_3208_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_a_3206_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
}
else
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3221_; 
lean_dec(v_a_2961_);
lean_dec(v_charInst_x3f_2949_);
lean_dec_ref(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_3214_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3216_ = v___x_2963_;
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_2963_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3219_; 
if (v_isShared_3217_ == 0)
{
v___x_3219_ = v___x_3216_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_a_3214_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
else
{
lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3229_; 
lean_dec(v_charInst_x3f_2949_);
lean_dec_ref(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v_a_2718_);
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v_type_2618_);
v_a_3222_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3224_ = v___x_2960_;
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_a_3222_);
lean_dec(v___x_2960_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3227_; 
if (v_isShared_3225_ == 0)
{
v___x_3227_ = v___x_3224_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_a_3222_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
}
}
}
else
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3591_; 
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v___f_2696_);
lean_dec_ref(v_type_2618_);
v_a_3584_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3586_ = v___x_2717_;
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v___x_2717_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3589_; 
if (v_isShared_3587_ == 0)
{
v___x_3589_ = v___x_3586_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_a_3584_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
}
else
{
lean_object* v_a_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3599_; 
lean_dec(v_a_2713_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v___f_2696_);
lean_dec_ref(v_type_2618_);
v_a_3592_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3594_ = v___x_2715_;
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_a_3592_);
lean_dec(v___x_2715_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3597_; 
if (v_isShared_3595_ == 0)
{
v___x_3597_ = v___x_3594_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_a_3592_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
}
else
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3607_; 
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v___f_2696_);
lean_dec_ref(v_type_2618_);
v_a_3600_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3602_ = v___x_2712_;
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_2712_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3605_; 
if (v_isShared_3603_ == 0)
{
v___x_3605_ = v___x_3602_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_a_3600_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
}
}
else
{
lean_del_object(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec_ref(v___f_2696_);
lean_dec_ref(v_type_2618_);
return v___x_2706_;
}
}
}
else
{
lean_object* v___x_3610_; lean_object* v___x_3612_; 
lean_dec(v_a_2698_);
lean_dec_ref(v___f_2696_);
lean_dec_ref(v_type_2618_);
v___x_3610_ = lean_box(0);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 0, v___x_3610_);
v___x_3612_ = v___x_2700_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v___x_3610_);
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
lean_dec_ref(v___f_2696_);
lean_dec_ref(v_type_2618_);
v_a_3615_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3617_ = v___x_2697_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_2697_);
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
v___jp_2630_:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2632_, 0, v___y_2631_);
v___x_2633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2632_);
return v___x_2633_;
}
v___jp_2634_:
{
if (lean_obj_tag(v___y_2636_) == 0)
{
lean_dec_ref_known(v___y_2636_, 1);
v___y_2631_ = v___y_2635_;
goto v___jp_2630_;
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_dec(v___y_2635_);
v_a_2637_ = lean_ctor_get(v___y_2636_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___y_2636_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___y_2636_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___y_2636_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
v___jp_2645_:
{
lean_object* v___x_2659_; 
v___x_2659_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v___y_2656_, v___y_2650_, v___y_2657_, v___y_2649_, v___y_2655_, v___y_2646_, v___y_2647_, v___y_2653_, v___y_2651_, v___y_2648_, v___y_2658_, v___y_2654_, v___y_2652_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v___x_2661_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc_n(v_a_2660_, 2);
lean_dec_ref_known(v___x_2659_, 1);
v___x_2661_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(v_a_2660_, v___y_2657_, v___y_2649_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v___x_2662_; 
lean_dec_ref_known(v___x_2661_, 1);
v___x_2662_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_a_2660_, v___y_2657_, v___y_2649_);
v___y_2635_ = v___y_2657_;
v___y_2636_ = v___x_2662_;
goto v___jp_2634_;
}
else
{
lean_dec(v_a_2660_);
v___y_2635_ = v___y_2657_;
v___y_2636_ = v___x_2661_;
goto v___jp_2634_;
}
}
else
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2670_; 
lean_dec(v___y_2657_);
v_a_2663_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2665_ = v___x_2659_;
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2659_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2668_; 
if (v_isShared_2666_ == 0)
{
v___x_2668_ = v___x_2665_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_a_2663_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
}
v___jp_2671_:
{
lean_object* v___x_2685_; 
v___x_2685_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v___y_2682_, v___y_2676_, v___y_2683_, v___y_2675_, v___y_2681_, v___y_2672_, v___y_2673_, v___y_2679_, v___y_2677_, v___y_2674_, v___y_2684_, v___y_2680_, v___y_2678_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v___x_2687_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_a_2686_);
lean_dec_ref_known(v___x_2685_, 1);
v___x_2687_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_a_2686_, v___y_2683_, v___y_2675_);
v___y_2635_ = v___y_2683_;
v___y_2636_ = v___x_2687_;
goto v___jp_2634_;
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
lean_dec(v___y_2683_);
v_a_2688_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2685_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2685_);
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
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2618_ = stack[0].m_obj;
lean_object* v_a_2619_ = stack[1].m_obj;
lean_object* v_a_2620_ = stack[2].m_obj;
lean_object* v_a_2621_ = stack[3].m_obj;
lean_object* v_a_2622_ = stack[4].m_obj;
lean_object* v_a_2623_ = stack[5].m_obj;
lean_object* v_a_2624_ = stack[6].m_obj;
lean_object* v_a_2625_ = stack[7].m_obj;
lean_object* v_a_2626_ = stack[8].m_obj;
lean_object* v_a_2627_ = stack[9].m_obj;
lean_object* v_a_2628_ = stack[10].m_obj;
lean_object* v_res_3623_;
v_res_3623_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f(v_type_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
stack->m_obj
 = v_res_3623_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___boxed(lean_object* v_type_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_){
_start:
{
lean_object* v_res_3636_; 
v_res_3636_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f(v_type_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_);
lean_dec(v_a_3634_);
lean_dec_ref(v_a_3633_);
lean_dec(v_a_3632_);
lean_dec_ref(v_a_3631_);
lean_dec(v_a_3630_);
lean_dec_ref(v_a_3629_);
lean_dec(v_a_3628_);
lean_dec_ref(v_a_3627_);
lean_dec(v_a_3626_);
lean_dec(v_a_3625_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0(lean_object* v_00_u03b2_3637_, lean_object* v_x_3638_, lean_object* v_x_3639_, lean_object* v_x_3640_){
_start:
{
lean_object* v___x_3641_; 
v___x_3641_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_x_3638_, v_x_3639_, v_x_3640_);
return v___x_3641_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0(lean_object* v_00_u03b2_3642_, lean_object* v_x_3643_, size_t v_x_3644_, size_t v_x_3645_, lean_object* v_x_3646_, lean_object* v_x_3647_){
_start:
{
lean_object* v___x_3648_; 
v___x_3648_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_x_3643_, v_x_3644_, v_x_3645_, v_x_3646_, v_x_3647_);
return v___x_3648_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3643_ = stack[1].m_obj;
size_t v_x_3644_ = stack[2].m_num;
size_t v_x_3645_ = stack[3].m_num;
lean_object* v_x_3646_ = stack[4].m_obj;
lean_object* v_x_3647_ = stack[5].m_obj;
lean_object* v_res_3649_;
v_res_3649_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0(lean_box(0), v_x_3643_, v_x_3644_, v_x_3645_, v_x_3646_, v_x_3647_);
stack->m_obj
 = v_res_3649_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3650_, lean_object* v_x_3651_, lean_object* v_x_3652_, lean_object* v_x_3653_, lean_object* v_x_3654_, lean_object* v_x_3655_){
_start:
{
size_t v_x_531582__boxed_3656_; size_t v_x_531583__boxed_3657_; lean_object* v_res_3658_; 
v_x_531582__boxed_3656_ = lean_unbox_usize(v_x_3652_);
lean_dec(v_x_3652_);
v_x_531583__boxed_3657_ = lean_unbox_usize(v_x_3653_);
lean_dec(v_x_3653_);
v_res_3658_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0(v_00_u03b2_3650_, v_x_3651_, v_x_531582__boxed_3656_, v_x_531583__boxed_3657_, v_x_3654_, v_x_3655_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3659_, lean_object* v_n_3660_, lean_object* v_k_3661_, lean_object* v_v_3662_){
_start:
{
lean_object* v___x_3663_; 
v___x_3663_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1___redArg(v_n_3660_, v_k_3661_, v_v_3662_);
return v___x_3663_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3664_, size_t v_depth_3665_, lean_object* v_keys_3666_, lean_object* v_vals_3667_, lean_object* v_heq_3668_, lean_object* v_i_3669_, lean_object* v_entries_3670_){
_start:
{
lean_object* v___x_3671_; 
v___x_3671_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(v_depth_3665_, v_keys_3666_, v_vals_3667_, v_i_3669_, v_entries_3670_);
return v___x_3671_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_depth_3665_ = stack[1].m_num;
lean_object* v_keys_3666_ = stack[2].m_obj;
lean_object* v_vals_3667_ = stack[3].m_obj;
lean_object* v_i_3669_ = stack[5].m_obj;
lean_object* v_entries_3670_ = stack[6].m_obj;
lean_object* v_res_3672_;
v_res_3672_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2(lean_box(0), v_depth_3665_, v_keys_3666_, v_vals_3667_, lean_box(0), v_i_3669_, v_entries_3670_);
stack->m_obj
 = v_res_3672_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3673_, lean_object* v_depth_3674_, lean_object* v_keys_3675_, lean_object* v_vals_3676_, lean_object* v_heq_3677_, lean_object* v_i_3678_, lean_object* v_entries_3679_){
_start:
{
size_t v_depth_boxed_3680_; lean_object* v_res_3681_; 
v_depth_boxed_3680_ = lean_unbox_usize(v_depth_3674_);
lean_dec(v_depth_3674_);
v_res_3681_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2(v_00_u03b2_3673_, v_depth_boxed_3680_, v_keys_3675_, v_vals_3676_, v_heq_3677_, v_i_3678_, v_entries_3679_);
lean_dec_ref(v_vals_3676_);
lean_dec_ref(v_keys_3675_);
return v_res_3681_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3682_, lean_object* v_x_3683_, lean_object* v_x_3684_, lean_object* v_x_3685_, lean_object* v_x_3686_){
_start:
{
lean_object* v___x_3687_; 
v___x_3687_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_x_3683_, v_x_3684_, v_x_3685_, v_x_3686_);
return v___x_3687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(lean_object* v_val_3688_, lean_object* v_base_3689_, lean_object* v_natModuleInst_3690_, lean_object* v_declName_3691_, lean_object* v_le_3692_, lean_object* v_mid_3693_, lean_object* v_ord_3694_){
_start:
{
lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3695_ = lean_box(0);
v___x_3696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3696_, 0, v_val_3688_);
lean_ctor_set(v___x_3696_, 1, v___x_3695_);
v___x_3697_ = l_Lean_mkConst(v_declName_3691_, v___x_3696_);
v___x_3698_ = l_Lean_mkApp5(v___x_3697_, v_base_3689_, v_natModuleInst_3690_, v_le_3692_, v_mid_3693_, v_ord_3694_);
return v___x_3698_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f(lean_object* v_type_3798_, lean_object* v_base_3799_, lean_object* v_natModuleInst_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_){
_start:
{
lean_object* v___x_3812_; 
lean_inc_ref(v_base_3799_);
v___x_3812_ = l_Lean_Meta_getDecLevel_x3f(v_base_3799_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_4550_; 
v_a_3813_ = lean_ctor_get(v___x_3812_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_3815_ = v___x_3812_;
v_isShared_3816_ = v_isSharedCheck_4550_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3812_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_4550_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
if (lean_obj_tag(v_a_3813_) == 1)
{
lean_object* v_val_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_4545_; 
lean_del_object(v___x_3815_);
v_val_3817_ = lean_ctor_get(v_a_3813_, 0);
v_isSharedCheck_4545_ = !lean_is_exclusive(v_a_3813_);
if (v_isSharedCheck_4545_ == 0)
{
v___x_3819_ = v_a_3813_;
v_isShared_3820_ = v_isSharedCheck_4545_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_val_3817_);
lean_dec(v_a_3813_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_4545_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v_a_3841_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v_a_3913_; lean_object* v___y_3930_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3933_; lean_object* v___y_3934_; lean_object* v___y_3935_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v___y_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___x_4131_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v_noNatDivInstQ_x3f_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4315_; lean_object* v___y_4316_; lean_object* v___y_4317_; lean_object* v_isLinearInstQ_x3f_4318_; lean_object* v___y_4319_; lean_object* v___y_4320_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___y_4323_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___x_4386_; 
v___x_4131_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1));
lean_inc_ref(v_base_3799_);
lean_inc(v_val_3817_);
v___x_4386_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_4131_, v_val_3817_, v_base_3799_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
if (lean_obj_tag(v___x_4386_) == 0)
{
lean_object* v_a_4387_; lean_object* v___y_4389_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v_fst_4398_; lean_object* v_snd_4399_; lean_object* v___y_4400_; lean_object* v___y_4401_; lean_object* v___y_4402_; lean_object* v___y_4403_; lean_object* v___y_4404_; lean_object* v___y_4405_; lean_object* v___y_4427_; lean_object* v___y_4428_; lean_object* v___y_4429_; lean_object* v___y_4430_; lean_object* v___y_4431_; lean_object* v___y_4432_; lean_object* v___y_4433_; lean_object* v___y_4434_; lean_object* v___y_4435_; lean_object* v___y_4436_; lean_object* v___y_4437_; lean_object* v___x_4439_; 
v_a_4387_ = lean_ctor_get(v___x_4386_, 0);
lean_inc_n(v_a_4387_, 2);
lean_dec_ref_known(v___x_4386_, 1);
lean_inc_ref(v_base_3799_);
lean_inc(v_val_3817_);
v___x_4439_ = l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f(v_val_3817_, v_base_3799_, v_a_4387_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
if (lean_obj_tag(v___x_4439_) == 0)
{
lean_object* v_a_4440_; lean_object* v_orderedAddInst_x3f_4442_; lean_object* v___y_4443_; lean_object* v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4446_; lean_object* v___y_4447_; lean_object* v___y_4448_; lean_object* v___y_4449_; lean_object* v___y_4450_; lean_object* v___y_4451_; lean_object* v___y_4452_; lean_object* v___y_4490_; lean_object* v___y_4491_; lean_object* v___y_4492_; lean_object* v___y_4493_; lean_object* v___y_4494_; lean_object* v___y_4495_; lean_object* v___y_4496_; lean_object* v___y_4497_; lean_object* v___y_4498_; lean_object* v___y_4499_; 
v_a_4440_ = lean_ctor_get(v___x_4439_, 0);
lean_inc(v_a_4440_);
lean_dec_ref_known(v___x_4439_, 1);
if (lean_obj_tag(v_a_4387_) == 1)
{
if (lean_obj_tag(v_a_4440_) == 1)
{
lean_object* v_val_4501_; lean_object* v_val_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; 
v_val_4501_ = lean_ctor_get(v_a_4387_, 0);
v_val_4502_ = lean_ctor_get(v_a_4440_, 0);
v___x_4503_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc_ref(v_base_3799_);
lean_inc(v_val_3817_);
v___x_4504_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_4503_, v_val_3817_, v_base_3799_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
if (lean_obj_tag(v___x_4504_) == 0)
{
lean_object* v_a_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; 
v_a_4505_ = lean_ctor_get(v___x_4504_, 0);
lean_inc(v_a_4505_);
lean_dec_ref_known(v___x_4504_, 1);
v___x_4506_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__66));
v___x_4507_ = lean_box(0);
lean_inc(v_val_3817_);
v___x_4508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4508_, 0, v_val_3817_);
lean_ctor_set(v___x_4508_, 1, v___x_4507_);
v___x_4509_ = l_Lean_mkConst(v___x_4506_, v___x_4508_);
lean_inc(v_val_4502_);
lean_inc(v_val_4501_);
lean_inc_ref(v_base_3799_);
v___x_4510_ = l_Lean_mkApp4(v___x_4509_, v_base_3799_, v_a_4505_, v_val_4501_, v_val_4502_);
v___x_4511_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4510_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
if (lean_obj_tag(v___x_4511_) == 0)
{
lean_object* v_a_4512_; 
v_a_4512_ = lean_ctor_get(v___x_4511_, 0);
lean_inc(v_a_4512_);
lean_dec_ref_known(v___x_4511_, 1);
v_orderedAddInst_x3f_4442_ = v_a_4512_;
v___y_4443_ = v_a_3801_;
v___y_4444_ = v_a_3802_;
v___y_4445_ = v_a_3803_;
v___y_4446_ = v_a_3804_;
v___y_4447_ = v_a_3805_;
v___y_4448_ = v_a_3806_;
v___y_4449_ = v_a_3807_;
v___y_4450_ = v_a_3808_;
v___y_4451_ = v_a_3809_;
v___y_4452_ = v_a_3810_;
goto v___jp_4441_;
}
else
{
lean_object* v_a_4513_; lean_object* v___x_4515_; uint8_t v_isShared_4516_; uint8_t v_isSharedCheck_4520_; 
lean_dec_ref_known(v_a_4440_, 1);
lean_dec_ref_known(v_a_4387_, 1);
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_natModuleInst_3800_);
lean_dec_ref(v_base_3799_);
lean_dec_ref(v_type_3798_);
v_a_4513_ = lean_ctor_get(v___x_4511_, 0);
v_isSharedCheck_4520_ = !lean_is_exclusive(v___x_4511_);
if (v_isSharedCheck_4520_ == 0)
{
v___x_4515_ = v___x_4511_;
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
else
{
lean_inc(v_a_4513_);
lean_dec(v___x_4511_);
v___x_4515_ = lean_box(0);
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
v_resetjp_4514_:
{
lean_object* v___x_4518_; 
if (v_isShared_4516_ == 0)
{
v___x_4518_ = v___x_4515_;
goto v_reusejp_4517_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_a_4513_);
v___x_4518_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4517_;
}
v_reusejp_4517_:
{
return v___x_4518_;
}
}
}
}
else
{
lean_object* v_a_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4528_; 
lean_dec_ref_known(v_a_4440_, 1);
lean_dec_ref_known(v_a_4387_, 1);
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_natModuleInst_3800_);
lean_dec_ref(v_base_3799_);
lean_dec_ref(v_type_3798_);
v_a_4521_ = lean_ctor_get(v___x_4504_, 0);
v_isSharedCheck_4528_ = !lean_is_exclusive(v___x_4504_);
if (v_isSharedCheck_4528_ == 0)
{
v___x_4523_ = v___x_4504_;
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_a_4521_);
lean_dec(v___x_4504_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v___x_4526_; 
if (v_isShared_4524_ == 0)
{
v___x_4526_ = v___x_4523_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v_a_4521_);
v___x_4526_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4525_;
}
v_reusejp_4525_:
{
return v___x_4526_;
}
}
}
}
else
{
v___y_4490_ = v_a_3801_;
v___y_4491_ = v_a_3802_;
v___y_4492_ = v_a_3803_;
v___y_4493_ = v_a_3804_;
v___y_4494_ = v_a_3805_;
v___y_4495_ = v_a_3806_;
v___y_4496_ = v_a_3807_;
v___y_4497_ = v_a_3808_;
v___y_4498_ = v_a_3809_;
v___y_4499_ = v_a_3810_;
goto v___jp_4489_;
}
}
else
{
v___y_4490_ = v_a_3801_;
v___y_4491_ = v_a_3802_;
v___y_4492_ = v_a_3803_;
v___y_4493_ = v_a_3804_;
v___y_4494_ = v_a_3805_;
v___y_4495_ = v_a_3806_;
v___y_4496_ = v_a_3807_;
v___y_4497_ = v_a_3808_;
v___y_4498_ = v_a_3809_;
v___y_4499_ = v_a_3810_;
goto v___jp_4489_;
}
v___jp_4441_:
{
if (lean_obj_tag(v_a_4387_) == 0)
{
lean_object* v___x_4453_; 
lean_dec(v_orderedAddInst_x3f_4442_);
lean_dec(v_a_4440_);
v___x_4453_ = lean_box(0);
v___y_4427_ = v___y_4448_;
v___y_4428_ = v___y_4446_;
v___y_4429_ = v___y_4447_;
v___y_4430_ = v___y_4449_;
v___y_4431_ = v___y_4452_;
v___y_4432_ = v___y_4444_;
v___y_4433_ = v___y_4443_;
v___y_4434_ = v___y_4450_;
v___y_4435_ = v___y_4451_;
v___y_4436_ = v___y_4445_;
v___y_4437_ = v___x_4453_;
goto v___jp_4426_;
}
else
{
if (lean_obj_tag(v_a_4440_) == 0)
{
lean_object* v___x_4454_; 
lean_dec_ref_known(v_a_4387_, 1);
lean_dec(v_orderedAddInst_x3f_4442_);
v___x_4454_ = lean_box(0);
v___y_4427_ = v___y_4448_;
v___y_4428_ = v___y_4446_;
v___y_4429_ = v___y_4447_;
v___y_4430_ = v___y_4449_;
v___y_4431_ = v___y_4452_;
v___y_4432_ = v___y_4444_;
v___y_4433_ = v___y_4443_;
v___y_4434_ = v___y_4450_;
v___y_4435_ = v___y_4451_;
v___y_4436_ = v___y_4445_;
v___y_4437_ = v___x_4454_;
goto v___jp_4426_;
}
else
{
if (lean_obj_tag(v_orderedAddInst_x3f_4442_) == 0)
{
lean_object* v___x_4455_; 
lean_dec_ref_known(v_a_4440_, 1);
lean_dec_ref_known(v_a_4387_, 1);
v___x_4455_ = lean_box(0);
v___y_4427_ = v___y_4448_;
v___y_4428_ = v___y_4446_;
v___y_4429_ = v___y_4447_;
v___y_4430_ = v___y_4449_;
v___y_4431_ = v___y_4452_;
v___y_4432_ = v___y_4444_;
v___y_4433_ = v___y_4443_;
v___y_4434_ = v___y_4450_;
v___y_4435_ = v___y_4451_;
v___y_4436_ = v___y_4445_;
v___y_4437_ = v___x_4455_;
goto v___jp_4426_;
}
else
{
lean_object* v_val_4456_; lean_object* v_val_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4488_; 
v_val_4456_ = lean_ctor_get(v_a_4387_, 0);
v_val_4457_ = lean_ctor_get(v_a_4440_, 0);
v_isSharedCheck_4488_ = !lean_is_exclusive(v_a_4440_);
if (v_isSharedCheck_4488_ == 0)
{
v___x_4459_ = v_a_4440_;
v_isShared_4460_ = v_isSharedCheck_4488_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_val_4457_);
lean_dec(v_a_4440_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4488_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v_val_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4487_; 
v_val_4461_ = lean_ctor_get(v_orderedAddInst_x3f_4442_, 0);
v_isSharedCheck_4487_ = !lean_is_exclusive(v_orderedAddInst_x3f_4442_);
if (v_isSharedCheck_4487_ == 0)
{
v___x_4463_ = v_orderedAddInst_x3f_4442_;
v_isShared_4464_ = v_isSharedCheck_4487_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_val_4461_);
lean_dec(v_orderedAddInst_x3f_4442_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4487_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4468_; 
v___x_4465_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__20));
lean_inc(v_val_4461_);
lean_inc(v_val_4457_);
lean_inc(v_val_4456_);
lean_inc_ref(v_natModuleInst_3800_);
lean_inc_ref(v_base_3799_);
lean_inc(v_val_3817_);
v___x_4466_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3817_, v_base_3799_, v_natModuleInst_3800_, v___x_4465_, v_val_4456_, v_val_4457_, v_val_4461_);
lean_inc_ref(v___x_4466_);
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 0, v___x_4466_);
v___x_4468_ = v___x_4463_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4486_; 
v_reuseFailAlloc_4486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4486_, 0, v___x_4466_);
v___x_4468_ = v_reuseFailAlloc_4486_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4472_; 
v___x_4469_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__22));
lean_inc(v_val_4461_);
lean_inc(v_val_4457_);
lean_inc(v_val_4456_);
lean_inc_ref(v_natModuleInst_3800_);
lean_inc_ref(v_base_3799_);
lean_inc(v_val_3817_);
v___x_4470_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3817_, v_base_3799_, v_natModuleInst_3800_, v___x_4469_, v_val_4456_, v_val_4457_, v_val_4461_);
if (v_isShared_4460_ == 0)
{
lean_ctor_set(v___x_4459_, 0, v___x_4470_);
v___x_4472_ = v___x_4459_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4485_; 
v_reuseFailAlloc_4485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4485_, 0, v___x_4470_);
v___x_4472_ = v_reuseFailAlloc_4485_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; 
v___x_4473_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__24));
lean_inc_n(v_val_4461_, 2);
lean_inc(v_val_4457_);
lean_inc_n(v_val_4456_, 3);
lean_inc_ref_n(v_natModuleInst_3800_, 2);
lean_inc_ref_n(v_base_3799_, 2);
lean_inc_n(v_val_3817_, 3);
v___x_4474_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3817_, v_base_3799_, v_natModuleInst_3800_, v___x_4473_, v_val_4456_, v_val_4457_, v_val_4461_);
v___x_4475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4475_, 0, v___x_4474_);
v___x_4476_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__26));
v___x_4477_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3817_, v_base_3799_, v_natModuleInst_3800_, v___x_4476_, v_val_4456_, v_val_4457_, v_val_4461_);
v___x_4478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4478_, 0, v___x_4477_);
v___x_4479_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__30));
v___x_4480_ = lean_box(0);
v___x_4481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4481_, 0, v_val_3817_);
lean_ctor_set(v___x_4481_, 1, v___x_4480_);
v___x_4482_ = l_Lean_mkConst(v___x_4479_, v___x_4481_);
lean_inc_ref(v_type_3798_);
v___x_4483_ = l_Lean_mkAppB(v___x_4482_, v_type_3798_, v___x_4466_);
v___x_4484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4484_, 0, v___x_4483_);
v___y_4389_ = v___x_4478_;
v___y_4390_ = v___y_4448_;
v___y_4391_ = v___y_4446_;
v___y_4392_ = v___y_4447_;
v___y_4393_ = v___x_4468_;
v___y_4394_ = v___y_4444_;
v___y_4395_ = v___y_4443_;
v___y_4396_ = v___y_4451_;
v___y_4397_ = v___y_4445_;
v_fst_4398_ = v_val_4456_;
v_snd_4399_ = v_val_4461_;
v___y_4400_ = v___x_4475_;
v___y_4401_ = v___y_4449_;
v___y_4402_ = v___y_4452_;
v___y_4403_ = v___x_4472_;
v___y_4404_ = v___y_4450_;
v___y_4405_ = v___x_4484_;
goto v___jp_4388_;
}
}
}
}
}
}
}
}
v___jp_4489_:
{
lean_object* v___x_4500_; 
v___x_4500_ = lean_box(0);
v_orderedAddInst_x3f_4442_ = v___x_4500_;
v___y_4443_ = v___y_4490_;
v___y_4444_ = v___y_4491_;
v___y_4445_ = v___y_4492_;
v___y_4446_ = v___y_4493_;
v___y_4447_ = v___y_4494_;
v___y_4448_ = v___y_4495_;
v___y_4449_ = v___y_4496_;
v___y_4450_ = v___y_4497_;
v___y_4451_ = v___y_4498_;
v___y_4452_ = v___y_4499_;
goto v___jp_4441_;
}
}
else
{
lean_object* v_a_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4536_; 
lean_dec(v_a_4387_);
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_natModuleInst_3800_);
lean_dec_ref(v_base_3799_);
lean_dec_ref(v_type_3798_);
v_a_4529_ = lean_ctor_get(v___x_4439_, 0);
v_isSharedCheck_4536_ = !lean_is_exclusive(v___x_4439_);
if (v_isSharedCheck_4536_ == 0)
{
v___x_4531_ = v___x_4439_;
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_a_4529_);
lean_dec(v___x_4439_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
lean_object* v___x_4534_; 
if (v_isShared_4532_ == 0)
{
v___x_4534_ = v___x_4531_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v_a_4529_);
v___x_4534_ = v_reuseFailAlloc_4535_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
return v___x_4534_;
}
}
}
v___jp_4388_:
{
lean_object* v___x_4406_; 
lean_inc_ref(v_base_3799_);
lean_inc(v_val_3817_);
v___x_4406_ = l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f(v_val_3817_, v_base_3799_, v_a_4387_, v___y_4392_, v___y_4390_, v___y_4401_, v___y_4404_, v___y_4396_, v___y_4402_);
if (lean_obj_tag(v___x_4406_) == 0)
{
lean_object* v_a_4407_; 
v_a_4407_ = lean_ctor_get(v___x_4406_, 0);
lean_inc(v_a_4407_);
lean_dec_ref_known(v___x_4406_, 1);
if (lean_obj_tag(v_a_4407_) == 0)
{
lean_dec_ref(v_snd_4399_);
lean_dec_ref(v_fst_4398_);
v___y_4313_ = v___y_4389_;
v___y_4314_ = v___y_4400_;
v___y_4315_ = v___y_4403_;
v___y_4316_ = v___y_4393_;
v___y_4317_ = v___y_4405_;
v_isLinearInstQ_x3f_4318_ = v_a_4407_;
v___y_4319_ = v___y_4395_;
v___y_4320_ = v___y_4394_;
v___y_4321_ = v___y_4397_;
v___y_4322_ = v___y_4391_;
v___y_4323_ = v___y_4392_;
v___y_4324_ = v___y_4390_;
v___y_4325_ = v___y_4401_;
v___y_4326_ = v___y_4404_;
v___y_4327_ = v___y_4396_;
v___y_4328_ = v___y_4402_;
goto v___jp_4312_;
}
else
{
lean_object* v_val_4408_; lean_object* v___x_4410_; uint8_t v_isShared_4411_; uint8_t v_isSharedCheck_4417_; 
v_val_4408_ = lean_ctor_get(v_a_4407_, 0);
v_isSharedCheck_4417_ = !lean_is_exclusive(v_a_4407_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4410_ = v_a_4407_;
v_isShared_4411_ = v_isSharedCheck_4417_;
goto v_resetjp_4409_;
}
else
{
lean_inc(v_val_4408_);
lean_dec(v_a_4407_);
v___x_4410_ = lean_box(0);
v_isShared_4411_ = v_isSharedCheck_4417_;
goto v_resetjp_4409_;
}
v_resetjp_4409_:
{
lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4415_; 
v___x_4412_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__18));
lean_inc_ref(v_natModuleInst_3800_);
lean_inc_ref(v_base_3799_);
lean_inc(v_val_3817_);
v___x_4413_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3817_, v_base_3799_, v_natModuleInst_3800_, v___x_4412_, v_fst_4398_, v_val_4408_, v_snd_4399_);
if (v_isShared_4411_ == 0)
{
lean_ctor_set(v___x_4410_, 0, v___x_4413_);
v___x_4415_ = v___x_4410_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v___x_4413_);
v___x_4415_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
v___y_4313_ = v___y_4389_;
v___y_4314_ = v___y_4400_;
v___y_4315_ = v___y_4403_;
v___y_4316_ = v___y_4393_;
v___y_4317_ = v___y_4405_;
v_isLinearInstQ_x3f_4318_ = v___x_4415_;
v___y_4319_ = v___y_4395_;
v___y_4320_ = v___y_4394_;
v___y_4321_ = v___y_4397_;
v___y_4322_ = v___y_4391_;
v___y_4323_ = v___y_4392_;
v___y_4324_ = v___y_4390_;
v___y_4325_ = v___y_4401_;
v___y_4326_ = v___y_4404_;
v___y_4327_ = v___y_4396_;
v___y_4328_ = v___y_4402_;
goto v___jp_4312_;
}
}
}
}
else
{
lean_object* v_a_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4425_; 
lean_dec(v___y_4405_);
lean_dec(v___y_4403_);
lean_dec(v___y_4400_);
lean_dec_ref(v_snd_4399_);
lean_dec_ref(v_fst_4398_);
lean_dec(v___y_4393_);
lean_dec(v___y_4389_);
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_natModuleInst_3800_);
lean_dec_ref(v_base_3799_);
lean_dec_ref(v_type_3798_);
v_a_4418_ = lean_ctor_get(v___x_4406_, 0);
v_isSharedCheck_4425_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4425_ == 0)
{
v___x_4420_ = v___x_4406_;
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_a_4418_);
lean_dec(v___x_4406_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___x_4423_; 
if (v_isShared_4421_ == 0)
{
v___x_4423_ = v___x_4420_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v_a_4418_);
v___x_4423_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
return v___x_4423_;
}
}
}
}
v___jp_4426_:
{
lean_object* v___x_4438_; 
v___x_4438_ = lean_box(0);
v___y_4313_ = v___x_4438_;
v___y_4314_ = v___x_4438_;
v___y_4315_ = v___x_4438_;
v___y_4316_ = v___x_4438_;
v___y_4317_ = v___x_4438_;
v_isLinearInstQ_x3f_4318_ = v___x_4438_;
v___y_4319_ = v___y_4433_;
v___y_4320_ = v___y_4432_;
v___y_4321_ = v___y_4436_;
v___y_4322_ = v___y_4428_;
v___y_4323_ = v___y_4429_;
v___y_4324_ = v___y_4427_;
v___y_4325_ = v___y_4430_;
v___y_4326_ = v___y_4434_;
v___y_4327_ = v___y_4435_;
v___y_4328_ = v___y_4431_;
goto v___jp_4312_;
}
}
else
{
lean_object* v_a_4537_; lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4544_; 
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_natModuleInst_3800_);
lean_dec_ref(v_base_3799_);
lean_dec_ref(v_type_3798_);
v_a_4537_ = lean_ctor_get(v___x_4386_, 0);
v_isSharedCheck_4544_ = !lean_is_exclusive(v___x_4386_);
if (v_isSharedCheck_4544_ == 0)
{
v___x_4539_ = v___x_4386_;
v_isShared_4540_ = v_isSharedCheck_4544_;
goto v_resetjp_4538_;
}
else
{
lean_inc(v_a_4537_);
lean_dec(v___x_4386_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4544_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
lean_object* v___x_4542_; 
if (v_isShared_4540_ == 0)
{
v___x_4542_ = v___x_4539_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v_a_4537_);
v___x_4542_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
return v___x_4542_;
}
}
}
v___jp_3821_:
{
lean_object* v___x_3842_; 
v___x_3842_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v___y_3831_, v___y_3827_);
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_object* v_a_3843_; lean_object* v_structs_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3848_; 
v_a_3843_ = lean_ctor_get(v___x_3842_, 0);
lean_inc(v_a_3843_);
lean_dec_ref_known(v___x_3842_, 1);
v_structs_3844_ = lean_ctor_get(v_a_3843_, 0);
lean_inc_ref(v_structs_3844_);
lean_dec(v_a_3843_);
v___x_3845_ = lean_array_get_size(v_structs_3844_);
lean_dec_ref(v_structs_3844_);
v___x_3846_ = lean_box(0);
lean_inc_ref(v___y_3838_);
if (v_isShared_3820_ == 0)
{
lean_ctor_set(v___x_3819_, 0, v___y_3838_);
v___x_3848_ = v___x_3819_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v___y_3838_);
v___x_3848_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; size_t v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; uint8_t v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___f_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; 
lean_inc_ref(v___y_3822_);
v___x_3849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3849_, 0, v___y_3822_);
v___x_3850_ = lean_unsigned_to_nat(32u);
v___x_3851_ = lean_mk_empty_array_with_capacity(v___x_3850_);
v___x_3852_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4);
v___x_3853_ = ((size_t)5ULL);
lean_inc(v___y_3824_);
v___x_3854_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3854_, 0, v___x_3852_);
lean_ctor_set(v___x_3854_, 1, v___x_3851_);
lean_ctor_set(v___x_3854_, 2, v___y_3824_);
lean_ctor_set(v___x_3854_, 3, v___y_3824_);
lean_ctor_set_usize(v___x_3854_, 4, v___x_3853_);
v___x_3855_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6);
v___x_3856_ = 0;
v___x_3857_ = lean_box(0);
lean_inc_ref_n(v___x_3854_, 7);
v___x_3858_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v___x_3858_, 0, v___x_3845_);
lean_ctor_set(v___x_3858_, 1, v___x_3846_);
lean_ctor_set(v___x_3858_, 2, v_type_3798_);
lean_ctor_set(v___x_3858_, 3, v_val_3817_);
lean_ctor_set(v___x_3858_, 4, v___y_3832_);
lean_ctor_set(v___x_3858_, 5, v___y_3826_);
lean_ctor_set(v___x_3858_, 6, v___y_3837_);
lean_ctor_set(v___x_3858_, 7, v___y_3839_);
lean_ctor_set(v___x_3858_, 8, v___y_3836_);
lean_ctor_set(v___x_3858_, 9, v___y_3823_);
lean_ctor_set(v___x_3858_, 10, v___y_3835_);
lean_ctor_set(v___x_3858_, 11, v___y_3828_);
lean_ctor_set(v___x_3858_, 12, v___x_3846_);
lean_ctor_set(v___x_3858_, 13, v___x_3846_);
lean_ctor_set(v___x_3858_, 14, v___x_3846_);
lean_ctor_set(v___x_3858_, 15, v___x_3846_);
lean_ctor_set(v___x_3858_, 16, v___x_3846_);
lean_ctor_set(v___x_3858_, 17, v___y_3840_);
lean_ctor_set(v___x_3858_, 18, v___y_3825_);
lean_ctor_set(v___x_3858_, 19, v___x_3846_);
lean_ctor_set(v___x_3858_, 20, v___y_3830_);
lean_ctor_set(v___x_3858_, 21, v_a_3841_);
lean_ctor_set(v___x_3858_, 22, v___y_3833_);
lean_ctor_set(v___x_3858_, 23, v___y_3838_);
lean_ctor_set(v___x_3858_, 24, v___y_3822_);
lean_ctor_set(v___x_3858_, 25, v___x_3848_);
lean_ctor_set(v___x_3858_, 26, v___x_3849_);
lean_ctor_set(v___x_3858_, 27, v___x_3846_);
lean_ctor_set(v___x_3858_, 28, v___y_3829_);
lean_ctor_set(v___x_3858_, 29, v___y_3834_);
lean_ctor_set(v___x_3858_, 30, v___x_3854_);
lean_ctor_set(v___x_3858_, 31, v___x_3855_);
lean_ctor_set(v___x_3858_, 32, v___x_3854_);
lean_ctor_set(v___x_3858_, 33, v___x_3854_);
lean_ctor_set(v___x_3858_, 34, v___x_3854_);
lean_ctor_set(v___x_3858_, 35, v___x_3854_);
lean_ctor_set(v___x_3858_, 36, v___x_3846_);
lean_ctor_set(v___x_3858_, 37, v___x_3855_);
lean_ctor_set(v___x_3858_, 38, v___x_3854_);
lean_ctor_set(v___x_3858_, 39, v___x_3857_);
lean_ctor_set(v___x_3858_, 40, v___x_3854_);
lean_ctor_set(v___x_3858_, 41, v___x_3854_);
lean_ctor_set_uint8(v___x_3858_, sizeof(void*)*42, v___x_3856_);
v___f_3859_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1), 2, 1);
lean_closure_set(v___f_3859_, 0, v___x_3858_);
v___x_3860_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3861_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3860_, v___f_3859_, v___y_3831_);
if (lean_obj_tag(v___x_3861_) == 0)
{
lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3869_; 
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3869_ == 0)
{
lean_object* v_unused_3870_; 
v_unused_3870_ = lean_ctor_get(v___x_3861_, 0);
lean_dec(v_unused_3870_);
v___x_3863_ = v___x_3861_;
v_isShared_3864_ = v_isSharedCheck_3869_;
goto v_resetjp_3862_;
}
else
{
lean_dec(v___x_3861_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3869_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3865_; lean_object* v___x_3867_; 
v___x_3865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3845_);
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 0, v___x_3865_);
v___x_3867_ = v___x_3863_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v___x_3865_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
}
else
{
lean_object* v_a_3871_; lean_object* v___x_3873_; uint8_t v_isShared_3874_; uint8_t v_isSharedCheck_3878_; 
v_a_3871_ = lean_ctor_get(v___x_3861_, 0);
v_isSharedCheck_3878_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_3873_ = v___x_3861_;
v_isShared_3874_ = v_isSharedCheck_3878_;
goto v_resetjp_3872_;
}
else
{
lean_inc(v_a_3871_);
lean_dec(v___x_3861_);
v___x_3873_ = lean_box(0);
v_isShared_3874_ = v_isSharedCheck_3878_;
goto v_resetjp_3872_;
}
v_resetjp_3872_:
{
lean_object* v___x_3876_; 
if (v_isShared_3874_ == 0)
{
v___x_3876_ = v___x_3873_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v_a_3871_);
v___x_3876_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
return v___x_3876_;
}
}
}
}
}
else
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3887_; 
lean_dec(v_a_3841_);
lean_dec_ref(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3830_);
lean_dec_ref(v___y_3829_);
lean_dec(v___y_3828_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
lean_dec(v___y_3824_);
lean_dec(v___y_3823_);
lean_dec_ref(v___y_3822_);
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_type_3798_);
v_a_3880_ = lean_ctor_get(v___x_3842_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3882_ = v___x_3842_;
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3842_);
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
}
v___jp_3888_:
{
if (lean_obj_tag(v___y_3907_) == 0)
{
lean_dec(v___y_3910_);
v___y_3822_ = v___y_3889_;
v___y_3823_ = v___y_3890_;
v___y_3824_ = v___y_3892_;
v___y_3825_ = v___y_3894_;
v___y_3826_ = v___y_3896_;
v___y_3827_ = v___y_3897_;
v___y_3828_ = v___y_3898_;
v___y_3829_ = v___y_3900_;
v___y_3830_ = v_a_3913_;
v___y_3831_ = v___y_3901_;
v___y_3832_ = v___y_3902_;
v___y_3833_ = v___y_3903_;
v___y_3834_ = v___y_3904_;
v___y_3835_ = v___y_3905_;
v___y_3836_ = v___y_3906_;
v___y_3837_ = v___y_3907_;
v___y_3838_ = v___y_3908_;
v___y_3839_ = v___y_3909_;
v___y_3840_ = v___y_3912_;
v_a_3841_ = v___y_3907_;
goto v___jp_3821_;
}
else
{
lean_object* v_val_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
v_val_3914_ = lean_ctor_get(v___y_3907_, 0);
v___x_3915_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__12));
v___x_3916_ = l_Lean_mkConst(v___x_3915_, v___y_3910_);
lean_inc(v_val_3914_);
lean_inc_ref(v_type_3798_);
v___x_3917_ = l_Lean_mkAppB(v___x_3916_, v_type_3798_, v_val_3914_);
v___x_3918_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3917_, v___y_3911_, v___y_3895_, v___y_3899_, v___y_3891_, v___y_3897_, v___y_3893_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v_a_3919_; lean_object* v___x_3920_; 
v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
lean_inc(v_a_3919_);
lean_dec_ref_known(v___x_3918_, 1);
v___x_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3920_, 0, v_a_3919_);
v___y_3822_ = v___y_3889_;
v___y_3823_ = v___y_3890_;
v___y_3824_ = v___y_3892_;
v___y_3825_ = v___y_3894_;
v___y_3826_ = v___y_3896_;
v___y_3827_ = v___y_3897_;
v___y_3828_ = v___y_3898_;
v___y_3829_ = v___y_3900_;
v___y_3830_ = v_a_3913_;
v___y_3831_ = v___y_3901_;
v___y_3832_ = v___y_3902_;
v___y_3833_ = v___y_3903_;
v___y_3834_ = v___y_3904_;
v___y_3835_ = v___y_3905_;
v___y_3836_ = v___y_3906_;
v___y_3837_ = v___y_3907_;
v___y_3838_ = v___y_3908_;
v___y_3839_ = v___y_3909_;
v___y_3840_ = v___y_3912_;
v_a_3841_ = v___x_3920_;
goto v___jp_3821_;
}
else
{
lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3928_; 
lean_dec_ref_known(v___y_3907_, 1);
lean_dec(v_a_3913_);
lean_dec_ref(v___y_3912_);
lean_dec(v___y_3909_);
lean_dec_ref(v___y_3908_);
lean_dec(v___y_3906_);
lean_dec(v___y_3905_);
lean_dec_ref(v___y_3904_);
lean_dec_ref(v___y_3903_);
lean_dec_ref(v___y_3902_);
lean_dec_ref(v___y_3900_);
lean_dec(v___y_3898_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3892_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_type_3798_);
v_a_3921_ = lean_ctor_get(v___x_3918_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3923_ = v___x_3918_;
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v___x_3918_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3926_; 
if (v_isShared_3924_ == 0)
{
v___x_3926_ = v___x_3923_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_a_3921_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
}
}
}
v___jp_3929_:
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3968_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__15));
lean_inc_ref(v___y_3932_);
v___x_3969_ = l_Lean_Name_mkStr2(v___y_3932_, v___x_3968_);
lean_inc(v___y_3942_);
v___x_3970_ = l_Lean_mkConst(v___x_3969_, v___y_3942_);
lean_inc_ref(v_type_3798_);
v___x_3971_ = l_Lean_mkAppB(v___x_3970_, v_type_3798_, v___y_3944_);
v___x_3972_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_3971_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_object* v_a_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
v_a_3973_ = lean_ctor_get(v___x_3972_, 0);
lean_inc(v_a_3973_);
lean_dec_ref_known(v___x_3972_, 1);
v___x_3974_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__20));
lean_inc_ref(v___y_3945_);
v___x_3975_ = l_Lean_Name_mkStr2(v___y_3945_, v___x_3974_);
lean_inc(v___y_3942_);
v___x_3976_ = l_Lean_mkConst(v___x_3975_, v___y_3942_);
lean_inc_ref(v_type_3798_);
v___x_3977_ = l_Lean_mkApp3(v___x_3976_, v_type_3798_, v___y_3954_, v___y_3941_);
v___x_3978_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3977_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
if (lean_obj_tag(v___x_3978_) == 0)
{
lean_object* v_a_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
v_a_3979_ = lean_ctor_get(v___x_3978_, 0);
lean_inc(v_a_3979_);
lean_dec_ref_known(v___x_3978_, 1);
v___x_3980_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__63));
lean_inc_ref(v___y_3957_);
v___x_3981_ = l_Lean_Name_mkStr2(v___y_3957_, v___x_3980_);
lean_inc(v___y_3956_);
v___x_3982_ = l_Lean_mkConst(v___x_3981_, v___y_3956_);
lean_inc_ref_n(v_type_3798_, 3);
v___x_3983_ = l_Lean_mkApp4(v___x_3982_, v_type_3798_, v_type_3798_, v_type_3798_, v___y_3951_);
v___x_3984_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3983_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v_a_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; 
v_a_3985_ = lean_ctor_get(v___x_3984_, 0);
lean_inc(v_a_3985_);
lean_dec_ref_known(v___x_3984_, 1);
v___x_3986_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__24));
lean_inc_ref(v___y_3934_);
v___x_3987_ = l_Lean_Name_mkStr2(v___y_3934_, v___x_3986_);
v___x_3988_ = l_Lean_mkConst(v___x_3987_, v___y_3956_);
lean_inc_ref_n(v_type_3798_, 3);
v___x_3989_ = l_Lean_mkApp4(v___x_3988_, v_type_3798_, v_type_3798_, v_type_3798_, v___y_3955_);
v___x_3990_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3989_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
if (lean_obj_tag(v___x_3990_) == 0)
{
lean_object* v_a_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; 
v_a_3991_ = lean_ctor_get(v___x_3990_, 0);
lean_inc(v_a_3991_);
lean_dec_ref_known(v___x_3990_, 1);
v___x_3992_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__28));
lean_inc_ref(v___y_3935_);
v___x_3993_ = l_Lean_Name_mkStr2(v___y_3935_, v___x_3992_);
lean_inc(v___y_3942_);
v___x_3994_ = l_Lean_mkConst(v___x_3993_, v___y_3942_);
lean_inc_ref(v_type_3798_);
v___x_3995_ = l_Lean_mkAppB(v___x_3994_, v_type_3798_, v___y_3939_);
v___x_3996_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3995_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
if (lean_obj_tag(v___x_3996_) == 0)
{
lean_object* v_a_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
v_a_3997_ = lean_ctor_get(v___x_3996_, 0);
lean_inc(v_a_3997_);
lean_dec_ref_known(v___x_3996_, 1);
v___x_3998_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__0));
lean_inc_ref(v___y_3948_);
v___x_3999_ = l_Lean_Name_mkStr2(v___y_3948_, v___x_3998_);
v___x_4000_ = l_Lean_mkConst(v___x_3999_, v___y_3936_);
lean_inc_ref_n(v_type_3798_, 2);
lean_inc_ref(v___x_4000_);
v___x_4001_ = l_Lean_mkApp4(v___x_4000_, v___y_3947_, v_type_3798_, v_type_3798_, v___y_3943_);
v___x_4002_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4001_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
if (lean_obj_tag(v___x_4002_) == 0)
{
lean_object* v_a_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
v_a_4003_ = lean_ctor_get(v___x_4002_, 0);
lean_inc(v_a_4003_);
lean_dec_ref_known(v___x_4002_, 1);
lean_inc_ref_n(v_type_3798_, 2);
v___x_4004_ = l_Lean_mkApp4(v___x_4000_, v___y_3952_, v_type_3798_, v_type_3798_, v___y_3953_);
v___x_4005_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4004_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
if (lean_obj_tag(v___x_4005_) == 0)
{
if (lean_obj_tag(v___y_3946_) == 0)
{
lean_object* v_a_4006_; 
v_a_4006_ = lean_ctor_get(v___x_4005_, 0);
lean_inc(v_a_4006_);
lean_dec_ref_known(v___x_4005_, 1);
v___y_3889_ = v_a_4006_;
v___y_3890_ = v___y_3930_;
v___y_3891_ = v___y_3965_;
v___y_3892_ = v___y_3931_;
v___y_3893_ = v___y_3967_;
v___y_3894_ = v_a_3979_;
v___y_3895_ = v___y_3963_;
v___y_3896_ = v___y_3946_;
v___y_3897_ = v___y_3966_;
v___y_3898_ = v___y_3933_;
v___y_3899_ = v___y_3964_;
v___y_3900_ = v_a_3991_;
v___y_3901_ = v___y_3958_;
v___y_3902_ = v___y_3937_;
v___y_3903_ = v_a_3985_;
v___y_3904_ = v_a_3997_;
v___y_3905_ = v___y_3949_;
v___y_3906_ = v___y_3938_;
v___y_3907_ = v___y_3950_;
v___y_3908_ = v_a_4003_;
v___y_3909_ = v___y_3940_;
v___y_3910_ = v___y_3942_;
v___y_3911_ = v___y_3962_;
v___y_3912_ = v_a_3973_;
v_a_3913_ = v___y_3946_;
goto v___jp_3888_;
}
else
{
lean_object* v_a_4007_; lean_object* v_val_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
v_a_4007_ = lean_ctor_get(v___x_4005_, 0);
lean_inc(v_a_4007_);
lean_dec_ref_known(v___x_4005_, 1);
v_val_4008_ = lean_ctor_get(v___y_3946_, 0);
v___x_4009_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__46));
lean_inc(v___y_3942_);
v___x_4010_ = l_Lean_mkConst(v___x_4009_, v___y_3942_);
lean_inc(v_val_4008_);
lean_inc_ref(v_type_3798_);
v___x_4011_ = l_Lean_mkAppB(v___x_4010_, v_type_3798_, v_val_4008_);
v___x_4012_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4011_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
if (lean_obj_tag(v___x_4012_) == 0)
{
lean_object* v_a_4013_; lean_object* v___x_4014_; 
v_a_4013_ = lean_ctor_get(v___x_4012_, 0);
lean_inc(v_a_4013_);
lean_dec_ref_known(v___x_4012_, 1);
v___x_4014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4014_, 0, v_a_4013_);
v___y_3889_ = v_a_4007_;
v___y_3890_ = v___y_3930_;
v___y_3891_ = v___y_3965_;
v___y_3892_ = v___y_3931_;
v___y_3893_ = v___y_3967_;
v___y_3894_ = v_a_3979_;
v___y_3895_ = v___y_3963_;
v___y_3896_ = v___y_3946_;
v___y_3897_ = v___y_3966_;
v___y_3898_ = v___y_3933_;
v___y_3899_ = v___y_3964_;
v___y_3900_ = v_a_3991_;
v___y_3901_ = v___y_3958_;
v___y_3902_ = v___y_3937_;
v___y_3903_ = v_a_3985_;
v___y_3904_ = v_a_3997_;
v___y_3905_ = v___y_3949_;
v___y_3906_ = v___y_3938_;
v___y_3907_ = v___y_3950_;
v___y_3908_ = v_a_4003_;
v___y_3909_ = v___y_3940_;
v___y_3910_ = v___y_3942_;
v___y_3911_ = v___y_3962_;
v___y_3912_ = v_a_3973_;
v_a_3913_ = v___x_4014_;
goto v___jp_3888_;
}
else
{
lean_object* v_a_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4022_; 
lean_dec(v_a_4007_);
lean_dec_ref_known(v___y_3946_, 1);
lean_dec(v_a_4003_);
lean_dec(v_a_3997_);
lean_dec(v_a_3991_);
lean_dec(v_a_3985_);
lean_dec(v_a_3979_);
lean_dec(v_a_3973_);
lean_dec(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec(v___y_3942_);
lean_dec(v___y_3940_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v___y_3933_);
lean_dec(v___y_3931_);
lean_dec(v___y_3930_);
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_type_3798_);
v_a_4015_ = lean_ctor_get(v___x_4012_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4017_ = v___x_4012_;
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_a_4015_);
lean_dec(v___x_4012_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4020_; 
if (v_isShared_4018_ == 0)
{
v___x_4020_ = v___x_4017_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_a_4015_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
}
}
}
}
}
else
{
lean_object* v_a_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4030_; 
lean_dec(v_a_4003_);
lean_dec(v_a_3997_);
lean_dec(v_a_3991_);
lean_dec(v_a_3985_);
lean_dec(v_a_3979_);
lean_dec(v_a_3973_);
lean_dec(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec(v___y_3946_);
lean_dec(v___y_3942_);
lean_dec(v___y_3940_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v___y_3933_);
lean_dec(v___y_3931_);
lean_dec(v___y_3930_);
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_type_3798_);
v_a_4023_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4030_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_4025_ = v___x_4005_;
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_a_4023_);
lean_dec(v___x_4005_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4028_; 
if (v_isShared_4026_ == 0)
{
v___x_4028_ = v___x_4025_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v_a_4023_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
}
}
else
{
lean_object* v_a_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4038_; 
lean_dec_ref(v___x_4000_);
lean_dec(v_a_3997_);
lean_dec(v_a_3991_);
lean_dec(v_a_3985_);
lean_dec(v_a_3979_);
lean_dec(v_a_3973_);
lean_dec_ref(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec(v___y_3946_);
lean_dec(v___y_3942_);
lean_dec(v___y_3940_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v___y_3933_);
lean_dec(v___y_3931_);
lean_dec(v___y_3930_);
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_type_3798_);
v_a_4031_ = lean_ctor_get(v___x_4002_, 0);
v_isSharedCheck_4038_ = !lean_is_exclusive(v___x_4002_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_4033_ = v___x_4002_;
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_a_4031_);
lean_dec(v___x_4002_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v___x_4036_; 
if (v_isShared_4034_ == 0)
{
v___x_4036_ = v___x_4033_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_a_4031_);
v___x_4036_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
return v___x_4036_;
}
}
}
}
else
{
lean_object* v_a_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4046_; 
lean_dec(v_a_3991_);
lean_dec(v_a_3985_);
lean_dec(v_a_3979_);
lean_dec(v_a_3973_);
lean_dec_ref(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3947_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec(v___y_3940_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v___y_3936_);
lean_dec(v___y_3933_);
lean_dec(v___y_3931_);
lean_dec(v___y_3930_);
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_type_3798_);
v_a_4039_ = lean_ctor_get(v___x_3996_, 0);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4041_ = v___x_3996_;
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_a_4039_);
lean_dec(v___x_3996_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v___x_4044_; 
if (v_isShared_4042_ == 0)
{
v___x_4044_ = v___x_4041_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v_a_4039_);
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
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4054_; 
lean_dec(v_a_3985_);
lean_dec(v_a_3979_);
lean_dec(v_a_3973_);
lean_dec_ref(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3947_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v___y_3936_);
lean_dec(v___y_3933_);
lean_dec(v___y_3931_);
lean_dec(v___y_3930_);
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_type_3798_);
v_a_4047_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_4054_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4049_ = v___x_3990_;
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_3990_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v___x_4052_; 
if (v_isShared_4050_ == 0)
{
v___x_4052_ = v___x_4049_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_a_4047_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
}
}
else
{
lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4062_; 
lean_dec(v_a_3979_);
lean_dec(v_a_3973_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
lean_dec_ref(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3947_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v___y_3936_);
lean_dec(v___y_3933_);
lean_dec(v___y_3931_);
lean_dec(v___y_3930_);
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_type_3798_);
v_a_4055_ = lean_ctor_get(v___x_3984_, 0);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4057_ = v___x_3984_;
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_a_4055_);
lean_dec(v___x_3984_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4060_; 
if (v_isShared_4058_ == 0)
{
v___x_4060_ = v___x_4057_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_a_4055_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
}
else
{
lean_object* v_a_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4070_; 
lean_dec(v_a_3973_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
lean_dec_ref(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec_ref(v___y_3951_);
lean_dec(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3947_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v___y_3936_);
lean_dec(v___y_3933_);
lean_dec(v___y_3931_);
lean_dec(v___y_3930_);
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_type_3798_);
v_a_4063_ = lean_ctor_get(v___x_3978_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_3978_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4065_ = v___x_3978_;
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_a_4063_);
lean_dec(v___x_3978_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4068_; 
if (v_isShared_4066_ == 0)
{
v___x_4068_ = v___x_4065_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_a_4063_);
v___x_4068_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
return v___x_4068_;
}
}
}
}
else
{
lean_object* v_a_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4078_; 
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec_ref(v___y_3951_);
lean_dec(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3947_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec_ref(v___y_3941_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v___y_3936_);
lean_dec(v___y_3933_);
lean_dec(v___y_3931_);
lean_dec(v___y_3930_);
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_type_3798_);
v_a_4071_ = lean_ctor_get(v___x_3972_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_3972_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4073_ = v___x_3972_;
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_a_4071_);
lean_dec(v___x_3972_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4076_; 
if (v_isShared_4074_ == 0)
{
v___x_4076_ = v___x_4073_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_a_4071_);
v___x_4076_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
return v___x_4076_;
}
}
}
}
v___jp_4079_:
{
if (lean_obj_tag(v___y_4100_) == 1)
{
lean_object* v_val_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; 
v_val_4118_ = lean_ctor_get(v___y_4100_, 0);
v___x_4119_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__3));
lean_inc(v___y_4091_);
v___x_4120_ = l_Lean_mkConst(v___x_4119_, v___y_4091_);
lean_inc_ref(v_type_3798_);
v___x_4121_ = l_Lean_Expr_app___override(v___x_4120_, v_type_3798_);
lean_inc(v_val_4118_);
v___x_4122_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4121_, v_val_4118_, v___y_4113_);
if (lean_obj_tag(v___x_4122_) == 0)
{
lean_dec_ref_known(v___x_4122_, 1);
v___y_3930_ = v___y_4080_;
v___y_3931_ = v___y_4081_;
v___y_3932_ = v___y_4082_;
v___y_3933_ = v___y_4083_;
v___y_3934_ = v___y_4084_;
v___y_3935_ = v___y_4087_;
v___y_3936_ = v___y_4086_;
v___y_3937_ = v___y_4085_;
v___y_3938_ = v___y_4088_;
v___y_3939_ = v___y_4089_;
v___y_3940_ = v___y_4090_;
v___y_3941_ = v___y_4092_;
v___y_3942_ = v___y_4091_;
v___y_3943_ = v___y_4093_;
v___y_3944_ = v___y_4094_;
v___y_3945_ = v___y_4095_;
v___y_3946_ = v___y_4096_;
v___y_3947_ = v___y_4097_;
v___y_3948_ = v___y_4098_;
v___y_3949_ = v___y_4099_;
v___y_3950_ = v___y_4100_;
v___y_3951_ = v___y_4101_;
v___y_3952_ = v___y_4102_;
v___y_3953_ = v___y_4103_;
v___y_3954_ = v___y_4104_;
v___y_3955_ = v___y_4107_;
v___y_3956_ = v___y_4106_;
v___y_3957_ = v___y_4105_;
v___y_3958_ = v___y_4108_;
v___y_3959_ = v___y_4109_;
v___y_3960_ = v___y_4110_;
v___y_3961_ = v___y_4111_;
v___y_3962_ = v___y_4112_;
v___y_3963_ = v___y_4113_;
v___y_3964_ = v___y_4114_;
v___y_3965_ = v___y_4115_;
v___y_3966_ = v___y_4116_;
v___y_3967_ = v___y_4117_;
goto v___jp_3929_;
}
else
{
lean_object* v_a_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4130_; 
lean_dec_ref_known(v___y_4100_, 1);
lean_dec_ref(v___y_4107_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec_ref(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec(v___y_4099_);
lean_dec_ref(v___y_4097_);
lean_dec(v___y_4096_);
lean_dec_ref(v___y_4094_);
lean_dec_ref(v___y_4093_);
lean_dec_ref(v___y_4092_);
lean_dec(v___y_4091_);
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4089_);
lean_dec(v___y_4088_);
lean_dec(v___y_4086_);
lean_dec_ref(v___y_4085_);
lean_dec(v___y_4083_);
lean_dec(v___y_4081_);
lean_dec(v___y_4080_);
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_type_3798_);
v_a_4123_ = lean_ctor_get(v___x_4122_, 0);
v_isSharedCheck_4130_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4130_ == 0)
{
v___x_4125_ = v___x_4122_;
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_a_4123_);
lean_dec(v___x_4122_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4128_; 
if (v_isShared_4126_ == 0)
{
v___x_4128_ = v___x_4125_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4129_; 
v_reuseFailAlloc_4129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4129_, 0, v_a_4123_);
v___x_4128_ = v_reuseFailAlloc_4129_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
return v___x_4128_;
}
}
}
}
else
{
v___y_3930_ = v___y_4080_;
v___y_3931_ = v___y_4081_;
v___y_3932_ = v___y_4082_;
v___y_3933_ = v___y_4083_;
v___y_3934_ = v___y_4084_;
v___y_3935_ = v___y_4087_;
v___y_3936_ = v___y_4086_;
v___y_3937_ = v___y_4085_;
v___y_3938_ = v___y_4088_;
v___y_3939_ = v___y_4089_;
v___y_3940_ = v___y_4090_;
v___y_3941_ = v___y_4092_;
v___y_3942_ = v___y_4091_;
v___y_3943_ = v___y_4093_;
v___y_3944_ = v___y_4094_;
v___y_3945_ = v___y_4095_;
v___y_3946_ = v___y_4096_;
v___y_3947_ = v___y_4097_;
v___y_3948_ = v___y_4098_;
v___y_3949_ = v___y_4099_;
v___y_3950_ = v___y_4100_;
v___y_3951_ = v___y_4101_;
v___y_3952_ = v___y_4102_;
v___y_3953_ = v___y_4103_;
v___y_3954_ = v___y_4104_;
v___y_3955_ = v___y_4107_;
v___y_3956_ = v___y_4106_;
v___y_3957_ = v___y_4105_;
v___y_3958_ = v___y_4108_;
v___y_3959_ = v___y_4109_;
v___y_3960_ = v___y_4110_;
v___y_3961_ = v___y_4111_;
v___y_3962_ = v___y_4112_;
v___y_3963_ = v___y_4113_;
v___y_3964_ = v___y_4114_;
v___y_3965_ = v___y_4115_;
v___y_3966_ = v___y_4116_;
v___y_3967_ = v___y_4117_;
goto v___jp_3929_;
}
}
v___jp_4132_:
{
lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; 
v___x_4151_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__2));
lean_inc_n(v___y_4139_, 14);
v___x_4152_ = l_Lean_mkConst(v___x_4151_, v___y_4139_);
v___x_4153_ = l_Lean_mkAppB(v___x_4152_, v_base_3799_, v_natModuleInst_3800_);
v___x_4154_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__55));
v___x_4155_ = l_Lean_mkConst(v___x_4154_, v___y_4139_);
lean_inc_ref_n(v___x_4153_, 4);
lean_inc_ref_n(v_type_3798_, 14);
v___x_4156_ = l_Lean_mkAppB(v___x_4155_, v_type_3798_, v___x_4153_);
v___x_4157_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58));
v___x_4158_ = l_Lean_mkConst(v___x_4157_, v___y_4139_);
lean_inc_ref_n(v___x_4156_, 2);
v___x_4159_ = l_Lean_mkAppB(v___x_4158_, v_type_3798_, v___x_4156_);
v___x_4160_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__3));
v___x_4161_ = l_Lean_mkConst(v___x_4160_, v___y_4139_);
lean_inc_ref(v___x_4159_);
v___x_4162_ = l_Lean_mkAppB(v___x_4161_, v_type_3798_, v___x_4159_);
v___x_4163_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__13));
v___x_4164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__5));
v___x_4165_ = l_Lean_mkConst(v___x_4164_, v___y_4139_);
lean_inc_ref(v___x_4162_);
v___x_4166_ = l_Lean_mkAppB(v___x_4165_, v_type_3798_, v___x_4162_);
v___x_4167_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__34));
v___x_4168_ = l_Lean_mkConst(v___x_4167_, v___y_4139_);
v___x_4169_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__6));
v___x_4170_ = l_Lean_mkConst(v___x_4169_, v___y_4139_);
v___x_4171_ = l_Lean_mkAppB(v___x_4170_, v_type_3798_, v___x_4159_);
v___x_4172_ = l_Lean_mkAppB(v___x_4168_, v_type_3798_, v___x_4171_);
v___x_4173_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__37));
v___x_4174_ = l_Lean_mkConst(v___x_4173_, v___y_4139_);
v___x_4175_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__7));
v___x_4176_ = l_Lean_mkConst(v___x_4175_, v___y_4139_);
v___x_4177_ = l_Lean_mkAppB(v___x_4176_, v_type_3798_, v___x_4156_);
v___x_4178_ = l_Lean_mkAppB(v___x_4174_, v_type_3798_, v___x_4177_);
v___x_4179_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__8));
v___x_4180_ = l_Lean_mkConst(v___x_4179_, v___y_4139_);
v___x_4181_ = l_Lean_mkAppB(v___x_4180_, v_type_3798_, v___x_4156_);
v___x_4182_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__41));
v___x_4183_ = lean_unsigned_to_nat(0u);
v___x_4184_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_4185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4184_);
lean_ctor_set(v___x_4185_, 1, v___y_4139_);
v___x_4186_ = l_Lean_mkConst(v___x_4182_, v___x_4185_);
v___x_4187_ = l_Lean_Int_mkType;
v___x_4188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__9));
v___x_4189_ = l_Lean_mkConst(v___x_4188_, v___y_4139_);
v___x_4190_ = l_Lean_mkAppB(v___x_4189_, v_type_3798_, v___x_4153_);
lean_inc_ref(v___x_4186_);
v___x_4191_ = l_Lean_mkApp3(v___x_4186_, v___x_4187_, v_type_3798_, v___x_4190_);
v___x_4192_ = l_Lean_Nat_mkType;
v___x_4193_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__10));
v___x_4194_ = l_Lean_mkConst(v___x_4193_, v___y_4139_);
v___x_4195_ = l_Lean_mkAppB(v___x_4194_, v_type_3798_, v___x_4153_);
v___x_4196_ = l_Lean_mkApp3(v___x_4186_, v___x_4192_, v_type_3798_, v___x_4195_);
v___x_4197_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3));
v___x_4198_ = l_Lean_mkConst(v___x_4197_, v___y_4139_);
v___x_4199_ = l_Lean_Expr_app___override(v___x_4198_, v_type_3798_);
v___x_4200_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4199_, v___x_4153_, v___y_4146_);
if (lean_obj_tag(v___x_4200_) == 0)
{
lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; 
lean_dec_ref_known(v___x_4200_, 1);
v___x_4201_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__14));
lean_inc(v___y_4139_);
v___x_4202_ = l_Lean_mkConst(v___x_4201_, v___y_4139_);
lean_inc_ref(v_type_3798_);
v___x_4203_ = l_Lean_Expr_app___override(v___x_4202_, v_type_3798_);
lean_inc_ref(v___x_4162_);
v___x_4204_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4203_, v___x_4162_, v___y_4146_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; 
lean_dec_ref_known(v___x_4204_, 1);
v___x_4205_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__17));
v___x_4206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__18));
lean_inc(v___y_4139_);
v___x_4207_ = l_Lean_mkConst(v___x_4206_, v___y_4139_);
v___x_4208_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19);
lean_inc_ref(v_type_3798_);
v___x_4209_ = l_Lean_mkAppB(v___x_4207_, v_type_3798_, v___x_4208_);
lean_inc_ref(v___x_4166_);
v___x_4210_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4209_, v___x_4166_, v___y_4146_);
if (lean_obj_tag(v___x_4210_) == 0)
{
lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
lean_dec_ref_known(v___x_4210_, 1);
v___x_4211_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__61));
v___x_4212_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc(v___y_4139_);
lean_inc_n(v_val_3817_, 2);
v___x_4213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4213_, 0, v_val_3817_);
lean_ctor_set(v___x_4213_, 1, v___y_4139_);
lean_inc_ref(v___x_4213_);
v___x_4214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4214_, 0, v_val_3817_);
lean_ctor_set(v___x_4214_, 1, v___x_4213_);
lean_inc_ref(v___x_4214_);
v___x_4215_ = l_Lean_mkConst(v___x_4212_, v___x_4214_);
lean_inc_ref_n(v_type_3798_, 3);
v___x_4216_ = l_Lean_mkApp3(v___x_4215_, v_type_3798_, v_type_3798_, v_type_3798_);
lean_inc_ref(v___x_4172_);
v___x_4217_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4216_, v___x_4172_, v___y_4146_);
if (lean_obj_tag(v___x_4217_) == 0)
{
lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; 
lean_dec_ref_known(v___x_4217_, 1);
v___x_4218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__22));
v___x_4219_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__23));
lean_inc_ref(v___x_4214_);
v___x_4220_ = l_Lean_mkConst(v___x_4219_, v___x_4214_);
lean_inc_ref_n(v_type_3798_, 3);
v___x_4221_ = l_Lean_mkApp3(v___x_4220_, v_type_3798_, v_type_3798_, v_type_3798_);
lean_inc_ref(v___x_4178_);
v___x_4222_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4221_, v___x_4178_, v___y_4146_);
if (lean_obj_tag(v___x_4222_) == 0)
{
lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
lean_dec_ref_known(v___x_4222_, 1);
v___x_4223_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__26));
v___x_4224_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__27));
lean_inc(v___y_4139_);
v___x_4225_ = l_Lean_mkConst(v___x_4224_, v___y_4139_);
lean_inc_ref(v_type_3798_);
v___x_4226_ = l_Lean_Expr_app___override(v___x_4225_, v_type_3798_);
lean_inc_ref(v___x_4181_);
v___x_4227_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4226_, v___x_4181_, v___y_4146_);
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; 
lean_dec_ref_known(v___x_4227_, 1);
v___x_4228_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__0));
v___x_4229_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_4230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4230_, 0, v___x_4184_);
lean_ctor_set(v___x_4230_, 1, v___x_4213_);
lean_inc_ref(v___x_4230_);
v___x_4231_ = l_Lean_mkConst(v___x_4229_, v___x_4230_);
lean_inc_ref_n(v_type_3798_, 2);
lean_inc_ref(v___x_4231_);
v___x_4232_ = l_Lean_mkApp3(v___x_4231_, v___x_4187_, v_type_3798_, v_type_3798_);
lean_inc_ref(v___x_4191_);
v___x_4233_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4232_, v___x_4191_, v___y_4146_);
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_object* v___x_4234_; lean_object* v___x_4235_; 
lean_dec_ref_known(v___x_4233_, 1);
lean_inc_ref_n(v_type_3798_, 2);
v___x_4234_ = l_Lean_mkApp3(v___x_4231_, v___x_4192_, v_type_3798_, v_type_3798_);
lean_inc_ref(v___x_4196_);
v___x_4235_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4234_, v___x_4196_, v___y_4146_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_dec_ref_known(v___x_4235_, 1);
if (lean_obj_tag(v___y_4137_) == 1)
{
lean_object* v_val_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; 
v_val_4236_ = lean_ctor_get(v___y_4137_, 0);
lean_inc(v___y_4139_);
v___x_4237_ = l_Lean_mkConst(v___x_4131_, v___y_4139_);
lean_inc_ref(v_type_3798_);
v___x_4238_ = l_Lean_Expr_app___override(v___x_4237_, v_type_3798_);
lean_inc(v_val_4236_);
v___x_4239_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4238_, v_val_4236_, v___y_4146_);
if (lean_obj_tag(v___x_4239_) == 0)
{
lean_dec_ref_known(v___x_4239_, 1);
v___y_4080_ = v___y_4134_;
v___y_4081_ = v___x_4183_;
v___y_4082_ = v___x_4163_;
v___y_4083_ = v_noNatDivInstQ_x3f_4140_;
v___y_4084_ = v___x_4218_;
v___y_4085_ = v___x_4153_;
v___y_4086_ = v___x_4230_;
v___y_4087_ = v___x_4223_;
v___y_4088_ = v___y_4135_;
v___y_4089_ = v___x_4181_;
v___y_4090_ = v___y_4138_;
v___y_4091_ = v___y_4139_;
v___y_4092_ = v___x_4166_;
v___y_4093_ = v___x_4191_;
v___y_4094_ = v___x_4162_;
v___y_4095_ = v___x_4205_;
v___y_4096_ = v___y_4137_;
v___y_4097_ = v___x_4187_;
v___y_4098_ = v___x_4228_;
v___y_4099_ = v___y_4133_;
v___y_4100_ = v___y_4136_;
v___y_4101_ = v___x_4172_;
v___y_4102_ = v___x_4192_;
v___y_4103_ = v___x_4196_;
v___y_4104_ = v___x_4208_;
v___y_4105_ = v___x_4211_;
v___y_4106_ = v___x_4214_;
v___y_4107_ = v___x_4178_;
v___y_4108_ = v___y_4141_;
v___y_4109_ = v___y_4142_;
v___y_4110_ = v___y_4143_;
v___y_4111_ = v___y_4144_;
v___y_4112_ = v___y_4145_;
v___y_4113_ = v___y_4146_;
v___y_4114_ = v___y_4147_;
v___y_4115_ = v___y_4148_;
v___y_4116_ = v___y_4149_;
v___y_4117_ = v___y_4150_;
goto v___jp_4079_;
}
else
{
lean_object* v_a_4240_; lean_object* v___x_4242_; uint8_t v_isShared_4243_; uint8_t v_isSharedCheck_4247_; 
lean_dec_ref_known(v___y_4137_, 1);
lean_dec_ref_known(v___x_4230_, 2);
lean_dec_ref_known(v___x_4214_, 2);
lean_dec_ref(v___x_4196_);
lean_dec_ref(v___x_4191_);
lean_dec_ref(v___x_4181_);
lean_dec_ref(v___x_4178_);
lean_dec_ref(v___x_4172_);
lean_dec_ref(v___x_4166_);
lean_dec_ref(v___x_4162_);
lean_dec_ref(v___x_4153_);
lean_dec(v_noNatDivInstQ_x3f_4140_);
lean_dec(v___y_4139_);
lean_dec(v___y_4138_);
lean_dec(v___y_4136_);
lean_dec(v___y_4135_);
lean_dec(v___y_4134_);
lean_dec(v___y_4133_);
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_type_3798_);
v_a_4240_ = lean_ctor_get(v___x_4239_, 0);
v_isSharedCheck_4247_ = !lean_is_exclusive(v___x_4239_);
if (v_isSharedCheck_4247_ == 0)
{
v___x_4242_ = v___x_4239_;
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
else
{
lean_inc(v_a_4240_);
lean_dec(v___x_4239_);
v___x_4242_ = lean_box(0);
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
v_resetjp_4241_:
{
lean_object* v___x_4245_; 
if (v_isShared_4243_ == 0)
{
v___x_4245_ = v___x_4242_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v_a_4240_);
v___x_4245_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
return v___x_4245_;
}
}
}
}
else
{
v___y_4080_ = v___y_4134_;
v___y_4081_ = v___x_4183_;
v___y_4082_ = v___x_4163_;
v___y_4083_ = v_noNatDivInstQ_x3f_4140_;
v___y_4084_ = v___x_4218_;
v___y_4085_ = v___x_4153_;
v___y_4086_ = v___x_4230_;
v___y_4087_ = v___x_4223_;
v___y_4088_ = v___y_4135_;
v___y_4089_ = v___x_4181_;
v___y_4090_ = v___y_4138_;
v___y_4091_ = v___y_4139_;
v___y_4092_ = v___x_4166_;
v___y_4093_ = v___x_4191_;
v___y_4094_ = v___x_4162_;
v___y_4095_ = v___x_4205_;
v___y_4096_ = v___y_4137_;
v___y_4097_ = v___x_4187_;
v___y_4098_ = v___x_4228_;
v___y_4099_ = v___y_4133_;
v___y_4100_ = v___y_4136_;
v___y_4101_ = v___x_4172_;
v___y_4102_ = v___x_4192_;
v___y_4103_ = v___x_4196_;
v___y_4104_ = v___x_4208_;
v___y_4105_ = v___x_4211_;
v___y_4106_ = v___x_4214_;
v___y_4107_ = v___x_4178_;
v___y_4108_ = v___y_4141_;
v___y_4109_ = v___y_4142_;
v___y_4110_ = v___y_4143_;
v___y_4111_ = v___y_4144_;
v___y_4112_ = v___y_4145_;
v___y_4113_ = v___y_4146_;
v___y_4114_ = v___y_4147_;
v___y_4115_ = v___y_4148_;
v___y_4116_ = v___y_4149_;
v___y_4117_ = v___y_4150_;
goto v___jp_4079_;
}
}
else
{
lean_object* v_a_4248_; lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4255_; 
lean_dec_ref_known(v___x_4230_, 2);
lean_dec_ref_known(v___x_4214_, 2);
lean_dec_ref(v___x_4196_);
lean_dec_ref(v___x_4191_);
lean_dec_ref(v___x_4181_);
lean_dec_ref(v___x_4178_);
lean_dec_ref(v___x_4172_);
lean_dec_ref(v___x_4166_);
lean_dec_ref(v___x_4162_);
lean_dec_ref(v___x_4153_);
lean_dec(v_noNatDivInstQ_x3f_4140_);
lean_dec(v___y_4139_);
lean_dec(v___y_4138_);
lean_dec(v___y_4137_);
lean_dec(v___y_4136_);
lean_dec(v___y_4135_);
lean_dec(v___y_4134_);
lean_dec(v___y_4133_);
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_type_3798_);
v_a_4248_ = lean_ctor_get(v___x_4235_, 0);
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4250_ = v___x_4235_;
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
else
{
lean_inc(v_a_4248_);
lean_dec(v___x_4235_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
lean_object* v___x_4253_; 
if (v_isShared_4251_ == 0)
{
v___x_4253_ = v___x_4250_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v_a_4248_);
v___x_4253_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
return v___x_4253_;
}
}
}
}
else
{
lean_object* v_a_4256_; lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4263_; 
lean_dec_ref(v___x_4231_);
lean_dec_ref_known(v___x_4230_, 2);
lean_dec_ref_known(v___x_4214_, 2);
lean_dec_ref(v___x_4196_);
lean_dec_ref(v___x_4191_);
lean_dec_ref(v___x_4181_);
lean_dec_ref(v___x_4178_);
lean_dec_ref(v___x_4172_);
lean_dec_ref(v___x_4166_);
lean_dec_ref(v___x_4162_);
lean_dec_ref(v___x_4153_);
lean_dec(v_noNatDivInstQ_x3f_4140_);
lean_dec(v___y_4139_);
lean_dec(v___y_4138_);
lean_dec(v___y_4137_);
lean_dec(v___y_4136_);
lean_dec(v___y_4135_);
lean_dec(v___y_4134_);
lean_dec(v___y_4133_);
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_type_3798_);
v_a_4256_ = lean_ctor_get(v___x_4233_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v___x_4233_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4258_ = v___x_4233_;
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
else
{
lean_inc(v_a_4256_);
lean_dec(v___x_4233_);
v___x_4258_ = lean_box(0);
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
v_resetjp_4257_:
{
lean_object* v___x_4261_; 
if (v_isShared_4259_ == 0)
{
v___x_4261_ = v___x_4258_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v_a_4256_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
}
}
else
{
lean_object* v_a_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4271_; 
lean_dec_ref_known(v___x_4214_, 2);
lean_dec_ref_known(v___x_4213_, 2);
lean_dec_ref(v___x_4196_);
lean_dec_ref(v___x_4191_);
lean_dec_ref(v___x_4181_);
lean_dec_ref(v___x_4178_);
lean_dec_ref(v___x_4172_);
lean_dec_ref(v___x_4166_);
lean_dec_ref(v___x_4162_);
lean_dec_ref(v___x_4153_);
lean_dec(v_noNatDivInstQ_x3f_4140_);
lean_dec(v___y_4139_);
lean_dec(v___y_4138_);
lean_dec(v___y_4137_);
lean_dec(v___y_4136_);
lean_dec(v___y_4135_);
lean_dec(v___y_4134_);
lean_dec(v___y_4133_);
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_type_3798_);
v_a_4264_ = lean_ctor_get(v___x_4227_, 0);
v_isSharedCheck_4271_ = !lean_is_exclusive(v___x_4227_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4266_ = v___x_4227_;
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_a_4264_);
lean_dec(v___x_4227_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4269_; 
if (v_isShared_4267_ == 0)
{
v___x_4269_ = v___x_4266_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v_a_4264_);
v___x_4269_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
return v___x_4269_;
}
}
}
}
else
{
lean_object* v_a_4272_; lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4279_; 
lean_dec_ref_known(v___x_4214_, 2);
lean_dec_ref_known(v___x_4213_, 2);
lean_dec_ref(v___x_4196_);
lean_dec_ref(v___x_4191_);
lean_dec_ref(v___x_4181_);
lean_dec_ref(v___x_4178_);
lean_dec_ref(v___x_4172_);
lean_dec_ref(v___x_4166_);
lean_dec_ref(v___x_4162_);
lean_dec_ref(v___x_4153_);
lean_dec(v_noNatDivInstQ_x3f_4140_);
lean_dec(v___y_4139_);
lean_dec(v___y_4138_);
lean_dec(v___y_4137_);
lean_dec(v___y_4136_);
lean_dec(v___y_4135_);
lean_dec(v___y_4134_);
lean_dec(v___y_4133_);
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_type_3798_);
v_a_4272_ = lean_ctor_get(v___x_4222_, 0);
v_isSharedCheck_4279_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4279_ == 0)
{
v___x_4274_ = v___x_4222_;
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
else
{
lean_inc(v_a_4272_);
lean_dec(v___x_4222_);
v___x_4274_ = lean_box(0);
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
v_resetjp_4273_:
{
lean_object* v___x_4277_; 
if (v_isShared_4275_ == 0)
{
v___x_4277_ = v___x_4274_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v_a_4272_);
v___x_4277_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
return v___x_4277_;
}
}
}
}
else
{
lean_object* v_a_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4287_; 
lean_dec_ref_known(v___x_4214_, 2);
lean_dec_ref_known(v___x_4213_, 2);
lean_dec_ref(v___x_4196_);
lean_dec_ref(v___x_4191_);
lean_dec_ref(v___x_4181_);
lean_dec_ref(v___x_4178_);
lean_dec_ref(v___x_4172_);
lean_dec_ref(v___x_4166_);
lean_dec_ref(v___x_4162_);
lean_dec_ref(v___x_4153_);
lean_dec(v_noNatDivInstQ_x3f_4140_);
lean_dec(v___y_4139_);
lean_dec(v___y_4138_);
lean_dec(v___y_4137_);
lean_dec(v___y_4136_);
lean_dec(v___y_4135_);
lean_dec(v___y_4134_);
lean_dec(v___y_4133_);
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_type_3798_);
v_a_4280_ = lean_ctor_get(v___x_4217_, 0);
v_isSharedCheck_4287_ = !lean_is_exclusive(v___x_4217_);
if (v_isSharedCheck_4287_ == 0)
{
v___x_4282_ = v___x_4217_;
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_a_4280_);
lean_dec(v___x_4217_);
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
else
{
lean_object* v_a_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4295_; 
lean_dec_ref(v___x_4196_);
lean_dec_ref(v___x_4191_);
lean_dec_ref(v___x_4181_);
lean_dec_ref(v___x_4178_);
lean_dec_ref(v___x_4172_);
lean_dec_ref(v___x_4166_);
lean_dec_ref(v___x_4162_);
lean_dec_ref(v___x_4153_);
lean_dec(v_noNatDivInstQ_x3f_4140_);
lean_dec(v___y_4139_);
lean_dec(v___y_4138_);
lean_dec(v___y_4137_);
lean_dec(v___y_4136_);
lean_dec(v___y_4135_);
lean_dec(v___y_4134_);
lean_dec(v___y_4133_);
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_type_3798_);
v_a_4288_ = lean_ctor_get(v___x_4210_, 0);
v_isSharedCheck_4295_ = !lean_is_exclusive(v___x_4210_);
if (v_isSharedCheck_4295_ == 0)
{
v___x_4290_ = v___x_4210_;
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_a_4288_);
lean_dec(v___x_4210_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
lean_object* v___x_4293_; 
if (v_isShared_4291_ == 0)
{
v___x_4293_ = v___x_4290_;
goto v_reusejp_4292_;
}
else
{
lean_object* v_reuseFailAlloc_4294_; 
v_reuseFailAlloc_4294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4294_, 0, v_a_4288_);
v___x_4293_ = v_reuseFailAlloc_4294_;
goto v_reusejp_4292_;
}
v_reusejp_4292_:
{
return v___x_4293_;
}
}
}
}
else
{
lean_object* v_a_4296_; lean_object* v___x_4298_; uint8_t v_isShared_4299_; uint8_t v_isSharedCheck_4303_; 
lean_dec_ref(v___x_4196_);
lean_dec_ref(v___x_4191_);
lean_dec_ref(v___x_4181_);
lean_dec_ref(v___x_4178_);
lean_dec_ref(v___x_4172_);
lean_dec_ref(v___x_4166_);
lean_dec_ref(v___x_4162_);
lean_dec_ref(v___x_4153_);
lean_dec(v_noNatDivInstQ_x3f_4140_);
lean_dec(v___y_4139_);
lean_dec(v___y_4138_);
lean_dec(v___y_4137_);
lean_dec(v___y_4136_);
lean_dec(v___y_4135_);
lean_dec(v___y_4134_);
lean_dec(v___y_4133_);
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_type_3798_);
v_a_4296_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4303_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4303_ == 0)
{
v___x_4298_ = v___x_4204_;
v_isShared_4299_ = v_isSharedCheck_4303_;
goto v_resetjp_4297_;
}
else
{
lean_inc(v_a_4296_);
lean_dec(v___x_4204_);
v___x_4298_ = lean_box(0);
v_isShared_4299_ = v_isSharedCheck_4303_;
goto v_resetjp_4297_;
}
v_resetjp_4297_:
{
lean_object* v___x_4301_; 
if (v_isShared_4299_ == 0)
{
v___x_4301_ = v___x_4298_;
goto v_reusejp_4300_;
}
else
{
lean_object* v_reuseFailAlloc_4302_; 
v_reuseFailAlloc_4302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4302_, 0, v_a_4296_);
v___x_4301_ = v_reuseFailAlloc_4302_;
goto v_reusejp_4300_;
}
v_reusejp_4300_:
{
return v___x_4301_;
}
}
}
}
else
{
lean_object* v_a_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4311_; 
lean_dec_ref(v___x_4196_);
lean_dec_ref(v___x_4191_);
lean_dec_ref(v___x_4181_);
lean_dec_ref(v___x_4178_);
lean_dec_ref(v___x_4172_);
lean_dec_ref(v___x_4166_);
lean_dec_ref(v___x_4162_);
lean_dec_ref(v___x_4153_);
lean_dec(v_noNatDivInstQ_x3f_4140_);
lean_dec(v___y_4139_);
lean_dec(v___y_4138_);
lean_dec(v___y_4137_);
lean_dec(v___y_4136_);
lean_dec(v___y_4135_);
lean_dec(v___y_4134_);
lean_dec(v___y_4133_);
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_type_3798_);
v_a_4304_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4311_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4311_ == 0)
{
v___x_4306_ = v___x_4200_;
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_a_4304_);
lean_dec(v___x_4200_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
lean_object* v___x_4309_; 
if (v_isShared_4307_ == 0)
{
v___x_4309_ = v___x_4306_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v_a_4304_);
v___x_4309_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
return v___x_4309_;
}
}
}
}
v___jp_4312_:
{
lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4329_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__12));
v___x_4330_ = lean_box(0);
lean_inc(v_val_3817_);
v___x_4331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4331_, 0, v_val_3817_);
lean_ctor_set(v___x_4331_, 1, v___x_4330_);
lean_inc_ref(v___x_4331_);
v___x_4332_ = l_Lean_mkConst(v___x_4329_, v___x_4331_);
lean_inc_ref(v_base_3799_);
v___x_4333_ = l_Lean_Expr_app___override(v___x_4332_, v_base_3799_);
v___x_4334_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4333_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
if (lean_obj_tag(v___x_4334_) == 0)
{
lean_object* v_a_4335_; 
v_a_4335_ = lean_ctor_get(v___x_4334_, 0);
lean_inc(v_a_4335_);
lean_dec_ref_known(v___x_4334_, 1);
if (lean_obj_tag(v_a_4335_) == 1)
{
lean_object* v_val_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; 
v_val_4336_ = lean_ctor_get(v_a_4335_, 0);
lean_inc(v_val_4336_);
lean_dec_ref_known(v_a_4335_, 1);
v___x_4337_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__14));
lean_inc_ref(v___x_4331_);
v___x_4338_ = l_Lean_mkConst(v___x_4337_, v___x_4331_);
lean_inc_ref(v_base_3799_);
v___x_4339_ = l_Lean_mkAppB(v___x_4338_, v_base_3799_, v_val_4336_);
v___x_4340_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4339_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
if (lean_obj_tag(v___x_4340_) == 0)
{
lean_object* v_a_4341_; 
v_a_4341_ = lean_ctor_get(v___x_4340_, 0);
lean_inc(v_a_4341_);
lean_dec_ref_known(v___x_4340_, 1);
if (lean_obj_tag(v_a_4341_) == 1)
{
lean_object* v_val_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; 
v_val_4342_ = lean_ctor_get(v_a_4341_, 0);
lean_inc(v_val_4342_);
lean_dec_ref_known(v_a_4341_, 1);
v___x_4343_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3));
lean_inc_ref(v___x_4331_);
v___x_4344_ = l_Lean_mkConst(v___x_4343_, v___x_4331_);
lean_inc_ref(v_natModuleInst_3800_);
lean_inc_ref(v_base_3799_);
v___x_4345_ = l_Lean_mkAppB(v___x_4344_, v_base_3799_, v_natModuleInst_3800_);
v___x_4346_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4345_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
if (lean_obj_tag(v___x_4346_) == 0)
{
lean_object* v_a_4347_; 
v_a_4347_ = lean_ctor_get(v___x_4346_, 0);
lean_inc(v_a_4347_);
lean_dec_ref_known(v___x_4346_, 1);
if (lean_obj_tag(v_a_4347_) == 1)
{
lean_object* v_val_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4358_; 
v_val_4348_ = lean_ctor_get(v_a_4347_, 0);
v_isSharedCheck_4358_ = !lean_is_exclusive(v_a_4347_);
if (v_isSharedCheck_4358_ == 0)
{
v___x_4350_ = v_a_4347_;
v_isShared_4351_ = v_isSharedCheck_4358_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_val_4348_);
lean_dec(v_a_4347_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4358_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4356_; 
v___x_4352_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__16));
lean_inc_ref(v___x_4331_);
v___x_4353_ = l_Lean_mkConst(v___x_4352_, v___x_4331_);
lean_inc_ref(v_natModuleInst_3800_);
lean_inc_ref(v_base_3799_);
v___x_4354_ = l_Lean_mkApp4(v___x_4353_, v_base_3799_, v_natModuleInst_3800_, v_val_4342_, v_val_4348_);
if (v_isShared_4351_ == 0)
{
lean_ctor_set(v___x_4350_, 0, v___x_4354_);
v___x_4356_ = v___x_4350_;
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
v___y_4133_ = v_isLinearInstQ_x3f_4318_;
v___y_4134_ = v___y_4313_;
v___y_4135_ = v___y_4314_;
v___y_4136_ = v___y_4315_;
v___y_4137_ = v___y_4316_;
v___y_4138_ = v___y_4317_;
v___y_4139_ = v___x_4331_;
v_noNatDivInstQ_x3f_4140_ = v___x_4356_;
v___y_4141_ = v___y_4319_;
v___y_4142_ = v___y_4320_;
v___y_4143_ = v___y_4321_;
v___y_4144_ = v___y_4322_;
v___y_4145_ = v___y_4323_;
v___y_4146_ = v___y_4324_;
v___y_4147_ = v___y_4325_;
v___y_4148_ = v___y_4326_;
v___y_4149_ = v___y_4327_;
v___y_4150_ = v___y_4328_;
goto v___jp_4132_;
}
}
}
else
{
lean_object* v___x_4359_; 
lean_dec(v_a_4347_);
lean_dec(v_val_4342_);
v___x_4359_ = lean_box(0);
v___y_4133_ = v_isLinearInstQ_x3f_4318_;
v___y_4134_ = v___y_4313_;
v___y_4135_ = v___y_4314_;
v___y_4136_ = v___y_4315_;
v___y_4137_ = v___y_4316_;
v___y_4138_ = v___y_4317_;
v___y_4139_ = v___x_4331_;
v_noNatDivInstQ_x3f_4140_ = v___x_4359_;
v___y_4141_ = v___y_4319_;
v___y_4142_ = v___y_4320_;
v___y_4143_ = v___y_4321_;
v___y_4144_ = v___y_4322_;
v___y_4145_ = v___y_4323_;
v___y_4146_ = v___y_4324_;
v___y_4147_ = v___y_4325_;
v___y_4148_ = v___y_4326_;
v___y_4149_ = v___y_4327_;
v___y_4150_ = v___y_4328_;
goto v___jp_4132_;
}
}
else
{
lean_object* v_a_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4367_; 
lean_dec(v_val_4342_);
lean_dec_ref_known(v___x_4331_, 2);
lean_dec(v_isLinearInstQ_x3f_4318_);
lean_dec(v___y_4317_);
lean_dec(v___y_4316_);
lean_dec(v___y_4315_);
lean_dec(v___y_4314_);
lean_dec(v___y_4313_);
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_natModuleInst_3800_);
lean_dec_ref(v_base_3799_);
lean_dec_ref(v_type_3798_);
v_a_4360_ = lean_ctor_get(v___x_4346_, 0);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4346_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4362_ = v___x_4346_;
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_a_4360_);
lean_dec(v___x_4346_);
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
lean_object* v___x_4368_; 
lean_dec(v_a_4341_);
v___x_4368_ = lean_box(0);
v___y_4133_ = v_isLinearInstQ_x3f_4318_;
v___y_4134_ = v___y_4313_;
v___y_4135_ = v___y_4314_;
v___y_4136_ = v___y_4315_;
v___y_4137_ = v___y_4316_;
v___y_4138_ = v___y_4317_;
v___y_4139_ = v___x_4331_;
v_noNatDivInstQ_x3f_4140_ = v___x_4368_;
v___y_4141_ = v___y_4319_;
v___y_4142_ = v___y_4320_;
v___y_4143_ = v___y_4321_;
v___y_4144_ = v___y_4322_;
v___y_4145_ = v___y_4323_;
v___y_4146_ = v___y_4324_;
v___y_4147_ = v___y_4325_;
v___y_4148_ = v___y_4326_;
v___y_4149_ = v___y_4327_;
v___y_4150_ = v___y_4328_;
goto v___jp_4132_;
}
}
else
{
lean_object* v_a_4369_; lean_object* v___x_4371_; uint8_t v_isShared_4372_; uint8_t v_isSharedCheck_4376_; 
lean_dec_ref_known(v___x_4331_, 2);
lean_dec(v_isLinearInstQ_x3f_4318_);
lean_dec(v___y_4317_);
lean_dec(v___y_4316_);
lean_dec(v___y_4315_);
lean_dec(v___y_4314_);
lean_dec(v___y_4313_);
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_natModuleInst_3800_);
lean_dec_ref(v_base_3799_);
lean_dec_ref(v_type_3798_);
v_a_4369_ = lean_ctor_get(v___x_4340_, 0);
v_isSharedCheck_4376_ = !lean_is_exclusive(v___x_4340_);
if (v_isSharedCheck_4376_ == 0)
{
v___x_4371_ = v___x_4340_;
v_isShared_4372_ = v_isSharedCheck_4376_;
goto v_resetjp_4370_;
}
else
{
lean_inc(v_a_4369_);
lean_dec(v___x_4340_);
v___x_4371_ = lean_box(0);
v_isShared_4372_ = v_isSharedCheck_4376_;
goto v_resetjp_4370_;
}
v_resetjp_4370_:
{
lean_object* v___x_4374_; 
if (v_isShared_4372_ == 0)
{
v___x_4374_ = v___x_4371_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4375_; 
v_reuseFailAlloc_4375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4375_, 0, v_a_4369_);
v___x_4374_ = v_reuseFailAlloc_4375_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
return v___x_4374_;
}
}
}
}
else
{
lean_object* v___x_4377_; 
lean_dec(v_a_4335_);
v___x_4377_ = lean_box(0);
v___y_4133_ = v_isLinearInstQ_x3f_4318_;
v___y_4134_ = v___y_4313_;
v___y_4135_ = v___y_4314_;
v___y_4136_ = v___y_4315_;
v___y_4137_ = v___y_4316_;
v___y_4138_ = v___y_4317_;
v___y_4139_ = v___x_4331_;
v_noNatDivInstQ_x3f_4140_ = v___x_4377_;
v___y_4141_ = v___y_4319_;
v___y_4142_ = v___y_4320_;
v___y_4143_ = v___y_4321_;
v___y_4144_ = v___y_4322_;
v___y_4145_ = v___y_4323_;
v___y_4146_ = v___y_4324_;
v___y_4147_ = v___y_4325_;
v___y_4148_ = v___y_4326_;
v___y_4149_ = v___y_4327_;
v___y_4150_ = v___y_4328_;
goto v___jp_4132_;
}
}
else
{
lean_object* v_a_4378_; lean_object* v___x_4380_; uint8_t v_isShared_4381_; uint8_t v_isSharedCheck_4385_; 
lean_dec_ref_known(v___x_4331_, 2);
lean_dec(v_isLinearInstQ_x3f_4318_);
lean_dec(v___y_4317_);
lean_dec(v___y_4316_);
lean_dec(v___y_4315_);
lean_dec(v___y_4314_);
lean_dec(v___y_4313_);
lean_del_object(v___x_3819_);
lean_dec(v_val_3817_);
lean_dec_ref(v_natModuleInst_3800_);
lean_dec_ref(v_base_3799_);
lean_dec_ref(v_type_3798_);
v_a_4378_ = lean_ctor_get(v___x_4334_, 0);
v_isSharedCheck_4385_ = !lean_is_exclusive(v___x_4334_);
if (v_isSharedCheck_4385_ == 0)
{
v___x_4380_ = v___x_4334_;
v_isShared_4381_ = v_isSharedCheck_4385_;
goto v_resetjp_4379_;
}
else
{
lean_inc(v_a_4378_);
lean_dec(v___x_4334_);
v___x_4380_ = lean_box(0);
v_isShared_4381_ = v_isSharedCheck_4385_;
goto v_resetjp_4379_;
}
v_resetjp_4379_:
{
lean_object* v___x_4383_; 
if (v_isShared_4381_ == 0)
{
v___x_4383_ = v___x_4380_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v_a_4378_);
v___x_4383_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
return v___x_4383_;
}
}
}
}
}
}
else
{
lean_object* v___x_4546_; lean_object* v___x_4548_; 
lean_dec(v_a_3813_);
lean_dec_ref(v_natModuleInst_3800_);
lean_dec_ref(v_base_3799_);
lean_dec_ref(v_type_3798_);
v___x_4546_ = lean_box(0);
if (v_isShared_3816_ == 0)
{
lean_ctor_set(v___x_3815_, 0, v___x_4546_);
v___x_4548_ = v___x_3815_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v___x_4546_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
}
}
else
{
lean_object* v_a_4551_; lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4558_; 
lean_dec_ref(v_natModuleInst_3800_);
lean_dec_ref(v_base_3799_);
lean_dec_ref(v_type_3798_);
v_a_4551_ = lean_ctor_get(v___x_3812_, 0);
v_isSharedCheck_4558_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_4558_ == 0)
{
v___x_4553_ = v___x_3812_;
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
else
{
lean_inc(v_a_4551_);
lean_dec(v___x_3812_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
lean_object* v___x_4556_; 
if (v_isShared_4554_ == 0)
{
v___x_4556_ = v___x_4553_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v_a_4551_);
v___x_4556_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
return v___x_4556_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_3798_ = stack[0].m_obj;
lean_object* v_base_3799_ = stack[1].m_obj;
lean_object* v_natModuleInst_3800_ = stack[2].m_obj;
lean_object* v_a_3801_ = stack[3].m_obj;
lean_object* v_a_3802_ = stack[4].m_obj;
lean_object* v_a_3803_ = stack[5].m_obj;
lean_object* v_a_3804_ = stack[6].m_obj;
lean_object* v_a_3805_ = stack[7].m_obj;
lean_object* v_a_3806_ = stack[8].m_obj;
lean_object* v_a_3807_ = stack[9].m_obj;
lean_object* v_a_3808_ = stack[10].m_obj;
lean_object* v_a_3809_ = stack[11].m_obj;
lean_object* v_a_3810_ = stack[12].m_obj;
lean_object* v_res_4559_;
v_res_4559_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f(v_type_3798_, v_base_3799_, v_natModuleInst_3800_, v_a_3801_, v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
stack->m_obj
 = v_res_4559_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___boxed(lean_object* v_type_4560_, lean_object* v_base_4561_, lean_object* v_natModuleInst_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_){
_start:
{
lean_object* v_res_4574_; 
v_res_4574_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f(v_type_4560_, v_base_4561_, v_natModuleInst_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_, v_a_4572_);
lean_dec(v_a_4572_);
lean_dec_ref(v_a_4571_);
lean_dec(v_a_4570_);
lean_dec_ref(v_a_4569_);
lean_dec(v_a_4568_);
lean_dec_ref(v_a_4567_);
lean_dec(v_a_4566_);
lean_dec_ref(v_a_4565_);
lean_dec(v_a_4564_);
lean_dec(v_a_4563_);
return v_res_4574_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(lean_object* v_type_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_){
_start:
{
lean_object* v___x_4594_; lean_object* v___x_4595_; uint8_t v___x_4596_; 
v___x_4594_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1));
v___x_4595_ = lean_unsigned_to_nat(2u);
v___x_4596_ = l_Lean_Expr_isAppOfArity(v_type_4582_, v___x_4594_, v___x_4595_);
if (v___x_4596_ == 0)
{
lean_object* v___x_4597_; 
v___x_4597_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f(v_type_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
return v___x_4597_;
}
else
{
lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; 
v___x_4598_ = l_Lean_Expr_appFn_x21(v_type_4582_);
v___x_4599_ = l_Lean_Expr_appArg_x21(v___x_4598_);
lean_dec_ref(v___x_4598_);
v___x_4600_ = l_Lean_Expr_appArg_x21(v_type_4582_);
v___x_4601_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f(v_type_4582_, v___x_4599_, v___x_4600_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
return v___x_4601_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_4582_ = stack[0].m_obj;
lean_object* v_a_4583_ = stack[1].m_obj;
lean_object* v_a_4584_ = stack[2].m_obj;
lean_object* v_a_4585_ = stack[3].m_obj;
lean_object* v_a_4586_ = stack[4].m_obj;
lean_object* v_a_4587_ = stack[5].m_obj;
lean_object* v_a_4588_ = stack[6].m_obj;
lean_object* v_a_4589_ = stack[7].m_obj;
lean_object* v_a_4590_ = stack[8].m_obj;
lean_object* v_a_4591_ = stack[9].m_obj;
lean_object* v_a_4592_ = stack[10].m_obj;
lean_object* v_res_4602_;
v_res_4602_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(v_type_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
stack->m_obj
 = v_res_4602_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___boxed(lean_object* v_type_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_){
_start:
{
lean_object* v_res_4615_; 
v_res_4615_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(v_type_4603_, v_a_4604_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_);
lean_dec(v_a_4613_);
lean_dec_ref(v_a_4612_);
lean_dec(v_a_4611_);
lean_dec_ref(v_a_4610_);
lean_dec(v_a_4609_);
lean_dec_ref(v_a_4608_);
lean_dec(v_a_4607_);
lean_dec_ref(v_a_4606_);
lean_dec(v_a_4605_);
lean_dec(v_a_4604_);
return v_res_4615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___lam__0(lean_object* v_type_4616_, lean_object* v_a_4617_, lean_object* v_s_4618_){
_start:
{
lean_object* v_structs_4619_; lean_object* v_typeIdOf_4620_; lean_object* v_exprToStructId_4621_; lean_object* v_exprToStructIdEntries_4622_; lean_object* v_forbiddenNatModules_4623_; lean_object* v_natStructs_4624_; lean_object* v_natTypeIdOf_4625_; lean_object* v_exprToNatStructId_4626_; lean_object* v___x_4628_; uint8_t v_isShared_4629_; uint8_t v_isSharedCheck_4634_; 
v_structs_4619_ = lean_ctor_get(v_s_4618_, 0);
v_typeIdOf_4620_ = lean_ctor_get(v_s_4618_, 1);
v_exprToStructId_4621_ = lean_ctor_get(v_s_4618_, 2);
v_exprToStructIdEntries_4622_ = lean_ctor_get(v_s_4618_, 3);
v_forbiddenNatModules_4623_ = lean_ctor_get(v_s_4618_, 4);
v_natStructs_4624_ = lean_ctor_get(v_s_4618_, 5);
v_natTypeIdOf_4625_ = lean_ctor_get(v_s_4618_, 6);
v_exprToNatStructId_4626_ = lean_ctor_get(v_s_4618_, 7);
v_isSharedCheck_4634_ = !lean_is_exclusive(v_s_4618_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4628_ = v_s_4618_;
v_isShared_4629_ = v_isSharedCheck_4634_;
goto v_resetjp_4627_;
}
else
{
lean_inc(v_exprToNatStructId_4626_);
lean_inc(v_natTypeIdOf_4625_);
lean_inc(v_natStructs_4624_);
lean_inc(v_forbiddenNatModules_4623_);
lean_inc(v_exprToStructIdEntries_4622_);
lean_inc(v_exprToStructId_4621_);
lean_inc(v_typeIdOf_4620_);
lean_inc(v_structs_4619_);
lean_dec(v_s_4618_);
v___x_4628_ = lean_box(0);
v_isShared_4629_ = v_isSharedCheck_4634_;
goto v_resetjp_4627_;
}
v_resetjp_4627_:
{
lean_object* v___x_4630_; lean_object* v___x_4632_; 
v___x_4630_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_typeIdOf_4620_, v_type_4616_, v_a_4617_);
if (v_isShared_4629_ == 0)
{
lean_ctor_set(v___x_4628_, 1, v___x_4630_);
v___x_4632_ = v___x_4628_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v_structs_4619_);
lean_ctor_set(v_reuseFailAlloc_4633_, 1, v___x_4630_);
lean_ctor_set(v_reuseFailAlloc_4633_, 2, v_exprToStructId_4621_);
lean_ctor_set(v_reuseFailAlloc_4633_, 3, v_exprToStructIdEntries_4622_);
lean_ctor_set(v_reuseFailAlloc_4633_, 4, v_forbiddenNatModules_4623_);
lean_ctor_set(v_reuseFailAlloc_4633_, 5, v_natStructs_4624_);
lean_ctor_set(v_reuseFailAlloc_4633_, 6, v_natTypeIdOf_4625_);
lean_ctor_set(v_reuseFailAlloc_4633_, 7, v_exprToNatStructId_4626_);
v___x_4632_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
return v___x_4632_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_4635_, lean_object* v_vals_4636_, lean_object* v_i_4637_, lean_object* v_k_4638_){
_start:
{
lean_object* v___x_4639_; uint8_t v___x_4640_; 
v___x_4639_ = lean_array_get_size(v_keys_4635_);
v___x_4640_ = lean_nat_dec_lt(v_i_4637_, v___x_4639_);
if (v___x_4640_ == 0)
{
lean_object* v___x_4641_; 
lean_dec(v_i_4637_);
v___x_4641_ = lean_box(0);
return v___x_4641_;
}
else
{
lean_object* v_k_x27_4642_; size_t v___x_4643_; size_t v___x_4644_; uint8_t v___x_4645_; 
v_k_x27_4642_ = lean_array_fget_borrowed(v_keys_4635_, v_i_4637_);
v___x_4643_ = lean_ptr_addr(v_k_4638_);
v___x_4644_ = lean_ptr_addr(v_k_x27_4642_);
v___x_4645_ = lean_usize_dec_eq(v___x_4643_, v___x_4644_);
if (v___x_4645_ == 0)
{
lean_object* v___x_4646_; lean_object* v___x_4647_; 
v___x_4646_ = lean_unsigned_to_nat(1u);
v___x_4647_ = lean_nat_add(v_i_4637_, v___x_4646_);
lean_dec(v_i_4637_);
v_i_4637_ = v___x_4647_;
goto _start;
}
else
{
lean_object* v___x_4649_; lean_object* v___x_4650_; 
v___x_4649_ = lean_array_fget_borrowed(v_vals_4636_, v_i_4637_);
lean_dec(v_i_4637_);
lean_inc(v___x_4649_);
v___x_4650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4650_, 0, v___x_4649_);
return v___x_4650_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_4651_, lean_object* v_vals_4652_, lean_object* v_i_4653_, lean_object* v_k_4654_){
_start:
{
lean_object* v_res_4655_; 
v_res_4655_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4651_, v_vals_4652_, v_i_4653_, v_k_4654_);
lean_dec_ref(v_k_4654_);
lean_dec_ref(v_vals_4652_);
lean_dec_ref(v_keys_4651_);
return v_res_4655_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_4656_, size_t v_x_4657_, lean_object* v_x_4658_){
_start:
{
if (lean_obj_tag(v_x_4656_) == 0)
{
lean_object* v_es_4659_; lean_object* v___x_4660_; size_t v___x_4661_; size_t v___x_4662_; lean_object* v_j_4663_; lean_object* v___x_4664_; 
v_es_4659_ = lean_ctor_get(v_x_4656_, 0);
v___x_4660_ = lean_box(2);
v___x_4661_ = ((size_t)31ULL);
v___x_4662_ = lean_usize_land(v_x_4657_, v___x_4661_);
v_j_4663_ = lean_usize_to_nat(v___x_4662_);
v___x_4664_ = lean_array_get_borrowed(v___x_4660_, v_es_4659_, v_j_4663_);
lean_dec(v_j_4663_);
switch(lean_obj_tag(v___x_4664_))
{
case 0:
{
lean_object* v_key_4665_; lean_object* v_val_4666_; size_t v___x_4667_; size_t v___x_4668_; uint8_t v___x_4669_; 
v_key_4665_ = lean_ctor_get(v___x_4664_, 0);
v_val_4666_ = lean_ctor_get(v___x_4664_, 1);
v___x_4667_ = lean_ptr_addr(v_x_4658_);
v___x_4668_ = lean_ptr_addr(v_key_4665_);
v___x_4669_ = lean_usize_dec_eq(v___x_4667_, v___x_4668_);
if (v___x_4669_ == 0)
{
lean_object* v___x_4670_; 
v___x_4670_ = lean_box(0);
return v___x_4670_;
}
else
{
lean_object* v___x_4671_; 
lean_inc(v_val_4666_);
v___x_4671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4671_, 0, v_val_4666_);
return v___x_4671_;
}
}
case 1:
{
lean_object* v_node_4672_; size_t v___x_4673_; size_t v___x_4674_; 
v_node_4672_ = lean_ctor_get(v___x_4664_, 0);
v___x_4673_ = ((size_t)5ULL);
v___x_4674_ = lean_usize_shift_right(v_x_4657_, v___x_4673_);
v_x_4656_ = v_node_4672_;
v_x_4657_ = v___x_4674_;
goto _start;
}
default: 
{
lean_object* v___x_4676_; 
v___x_4676_ = lean_box(0);
return v___x_4676_;
}
}
}
else
{
lean_object* v_ks_4677_; lean_object* v_vs_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; 
v_ks_4677_ = lean_ctor_get(v_x_4656_, 0);
v_vs_4678_ = lean_ctor_get(v_x_4656_, 1);
v___x_4679_ = lean_unsigned_to_nat(0u);
v___x_4680_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_4677_, v_vs_4678_, v___x_4679_, v_x_4658_);
return v___x_4680_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4656_ = stack[0].m_obj;
size_t v_x_4657_ = stack[1].m_num;
lean_object* v_x_4658_ = stack[2].m_obj;
lean_object* v_res_4681_;
v_res_4681_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_4656_, v_x_4657_, v_x_4658_);
stack->m_obj
 = v_res_4681_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_4682_, lean_object* v_x_4683_, lean_object* v_x_4684_){
_start:
{
size_t v_x_6761__boxed_4685_; lean_object* v_res_4686_; 
v_x_6761__boxed_4685_ = lean_unbox_usize(v_x_4683_);
lean_dec(v_x_4683_);
v_res_4686_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_4682_, v_x_6761__boxed_4685_, v_x_4684_);
lean_dec_ref(v_x_4684_);
lean_dec_ref(v_x_4682_);
return v_res_4686_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(lean_object* v_x_4687_, lean_object* v_x_4688_){
_start:
{
size_t v___x_4689_; size_t v___x_4690_; size_t v___x_4691_; uint64_t v___x_4692_; size_t v___x_4693_; lean_object* v___x_4694_; 
v___x_4689_ = lean_ptr_addr(v_x_4688_);
v___x_4690_ = ((size_t)3ULL);
v___x_4691_ = lean_usize_shift_right(v___x_4689_, v___x_4690_);
v___x_4692_ = lean_usize_to_uint64(v___x_4691_);
v___x_4693_ = lean_uint64_to_usize(v___x_4692_);
v___x_4694_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_4687_, v___x_4693_, v_x_4688_);
return v___x_4694_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_4695_, lean_object* v_x_4696_){
_start:
{
lean_object* v_res_4697_; 
v_res_4697_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_x_4695_, v_x_4696_);
lean_dec_ref(v_x_4696_);
lean_dec_ref(v_x_4695_);
return v_res_4697_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(lean_object* v_type_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_){
_start:
{
lean_object* v___x_4710_; 
v___x_4710_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4701_);
if (lean_obj_tag(v___x_4710_) == 0)
{
lean_object* v_a_4711_; lean_object* v___x_4713_; uint8_t v_isShared_4714_; uint8_t v_isSharedCheck_4780_; 
v_a_4711_ = lean_ctor_get(v___x_4710_, 0);
v_isSharedCheck_4780_ = !lean_is_exclusive(v___x_4710_);
if (v_isSharedCheck_4780_ == 0)
{
v___x_4713_ = v___x_4710_;
v_isShared_4714_ = v_isSharedCheck_4780_;
goto v_resetjp_4712_;
}
else
{
lean_inc(v_a_4711_);
lean_dec(v___x_4710_);
v___x_4713_ = lean_box(0);
v_isShared_4714_ = v_isSharedCheck_4780_;
goto v_resetjp_4712_;
}
v_resetjp_4712_:
{
uint8_t v_linarith_4715_; 
v_linarith_4715_ = lean_ctor_get_uint8(v_a_4711_, sizeof(void*)*14 + 22);
lean_dec(v_a_4711_);
if (v_linarith_4715_ == 0)
{
lean_object* v___x_4716_; lean_object* v___x_4718_; 
lean_dec_ref(v_type_4698_);
v___x_4716_ = lean_box(0);
if (v_isShared_4714_ == 0)
{
lean_ctor_set(v___x_4713_, 0, v___x_4716_);
v___x_4718_ = v___x_4713_;
goto v_reusejp_4717_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v___x_4716_);
v___x_4718_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4717_;
}
v_reusejp_4717_:
{
return v___x_4718_;
}
}
else
{
lean_object* v___x_4720_; 
lean_del_object(v___x_4713_);
lean_inc_ref(v_type_4698_);
v___x_4720_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___redArg(v_type_4698_, v_a_4701_, v_a_4706_);
if (lean_obj_tag(v___x_4720_) == 0)
{
lean_object* v_a_4721_; lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4771_; 
v_a_4721_ = lean_ctor_get(v___x_4720_, 0);
v_isSharedCheck_4771_ = !lean_is_exclusive(v___x_4720_);
if (v_isSharedCheck_4771_ == 0)
{
v___x_4723_ = v___x_4720_;
v_isShared_4724_ = v_isSharedCheck_4771_;
goto v_resetjp_4722_;
}
else
{
lean_inc(v_a_4721_);
lean_dec(v___x_4720_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4771_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
uint8_t v___x_4725_; 
v___x_4725_ = lean_unbox(v_a_4721_);
lean_dec(v_a_4721_);
if (v___x_4725_ == 0)
{
lean_object* v___x_4726_; 
lean_del_object(v___x_4723_);
v___x_4726_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_4699_, v_a_4707_);
if (lean_obj_tag(v___x_4726_) == 0)
{
lean_object* v_a_4727_; lean_object* v___x_4729_; uint8_t v_isShared_4730_; uint8_t v_isSharedCheck_4758_; 
v_a_4727_ = lean_ctor_get(v___x_4726_, 0);
v_isSharedCheck_4758_ = !lean_is_exclusive(v___x_4726_);
if (v_isSharedCheck_4758_ == 0)
{
v___x_4729_ = v___x_4726_;
v_isShared_4730_ = v_isSharedCheck_4758_;
goto v_resetjp_4728_;
}
else
{
lean_inc(v_a_4727_);
lean_dec(v___x_4726_);
v___x_4729_ = lean_box(0);
v_isShared_4730_ = v_isSharedCheck_4758_;
goto v_resetjp_4728_;
}
v_resetjp_4728_:
{
lean_object* v_typeIdOf_4731_; lean_object* v___x_4732_; 
v_typeIdOf_4731_ = lean_ctor_get(v_a_4727_, 1);
lean_inc_ref(v_typeIdOf_4731_);
lean_dec(v_a_4727_);
v___x_4732_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_typeIdOf_4731_, v_type_4698_);
lean_dec_ref(v_typeIdOf_4731_);
if (lean_obj_tag(v___x_4732_) == 1)
{
lean_object* v_val_4733_; lean_object* v___x_4735_; 
lean_dec_ref(v_type_4698_);
v_val_4733_ = lean_ctor_get(v___x_4732_, 0);
lean_inc(v_val_4733_);
lean_dec_ref_known(v___x_4732_, 1);
if (v_isShared_4730_ == 0)
{
lean_ctor_set(v___x_4729_, 0, v_val_4733_);
v___x_4735_ = v___x_4729_;
goto v_reusejp_4734_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v_val_4733_);
v___x_4735_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4734_;
}
v_reusejp_4734_:
{
return v___x_4735_;
}
}
else
{
lean_object* v___x_4737_; 
lean_dec(v___x_4732_);
lean_del_object(v___x_4729_);
lean_inc_ref(v_type_4698_);
v___x_4737_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(v_type_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_);
if (lean_obj_tag(v___x_4737_) == 0)
{
lean_object* v_a_4738_; lean_object* v___f_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; 
v_a_4738_ = lean_ctor_get(v___x_4737_, 0);
lean_inc_n(v_a_4738_, 2);
lean_dec_ref_known(v___x_4737_, 1);
v___f_4739_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_4739_, 0, v_type_4698_);
lean_closure_set(v___f_4739_, 1, v_a_4738_);
v___x_4740_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4741_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4740_, v___f_4739_, v_a_4699_);
if (lean_obj_tag(v___x_4741_) == 0)
{
lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4748_; 
v_isSharedCheck_4748_ = !lean_is_exclusive(v___x_4741_);
if (v_isSharedCheck_4748_ == 0)
{
lean_object* v_unused_4749_; 
v_unused_4749_ = lean_ctor_get(v___x_4741_, 0);
lean_dec(v_unused_4749_);
v___x_4743_ = v___x_4741_;
v_isShared_4744_ = v_isSharedCheck_4748_;
goto v_resetjp_4742_;
}
else
{
lean_dec(v___x_4741_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4748_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v___x_4746_; 
if (v_isShared_4744_ == 0)
{
lean_ctor_set(v___x_4743_, 0, v_a_4738_);
v___x_4746_ = v___x_4743_;
goto v_reusejp_4745_;
}
else
{
lean_object* v_reuseFailAlloc_4747_; 
v_reuseFailAlloc_4747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4747_, 0, v_a_4738_);
v___x_4746_ = v_reuseFailAlloc_4747_;
goto v_reusejp_4745_;
}
v_reusejp_4745_:
{
return v___x_4746_;
}
}
}
else
{
lean_object* v_a_4750_; lean_object* v___x_4752_; uint8_t v_isShared_4753_; uint8_t v_isSharedCheck_4757_; 
lean_dec(v_a_4738_);
v_a_4750_ = lean_ctor_get(v___x_4741_, 0);
v_isSharedCheck_4757_ = !lean_is_exclusive(v___x_4741_);
if (v_isSharedCheck_4757_ == 0)
{
v___x_4752_ = v___x_4741_;
v_isShared_4753_ = v_isSharedCheck_4757_;
goto v_resetjp_4751_;
}
else
{
lean_inc(v_a_4750_);
lean_dec(v___x_4741_);
v___x_4752_ = lean_box(0);
v_isShared_4753_ = v_isSharedCheck_4757_;
goto v_resetjp_4751_;
}
v_resetjp_4751_:
{
lean_object* v___x_4755_; 
if (v_isShared_4753_ == 0)
{
v___x_4755_ = v___x_4752_;
goto v_reusejp_4754_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v_a_4750_);
v___x_4755_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4754_;
}
v_reusejp_4754_:
{
return v___x_4755_;
}
}
}
}
else
{
lean_dec_ref(v_type_4698_);
return v___x_4737_;
}
}
}
}
else
{
lean_object* v_a_4759_; lean_object* v___x_4761_; uint8_t v_isShared_4762_; uint8_t v_isSharedCheck_4766_; 
lean_dec_ref(v_type_4698_);
v_a_4759_ = lean_ctor_get(v___x_4726_, 0);
v_isSharedCheck_4766_ = !lean_is_exclusive(v___x_4726_);
if (v_isSharedCheck_4766_ == 0)
{
v___x_4761_ = v___x_4726_;
v_isShared_4762_ = v_isSharedCheck_4766_;
goto v_resetjp_4760_;
}
else
{
lean_inc(v_a_4759_);
lean_dec(v___x_4726_);
v___x_4761_ = lean_box(0);
v_isShared_4762_ = v_isSharedCheck_4766_;
goto v_resetjp_4760_;
}
v_resetjp_4760_:
{
lean_object* v___x_4764_; 
if (v_isShared_4762_ == 0)
{
v___x_4764_ = v___x_4761_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v_a_4759_);
v___x_4764_ = v_reuseFailAlloc_4765_;
goto v_reusejp_4763_;
}
v_reusejp_4763_:
{
return v___x_4764_;
}
}
}
}
else
{
lean_object* v___x_4767_; lean_object* v___x_4769_; 
lean_dec_ref(v_type_4698_);
v___x_4767_ = lean_box(0);
if (v_isShared_4724_ == 0)
{
lean_ctor_set(v___x_4723_, 0, v___x_4767_);
v___x_4769_ = v___x_4723_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4770_; 
v_reuseFailAlloc_4770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4770_, 0, v___x_4767_);
v___x_4769_ = v_reuseFailAlloc_4770_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
return v___x_4769_;
}
}
}
}
else
{
lean_object* v_a_4772_; lean_object* v___x_4774_; uint8_t v_isShared_4775_; uint8_t v_isSharedCheck_4779_; 
lean_dec_ref(v_type_4698_);
v_a_4772_ = lean_ctor_get(v___x_4720_, 0);
v_isSharedCheck_4779_ = !lean_is_exclusive(v___x_4720_);
if (v_isSharedCheck_4779_ == 0)
{
v___x_4774_ = v___x_4720_;
v_isShared_4775_ = v_isSharedCheck_4779_;
goto v_resetjp_4773_;
}
else
{
lean_inc(v_a_4772_);
lean_dec(v___x_4720_);
v___x_4774_ = lean_box(0);
v_isShared_4775_ = v_isSharedCheck_4779_;
goto v_resetjp_4773_;
}
v_resetjp_4773_:
{
lean_object* v___x_4777_; 
if (v_isShared_4775_ == 0)
{
v___x_4777_ = v___x_4774_;
goto v_reusejp_4776_;
}
else
{
lean_object* v_reuseFailAlloc_4778_; 
v_reuseFailAlloc_4778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4778_, 0, v_a_4772_);
v___x_4777_ = v_reuseFailAlloc_4778_;
goto v_reusejp_4776_;
}
v_reusejp_4776_:
{
return v___x_4777_;
}
}
}
}
}
}
else
{
lean_object* v_a_4781_; lean_object* v___x_4783_; uint8_t v_isShared_4784_; uint8_t v_isSharedCheck_4788_; 
lean_dec_ref(v_type_4698_);
v_a_4781_ = lean_ctor_get(v___x_4710_, 0);
v_isSharedCheck_4788_ = !lean_is_exclusive(v___x_4710_);
if (v_isSharedCheck_4788_ == 0)
{
v___x_4783_ = v___x_4710_;
v_isShared_4784_ = v_isSharedCheck_4788_;
goto v_resetjp_4782_;
}
else
{
lean_inc(v_a_4781_);
lean_dec(v___x_4710_);
v___x_4783_ = lean_box(0);
v_isShared_4784_ = v_isSharedCheck_4788_;
goto v_resetjp_4782_;
}
v_resetjp_4782_:
{
lean_object* v___x_4786_; 
if (v_isShared_4784_ == 0)
{
v___x_4786_ = v___x_4783_;
goto v_reusejp_4785_;
}
else
{
lean_object* v_reuseFailAlloc_4787_; 
v_reuseFailAlloc_4787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4787_, 0, v_a_4781_);
v___x_4786_ = v_reuseFailAlloc_4787_;
goto v_reusejp_4785_;
}
v_reusejp_4785_:
{
return v___x_4786_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_4698_ = stack[0].m_obj;
lean_object* v_a_4699_ = stack[1].m_obj;
lean_object* v_a_4700_ = stack[2].m_obj;
lean_object* v_a_4701_ = stack[3].m_obj;
lean_object* v_a_4702_ = stack[4].m_obj;
lean_object* v_a_4703_ = stack[5].m_obj;
lean_object* v_a_4704_ = stack[6].m_obj;
lean_object* v_a_4705_ = stack[7].m_obj;
lean_object* v_a_4706_ = stack[8].m_obj;
lean_object* v_a_4707_ = stack[9].m_obj;
lean_object* v_a_4708_ = stack[10].m_obj;
lean_object* v_res_4789_;
v_res_4789_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v_type_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_);
stack->m_obj
 = v_res_4789_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___boxed(lean_object* v_type_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_){
_start:
{
lean_object* v_res_4802_; 
v_res_4802_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v_type_4790_, v_a_4791_, v_a_4792_, v_a_4793_, v_a_4794_, v_a_4795_, v_a_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_);
lean_dec(v_a_4800_);
lean_dec_ref(v_a_4799_);
lean_dec(v_a_4798_);
lean_dec_ref(v_a_4797_);
lean_dec(v_a_4796_);
lean_dec_ref(v_a_4795_);
lean_dec(v_a_4794_);
lean_dec_ref(v_a_4793_);
lean_dec(v_a_4792_);
lean_dec(v_a_4791_);
return v_res_4802_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0(lean_object* v_00_u03b2_4803_, lean_object* v_x_4804_, lean_object* v_x_4805_){
_start:
{
lean_object* v___x_4806_; 
v___x_4806_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_x_4804_, v_x_4805_);
return v___x_4806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_4807_, lean_object* v_x_4808_, lean_object* v_x_4809_){
_start:
{
lean_object* v_res_4810_; 
v_res_4810_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0(v_00_u03b2_4807_, v_x_4808_, v_x_4809_);
lean_dec_ref(v_x_4809_);
lean_dec_ref(v_x_4808_);
return v_res_4810_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_4811_, lean_object* v_x_4812_, size_t v_x_4813_, lean_object* v_x_4814_){
_start:
{
lean_object* v___x_4815_; 
v___x_4815_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_4812_, v_x_4813_, v_x_4814_);
return v___x_4815_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4812_ = stack[1].m_obj;
size_t v_x_4813_ = stack[2].m_num;
lean_object* v_x_4814_ = stack[3].m_obj;
lean_object* v_res_4816_;
v_res_4816_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0(lean_box(0), v_x_4812_, v_x_4813_, v_x_4814_);
stack->m_obj
 = v_res_4816_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4817_, lean_object* v_x_4818_, lean_object* v_x_4819_, lean_object* v_x_4820_){
_start:
{
size_t v_x_7118__boxed_4821_; lean_object* v_res_4822_; 
v_x_7118__boxed_4821_ = lean_unbox_usize(v_x_4819_);
lean_dec(v_x_4819_);
v_res_4822_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0(v_00_u03b2_4817_, v_x_4818_, v_x_7118__boxed_4821_, v_x_4820_);
lean_dec_ref(v_x_4820_);
lean_dec_ref(v_x_4818_);
return v_res_4822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4823_, lean_object* v_keys_4824_, lean_object* v_vals_4825_, lean_object* v_heq_4826_, lean_object* v_i_4827_, lean_object* v_k_4828_){
_start:
{
lean_object* v___x_4829_; 
v___x_4829_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4824_, v_vals_4825_, v_i_4827_, v_k_4828_);
return v___x_4829_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4830_, lean_object* v_keys_4831_, lean_object* v_vals_4832_, lean_object* v_heq_4833_, lean_object* v_i_4834_, lean_object* v_k_4835_){
_start:
{
lean_object* v_res_4836_; 
v_res_4836_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_4830_, v_keys_4831_, v_vals_4832_, v_heq_4833_, v_i_4834_, v_k_4835_);
lean_dec_ref(v_k_4835_);
lean_dec_ref(v_vals_4832_);
lean_dec_ref(v_keys_4831_);
return v_res_4836_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(lean_object* v_u_4837_, lean_object* v_type_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_){
_start:
{
lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; 
v___x_4845_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1));
v___x_4846_ = lean_box(0);
v___x_4847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4847_, 0, v_u_4837_);
lean_ctor_set(v___x_4847_, 1, v___x_4846_);
v___x_4848_ = l_Lean_mkConst(v___x_4845_, v___x_4847_);
v___x_4849_ = l_Lean_Expr_app___override(v___x_4848_, v_type_4838_);
v___x_4850_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4849_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_, v_a_4843_);
return v___x_4850_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_4837_ = stack[0].m_obj;
lean_object* v_type_4838_ = stack[1].m_obj;
lean_object* v_a_4839_ = stack[2].m_obj;
lean_object* v_a_4840_ = stack[3].m_obj;
lean_object* v_a_4841_ = stack[4].m_obj;
lean_object* v_a_4842_ = stack[5].m_obj;
lean_object* v_a_4843_ = stack[6].m_obj;
lean_object* v_res_4851_;
v_res_4851_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_u_4837_, v_type_4838_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_, v_a_4843_);
stack->m_obj
 = v_res_4851_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg___boxed(lean_object* v_u_4852_, lean_object* v_type_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_){
_start:
{
lean_object* v_res_4860_; 
v_res_4860_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_u_4852_, v_type_4853_, v_a_4854_, v_a_4855_, v_a_4856_, v_a_4857_, v_a_4858_);
lean_dec(v_a_4858_);
lean_dec_ref(v_a_4857_);
lean_dec(v_a_4856_);
lean_dec_ref(v_a_4855_);
lean_dec(v_a_4854_);
return v_res_4860_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f(lean_object* v_u_4861_, lean_object* v_type_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_, lean_object* v_a_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_){
_start:
{
lean_object* v___x_4874_; 
v___x_4874_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_u_4861_, v_type_4862_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_);
return v___x_4874_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_4861_ = stack[0].m_obj;
lean_object* v_type_4862_ = stack[1].m_obj;
lean_object* v_a_4863_ = stack[2].m_obj;
lean_object* v_a_4864_ = stack[3].m_obj;
lean_object* v_a_4865_ = stack[4].m_obj;
lean_object* v_a_4866_ = stack[5].m_obj;
lean_object* v_a_4867_ = stack[6].m_obj;
lean_object* v_a_4868_ = stack[7].m_obj;
lean_object* v_a_4869_ = stack[8].m_obj;
lean_object* v_a_4870_ = stack[9].m_obj;
lean_object* v_a_4871_ = stack[10].m_obj;
lean_object* v_a_4872_ = stack[11].m_obj;
lean_object* v_res_4875_;
v_res_4875_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f(v_u_4861_, v_type_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_);
stack->m_obj
 = v_res_4875_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___boxed(lean_object* v_u_4876_, lean_object* v_type_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_, lean_object* v_a_4886_, lean_object* v_a_4887_, lean_object* v_a_4888_){
_start:
{
lean_object* v_res_4889_; 
v_res_4889_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f(v_u_4876_, v_type_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_);
lean_dec(v_a_4887_);
lean_dec_ref(v_a_4886_);
lean_dec(v_a_4885_);
lean_dec_ref(v_a_4884_);
lean_dec(v_a_4883_);
lean_dec_ref(v_a_4882_);
lean_dec(v_a_4881_);
lean_dec_ref(v_a_4880_);
lean_dec(v_a_4879_);
lean_dec(v_a_4878_);
return v_res_4889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___lam__0(lean_object* v___x_4890_, lean_object* v_s_4891_){
_start:
{
lean_object* v_structs_4892_; lean_object* v_typeIdOf_4893_; lean_object* v_exprToStructId_4894_; lean_object* v_exprToStructIdEntries_4895_; lean_object* v_forbiddenNatModules_4896_; lean_object* v_natStructs_4897_; lean_object* v_natTypeIdOf_4898_; lean_object* v_exprToNatStructId_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4907_; 
v_structs_4892_ = lean_ctor_get(v_s_4891_, 0);
v_typeIdOf_4893_ = lean_ctor_get(v_s_4891_, 1);
v_exprToStructId_4894_ = lean_ctor_get(v_s_4891_, 2);
v_exprToStructIdEntries_4895_ = lean_ctor_get(v_s_4891_, 3);
v_forbiddenNatModules_4896_ = lean_ctor_get(v_s_4891_, 4);
v_natStructs_4897_ = lean_ctor_get(v_s_4891_, 5);
v_natTypeIdOf_4898_ = lean_ctor_get(v_s_4891_, 6);
v_exprToNatStructId_4899_ = lean_ctor_get(v_s_4891_, 7);
v_isSharedCheck_4907_ = !lean_is_exclusive(v_s_4891_);
if (v_isSharedCheck_4907_ == 0)
{
v___x_4901_ = v_s_4891_;
v_isShared_4902_ = v_isSharedCheck_4907_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_exprToNatStructId_4899_);
lean_inc(v_natTypeIdOf_4898_);
lean_inc(v_natStructs_4897_);
lean_inc(v_forbiddenNatModules_4896_);
lean_inc(v_exprToStructIdEntries_4895_);
lean_inc(v_exprToStructId_4894_);
lean_inc(v_typeIdOf_4893_);
lean_inc(v_structs_4892_);
lean_dec(v_s_4891_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4907_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
lean_object* v___x_4903_; lean_object* v___x_4905_; 
v___x_4903_ = lean_array_push(v_natStructs_4897_, v___x_4890_);
if (v_isShared_4902_ == 0)
{
lean_ctor_set(v___x_4901_, 5, v___x_4903_);
v___x_4905_ = v___x_4901_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v_structs_4892_);
lean_ctor_set(v_reuseFailAlloc_4906_, 1, v_typeIdOf_4893_);
lean_ctor_set(v_reuseFailAlloc_4906_, 2, v_exprToStructId_4894_);
lean_ctor_set(v_reuseFailAlloc_4906_, 3, v_exprToStructIdEntries_4895_);
lean_ctor_set(v_reuseFailAlloc_4906_, 4, v_forbiddenNatModules_4896_);
lean_ctor_set(v_reuseFailAlloc_4906_, 5, v___x_4903_);
lean_ctor_set(v_reuseFailAlloc_4906_, 6, v_natTypeIdOf_4898_);
lean_ctor_set(v_reuseFailAlloc_4906_, 7, v_exprToNatStructId_4899_);
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
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(lean_object* v_msg_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_){
_start:
{
lean_object* v_ref_4914_; lean_object* v___x_4915_; lean_object* v_a_4916_; lean_object* v___x_4918_; uint8_t v_isShared_4919_; uint8_t v_isSharedCheck_4924_; 
v_ref_4914_ = lean_ctor_get(v___y_4911_, 2);
v___x_4915_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(v_msg_4908_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_);
v_a_4916_ = lean_ctor_get(v___x_4915_, 0);
v_isSharedCheck_4924_ = !lean_is_exclusive(v___x_4915_);
if (v_isSharedCheck_4924_ == 0)
{
v___x_4918_ = v___x_4915_;
v_isShared_4919_ = v_isSharedCheck_4924_;
goto v_resetjp_4917_;
}
else
{
lean_inc(v_a_4916_);
lean_dec(v___x_4915_);
v___x_4918_ = lean_box(0);
v_isShared_4919_ = v_isSharedCheck_4924_;
goto v_resetjp_4917_;
}
v_resetjp_4917_:
{
lean_object* v___x_4920_; lean_object* v___x_4922_; 
lean_inc(v_ref_4914_);
v___x_4920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4920_, 0, v_ref_4914_);
lean_ctor_set(v___x_4920_, 1, v_a_4916_);
if (v_isShared_4919_ == 0)
{
lean_ctor_set_tag(v___x_4918_, 1);
lean_ctor_set(v___x_4918_, 0, v___x_4920_);
v___x_4922_ = v___x_4918_;
goto v_reusejp_4921_;
}
else
{
lean_object* v_reuseFailAlloc_4923_; 
v_reuseFailAlloc_4923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4923_, 0, v___x_4920_);
v___x_4922_ = v_reuseFailAlloc_4923_;
goto v_reusejp_4921_;
}
v_reusejp_4921_:
{
return v___x_4922_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4908_ = stack[0].m_obj;
lean_object* v___y_4909_ = stack[1].m_obj;
lean_object* v___y_4910_ = stack[2].m_obj;
lean_object* v___y_4911_ = stack[3].m_obj;
lean_object* v___y_4912_ = stack[4].m_obj;
lean_object* v_res_4925_;
v_res_4925_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v_msg_4908_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_);
stack->m_obj
 = v_res_4925_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg___boxed(lean_object* v_msg_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_){
_start:
{
lean_object* v_res_4932_; 
v_res_4932_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v_msg_4926_, v___y_4927_, v___y_4928_, v___y_4929_, v___y_4930_);
lean_dec(v___y_4930_);
lean_dec_ref(v___y_4929_);
lean_dec(v___y_4928_);
lean_dec_ref(v___y_4927_);
return v_res_4932_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5(void){
_start:
{
lean_object* v___x_4945_; lean_object* v___x_4946_; 
v___x_4945_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5);
v___x_4946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4946_, 0, v___x_4945_);
return v___x_4946_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7(void){
_start:
{
lean_object* v___x_4948_; lean_object* v___x_4949_; 
v___x_4948_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6));
v___x_4949_ = l_Lean_stringToMessageData(v___x_4948_);
return v___x_4949_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(lean_object* v_type_4950_, lean_object* v_a_4951_, lean_object* v_a_4952_, lean_object* v_a_4953_, lean_object* v_a_4954_, lean_object* v_a_4955_, lean_object* v_a_4956_, lean_object* v_a_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_){
_start:
{
lean_object* v___x_4962_; 
lean_inc_ref(v_type_4950_);
v___x_4962_ = l_Lean_Meta_getDecLevel(v_type_4950_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_);
if (lean_obj_tag(v___x_4962_) == 0)
{
lean_object* v_a_4963_; lean_object* v___x_4964_; 
v_a_4963_ = lean_ctor_get(v___x_4962_, 0);
lean_inc_n(v_a_4963_, 2);
lean_dec_ref_known(v___x_4962_, 1);
lean_inc_ref(v_type_4950_);
v___x_4964_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_a_4963_, v_type_4950_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_);
if (lean_obj_tag(v___x_4964_) == 0)
{
lean_object* v_a_4965_; lean_object* v___x_4967_; uint8_t v_isShared_4968_; uint8_t v_isSharedCheck_5257_; 
v_a_4965_ = lean_ctor_get(v___x_4964_, 0);
v_isSharedCheck_5257_ = !lean_is_exclusive(v___x_4964_);
if (v_isSharedCheck_5257_ == 0)
{
v___x_4967_ = v___x_4964_;
v_isShared_4968_ = v_isSharedCheck_5257_;
goto v_resetjp_4966_;
}
else
{
lean_inc(v_a_4965_);
lean_dec(v___x_4964_);
v___x_4967_ = lean_box(0);
v_isShared_4968_ = v_isSharedCheck_5257_;
goto v_resetjp_4966_;
}
v_resetjp_4966_:
{
if (lean_obj_tag(v_a_4965_) == 1)
{
lean_object* v_val_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; 
lean_del_object(v___x_4967_);
v_val_4969_ = lean_ctor_get(v_a_4965_, 0);
lean_inc_n(v_val_4969_, 2);
lean_dec_ref_known(v_a_4965_, 1);
v___x_4970_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1));
v___x_4971_ = lean_box(0);
lean_inc(v_a_4963_);
v___x_4972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4972_, 0, v_a_4963_);
lean_ctor_set(v___x_4972_, 1, v___x_4971_);
lean_inc_ref(v___x_4972_);
v___x_4973_ = l_Lean_mkConst(v___x_4970_, v___x_4972_);
lean_inc_ref(v_type_4950_);
v___x_4974_ = l_Lean_mkAppB(v___x_4973_, v_type_4950_, v_val_4969_);
v___x_4975_ = l_Lean_Meta_Sym_canon(v___x_4974_, v_a_4955_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_);
if (lean_obj_tag(v___x_4975_) == 0)
{
lean_object* v_a_4976_; lean_object* v___x_4977_; 
v_a_4976_ = lean_ctor_get(v___x_4975_, 0);
lean_inc(v_a_4976_);
lean_dec_ref_known(v___x_4975_, 1);
v___x_4977_ = l_Lean_Meta_Sym_shareCommon(v_a_4976_, v_a_4955_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_);
if (lean_obj_tag(v___x_4977_) == 0)
{
lean_object* v_a_4978_; lean_object* v___x_4979_; 
v_a_4978_ = lean_ctor_get(v___x_4977_, 0);
lean_inc_n(v_a_4978_, 2);
lean_dec_ref_known(v___x_4977_, 1);
v___x_4979_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v_a_4978_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_);
if (lean_obj_tag(v___x_4979_) == 0)
{
lean_object* v_a_4980_; 
v_a_4980_ = lean_ctor_get(v___x_4979_, 0);
lean_inc(v_a_4980_);
lean_dec_ref_known(v___x_4979_, 1);
if (lean_obj_tag(v_a_4980_) == 1)
{
lean_object* v_val_4981_; lean_object* v___x_4983_; uint8_t v_isShared_4984_; uint8_t v_isSharedCheck_5232_; 
v_val_4981_ = lean_ctor_get(v_a_4980_, 0);
v_isSharedCheck_5232_ = !lean_is_exclusive(v_a_4980_);
if (v_isSharedCheck_5232_ == 0)
{
v___x_4983_ = v_a_4980_;
v_isShared_4984_ = v_isSharedCheck_5232_;
goto v_resetjp_4982_;
}
else
{
lean_inc(v_val_4981_);
lean_dec(v_a_4980_);
v___x_4983_ = lean_box(0);
v_isShared_4984_ = v_isSharedCheck_5232_;
goto v_resetjp_4982_;
}
v_resetjp_4982_:
{
lean_object* v___x_4985_; lean_object* v___x_4986_; 
v___x_4985_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1));
lean_inc_ref(v_type_4950_);
lean_inc(v_a_4963_);
v___x_4986_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_4985_, v_a_4963_, v_type_4950_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_);
if (lean_obj_tag(v___x_4986_) == 0)
{
lean_object* v_a_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; 
v_a_4987_ = lean_ctor_get(v___x_4986_, 0);
lean_inc(v_a_4987_);
lean_dec_ref_known(v___x_4986_, 1);
v___x_4988_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__3));
lean_inc_ref(v_type_4950_);
lean_inc(v_a_4963_);
v___x_4989_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_4988_, v_a_4963_, v_type_4950_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_);
if (lean_obj_tag(v___x_4989_) == 0)
{
lean_object* v_a_4990_; lean_object* v___x_4991_; 
v_a_4990_ = lean_ctor_get(v___x_4989_, 0);
lean_inc(v_a_4990_);
lean_dec_ref_known(v___x_4989_, 1);
lean_inc(v_a_4987_);
lean_inc_ref(v_type_4950_);
lean_inc(v_a_4963_);
v___x_4991_ = l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f(v_a_4963_, v_type_4950_, v_a_4987_, v_a_4955_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_);
if (lean_obj_tag(v___x_4991_) == 0)
{
lean_object* v_a_4992_; lean_object* v___x_4993_; 
v_a_4992_ = lean_ctor_get(v___x_4991_, 0);
lean_inc(v_a_4992_);
lean_dec_ref_known(v___x_4991_, 1);
lean_inc(v_a_4987_);
lean_inc(v_a_4990_);
lean_inc_ref(v_type_4950_);
lean_inc(v_a_4963_);
v___x_4993_ = l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f(v_a_4963_, v_type_4950_, v_a_4990_, v_a_4987_, v_a_4955_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_);
if (lean_obj_tag(v___x_4993_) == 0)
{
lean_object* v_a_4994_; lean_object* v___x_4995_; 
v_a_4994_ = lean_ctor_get(v___x_4993_, 0);
lean_inc(v_a_4994_);
lean_dec_ref_known(v___x_4993_, 1);
lean_inc(v_a_4987_);
lean_inc_ref(v_type_4950_);
lean_inc(v_a_4963_);
v___x_4995_ = l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f(v_a_4963_, v_type_4950_, v_a_4987_, v_a_4955_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_);
if (lean_obj_tag(v___x_4995_) == 0)
{
lean_object* v_a_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; 
v_a_4996_ = lean_ctor_get(v___x_4995_, 0);
lean_inc(v_a_4996_);
lean_dec_ref_known(v___x_4995_, 1);
v___x_4997_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc_ref(v_type_4950_);
lean_inc(v_a_4963_);
v___x_4998_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_4997_, v_a_4963_, v_type_4950_, v_a_4955_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_);
if (lean_obj_tag(v___x_4998_) == 0)
{
lean_object* v_a_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; 
v_a_4999_ = lean_ctor_get(v___x_4998_, 0);
lean_inc_n(v_a_4999_, 2);
lean_dec_ref_known(v___x_4998_, 1);
v___x_5000_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__64));
lean_inc_ref(v___x_4972_);
lean_inc_n(v_a_4963_, 2);
v___x_5001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5001_, 0, v_a_4963_);
lean_ctor_set(v___x_5001_, 1, v___x_4972_);
lean_inc_ref(v___x_5001_);
v___x_5002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5002_, 0, v_a_4963_);
lean_ctor_set(v___x_5002_, 1, v___x_5001_);
v___x_5003_ = l_Lean_mkConst(v___x_5000_, v___x_5002_);
lean_inc_ref_n(v_type_4950_, 3);
v___x_5004_ = l_Lean_mkApp4(v___x_5003_, v_type_4950_, v_type_4950_, v_type_4950_, v_a_4999_);
v___x_5005_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_5004_, v_a_4955_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_);
if (lean_obj_tag(v___x_5005_) == 0)
{
lean_object* v_a_5006_; lean_object* v_orderedAddInst_x3f_5008_; lean_object* v___y_5009_; lean_object* v___y_5010_; lean_object* v___y_5011_; lean_object* v___y_5012_; lean_object* v___y_5013_; lean_object* v___y_5014_; lean_object* v___y_5015_; lean_object* v___y_5016_; lean_object* v___y_5017_; lean_object* v___y_5018_; lean_object* v___y_5150_; lean_object* v___y_5151_; lean_object* v___y_5152_; lean_object* v___y_5153_; lean_object* v___y_5154_; lean_object* v___y_5155_; lean_object* v___y_5156_; lean_object* v___y_5157_; lean_object* v___y_5158_; lean_object* v___y_5159_; 
v_a_5006_ = lean_ctor_get(v___x_5005_, 0);
lean_inc(v_a_5006_);
lean_dec_ref_known(v___x_5005_, 1);
if (lean_obj_tag(v_a_4987_) == 1)
{
if (lean_obj_tag(v_a_4992_) == 1)
{
lean_object* v_val_5161_; lean_object* v_val_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; 
v_val_5161_ = lean_ctor_get(v_a_4987_, 0);
v_val_5162_ = lean_ctor_get(v_a_4992_, 0);
v___x_5163_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__66));
lean_inc_ref(v___x_4972_);
v___x_5164_ = l_Lean_mkConst(v___x_5163_, v___x_4972_);
lean_inc(v_val_5162_);
lean_inc(v_val_5161_);
lean_inc_ref(v_type_4950_);
v___x_5165_ = l_Lean_mkApp4(v___x_5164_, v_type_4950_, v_a_4999_, v_val_5161_, v_val_5162_);
v___x_5166_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_5165_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_);
if (lean_obj_tag(v___x_5166_) == 0)
{
lean_object* v_a_5167_; 
v_a_5167_ = lean_ctor_get(v___x_5166_, 0);
lean_inc(v_a_5167_);
lean_dec_ref_known(v___x_5166_, 1);
v_orderedAddInst_x3f_5008_ = v_a_5167_;
v___y_5009_ = v_a_4951_;
v___y_5010_ = v_a_4952_;
v___y_5011_ = v_a_4953_;
v___y_5012_ = v_a_4954_;
v___y_5013_ = v_a_4955_;
v___y_5014_ = v_a_4956_;
v___y_5015_ = v_a_4957_;
v___y_5016_ = v_a_4958_;
v___y_5017_ = v_a_4959_;
v___y_5018_ = v_a_4960_;
goto v___jp_5007_;
}
else
{
lean_object* v_a_5168_; lean_object* v___x_5170_; uint8_t v_isShared_5171_; uint8_t v_isSharedCheck_5175_; 
lean_dec_ref_known(v_a_4992_, 1);
lean_dec_ref_known(v_a_4987_, 1);
lean_dec(v_a_5006_);
lean_dec_ref_known(v___x_5001_, 2);
lean_dec(v_a_4996_);
lean_dec(v_a_4994_);
lean_dec(v_a_4990_);
lean_del_object(v___x_4983_);
lean_dec(v_val_4981_);
lean_dec(v_a_4978_);
lean_dec_ref_known(v___x_4972_, 2);
lean_dec(v_val_4969_);
lean_dec(v_a_4963_);
lean_dec_ref(v_type_4950_);
v_a_5168_ = lean_ctor_get(v___x_5166_, 0);
v_isSharedCheck_5175_ = !lean_is_exclusive(v___x_5166_);
if (v_isSharedCheck_5175_ == 0)
{
v___x_5170_ = v___x_5166_;
v_isShared_5171_ = v_isSharedCheck_5175_;
goto v_resetjp_5169_;
}
else
{
lean_inc(v_a_5168_);
lean_dec(v___x_5166_);
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
lean_dec(v_a_4999_);
v___y_5150_ = v_a_4951_;
v___y_5151_ = v_a_4952_;
v___y_5152_ = v_a_4953_;
v___y_5153_ = v_a_4954_;
v___y_5154_ = v_a_4955_;
v___y_5155_ = v_a_4956_;
v___y_5156_ = v_a_4957_;
v___y_5157_ = v_a_4958_;
v___y_5158_ = v_a_4959_;
v___y_5159_ = v_a_4960_;
goto v___jp_5149_;
}
}
else
{
lean_dec(v_a_4999_);
v___y_5150_ = v_a_4951_;
v___y_5151_ = v_a_4952_;
v___y_5152_ = v_a_4953_;
v___y_5153_ = v_a_4954_;
v___y_5154_ = v_a_4955_;
v___y_5155_ = v_a_4956_;
v___y_5156_ = v_a_4957_;
v___y_5157_ = v_a_4958_;
v___y_5158_ = v_a_4959_;
v___y_5159_ = v_a_4960_;
goto v___jp_5149_;
}
v___jp_5007_:
{
lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; 
v___x_5019_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__12));
lean_inc_ref(v___x_4972_);
v___x_5020_ = l_Lean_mkConst(v___x_5019_, v___x_4972_);
lean_inc_ref(v_type_4950_);
v___x_5021_ = l_Lean_Expr_app___override(v___x_5020_, v_type_4950_);
v___x_5022_ = l_Lean_Meta_Sym_synthInstance(v___x_5021_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_);
if (lean_obj_tag(v___x_5022_) == 0)
{
lean_object* v_a_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; 
v_a_5023_ = lean_ctor_get(v___x_5022_, 0);
lean_inc(v_a_5023_);
lean_dec_ref_known(v___x_5022_, 1);
v___x_5024_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__14));
lean_inc_ref(v___x_4972_);
v___x_5025_ = l_Lean_mkConst(v___x_5024_, v___x_4972_);
lean_inc_ref(v_type_4950_);
v___x_5026_ = l_Lean_mkAppB(v___x_5025_, v_type_4950_, v_a_5023_);
v___x_5027_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_5026_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_);
if (lean_obj_tag(v___x_5027_) == 0)
{
lean_object* v_a_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; 
v_a_5028_ = lean_ctor_get(v___x_5027_, 0);
lean_inc(v_a_5028_);
lean_dec_ref_known(v___x_5027_, 1);
v___x_5029_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1));
lean_inc_ref(v___x_4972_);
v___x_5030_ = l_Lean_mkConst(v___x_5029_, v___x_4972_);
lean_inc(v_val_4969_);
lean_inc_ref(v_type_4950_);
v___x_5031_ = l_Lean_mkAppB(v___x_5030_, v_type_4950_, v_val_4969_);
v___x_5032_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_5031_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_);
if (lean_obj_tag(v___x_5032_) == 0)
{
lean_object* v_a_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; 
v_a_5033_ = lean_ctor_get(v___x_5032_, 0);
lean_inc(v_a_5033_);
lean_dec_ref_known(v___x_5032_, 1);
v___x_5034_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__14));
lean_inc_ref(v_type_4950_);
lean_inc(v_a_4963_);
v___x_5035_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v___x_5034_, v_a_4963_, v_type_4950_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_);
if (lean_obj_tag(v___x_5035_) == 0)
{
lean_object* v_a_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; 
v_a_5036_ = lean_ctor_get(v___x_5035_, 0);
lean_inc(v_a_5036_);
lean_dec_ref_known(v___x_5035_, 1);
v___x_5037_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__16));
v___x_5038_ = l_Lean_mkConst(v___x_5037_, v___x_4972_);
lean_inc_ref(v_type_4950_);
v___x_5039_ = l_Lean_mkAppB(v___x_5038_, v_type_4950_, v_a_5036_);
v___x_5040_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_5039_, v___y_5009_, v___y_5010_, v___y_5011_, v___y_5012_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_);
if (lean_obj_tag(v___x_5040_) == 0)
{
lean_object* v_a_5041_; lean_object* v___x_5042_; 
v_a_5041_ = lean_ctor_get(v___x_5040_, 0);
lean_inc(v_a_5041_);
lean_dec_ref_known(v___x_5040_, 1);
lean_inc_ref(v_type_4950_);
lean_inc(v_a_4963_);
v___x_5042_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_a_4963_, v_type_4950_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_);
if (lean_obj_tag(v___x_5042_) == 0)
{
lean_object* v_a_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; 
v_a_5043_ = lean_ctor_get(v___x_5042_, 0);
lean_inc(v_a_5043_);
lean_dec_ref_known(v___x_5042_, 1);
v___x_5044_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_5045_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_5046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5046_, 0, v___x_5045_);
lean_ctor_set(v___x_5046_, 1, v___x_5001_);
v___x_5047_ = l_Lean_mkConst(v___x_5044_, v___x_5046_);
v___x_5048_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_4950_, 2);
v___x_5049_ = l_Lean_mkApp4(v___x_5047_, v___x_5048_, v_type_4950_, v_type_4950_, v_a_5043_);
v___x_5050_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_5049_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_);
if (lean_obj_tag(v___x_5050_) == 0)
{
lean_object* v_a_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; 
v_a_5051_ = lean_ctor_get(v___x_5050_, 0);
lean_inc(v_a_5051_);
lean_dec_ref_known(v___x_5050_, 1);
v___x_5052_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4));
lean_inc(v_a_4963_);
v___x_5053_ = l_Lean_Level_succ___override(v_a_4963_);
v___x_5054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5054_, 0, v___x_5053_);
lean_ctor_set(v___x_5054_, 1, v___x_4971_);
v___x_5055_ = l_Lean_mkConst(v___x_5052_, v___x_5054_);
v___x_5056_ = l_Lean_Expr_app___override(v___x_5055_, v_a_4978_);
v___x_5057_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v___y_5009_, v___y_5017_);
if (lean_obj_tag(v___x_5057_) == 0)
{
lean_object* v_a_5058_; lean_object* v_natStructs_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___f_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; 
v_a_5058_ = lean_ctor_get(v___x_5057_, 0);
lean_inc(v_a_5058_);
lean_dec_ref_known(v___x_5057_, 1);
v_natStructs_5059_ = lean_ctor_get(v_a_5058_, 5);
lean_inc_ref(v_natStructs_5059_);
lean_dec(v_a_5058_);
v___x_5060_ = lean_array_get_size(v_natStructs_5059_);
lean_dec_ref(v_natStructs_5059_);
v___x_5061_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5);
v___x_5062_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v___x_5062_, 0, v___x_5060_);
lean_ctor_set(v___x_5062_, 1, v_val_4981_);
lean_ctor_set(v___x_5062_, 2, v_type_4950_);
lean_ctor_set(v___x_5062_, 3, v_a_4963_);
lean_ctor_set(v___x_5062_, 4, v_val_4969_);
lean_ctor_set(v___x_5062_, 5, v_a_4987_);
lean_ctor_set(v___x_5062_, 6, v_a_4990_);
lean_ctor_set(v___x_5062_, 7, v_a_4994_);
lean_ctor_set(v___x_5062_, 8, v_a_4992_);
lean_ctor_set(v___x_5062_, 9, v_orderedAddInst_x3f_5008_);
lean_ctor_set(v___x_5062_, 10, v_a_4996_);
lean_ctor_set(v___x_5062_, 11, v_a_5028_);
lean_ctor_set(v___x_5062_, 12, v___x_5056_);
lean_ctor_set(v___x_5062_, 13, v_a_5041_);
lean_ctor_set(v___x_5062_, 14, v_a_5033_);
lean_ctor_set(v___x_5062_, 15, v_a_5006_);
lean_ctor_set(v___x_5062_, 16, v_a_5051_);
lean_ctor_set(v___x_5062_, 17, v___x_5061_);
v___f_5063_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(v___f_5063_, 0, v___x_5062_);
v___x_5064_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_5065_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_5064_, v___f_5063_, v___y_5009_);
if (lean_obj_tag(v___x_5065_) == 0)
{
lean_object* v___x_5067_; uint8_t v_isShared_5068_; uint8_t v_isSharedCheck_5075_; 
v_isSharedCheck_5075_ = !lean_is_exclusive(v___x_5065_);
if (v_isSharedCheck_5075_ == 0)
{
lean_object* v_unused_5076_; 
v_unused_5076_ = lean_ctor_get(v___x_5065_, 0);
lean_dec(v_unused_5076_);
v___x_5067_ = v___x_5065_;
v_isShared_5068_ = v_isSharedCheck_5075_;
goto v_resetjp_5066_;
}
else
{
lean_dec(v___x_5065_);
v___x_5067_ = lean_box(0);
v_isShared_5068_ = v_isSharedCheck_5075_;
goto v_resetjp_5066_;
}
v_resetjp_5066_:
{
lean_object* v___x_5070_; 
if (v_isShared_4984_ == 0)
{
lean_ctor_set(v___x_4983_, 0, v___x_5060_);
v___x_5070_ = v___x_4983_;
goto v_reusejp_5069_;
}
else
{
lean_object* v_reuseFailAlloc_5074_; 
v_reuseFailAlloc_5074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5074_, 0, v___x_5060_);
v___x_5070_ = v_reuseFailAlloc_5074_;
goto v_reusejp_5069_;
}
v_reusejp_5069_:
{
lean_object* v___x_5072_; 
if (v_isShared_5068_ == 0)
{
lean_ctor_set(v___x_5067_, 0, v___x_5070_);
v___x_5072_ = v___x_5067_;
goto v_reusejp_5071_;
}
else
{
lean_object* v_reuseFailAlloc_5073_; 
v_reuseFailAlloc_5073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5073_, 0, v___x_5070_);
v___x_5072_ = v_reuseFailAlloc_5073_;
goto v_reusejp_5071_;
}
v_reusejp_5071_:
{
return v___x_5072_;
}
}
}
}
else
{
lean_object* v_a_5077_; lean_object* v___x_5079_; uint8_t v_isShared_5080_; uint8_t v_isSharedCheck_5084_; 
lean_del_object(v___x_4983_);
v_a_5077_ = lean_ctor_get(v___x_5065_, 0);
v_isSharedCheck_5084_ = !lean_is_exclusive(v___x_5065_);
if (v_isSharedCheck_5084_ == 0)
{
v___x_5079_ = v___x_5065_;
v_isShared_5080_ = v_isSharedCheck_5084_;
goto v_resetjp_5078_;
}
else
{
lean_inc(v_a_5077_);
lean_dec(v___x_5065_);
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
else
{
lean_object* v_a_5085_; lean_object* v___x_5087_; uint8_t v_isShared_5088_; uint8_t v_isSharedCheck_5092_; 
lean_dec_ref(v___x_5056_);
lean_dec(v_a_5051_);
lean_dec(v_a_5041_);
lean_dec(v_a_5033_);
lean_dec(v_a_5028_);
lean_dec(v_orderedAddInst_x3f_5008_);
lean_dec(v_a_5006_);
lean_dec(v_a_4996_);
lean_dec(v_a_4994_);
lean_dec(v_a_4992_);
lean_dec(v_a_4990_);
lean_dec(v_a_4987_);
lean_del_object(v___x_4983_);
lean_dec(v_val_4981_);
lean_dec(v_val_4969_);
lean_dec(v_a_4963_);
lean_dec_ref(v_type_4950_);
v_a_5085_ = lean_ctor_get(v___x_5057_, 0);
v_isSharedCheck_5092_ = !lean_is_exclusive(v___x_5057_);
if (v_isSharedCheck_5092_ == 0)
{
v___x_5087_ = v___x_5057_;
v_isShared_5088_ = v_isSharedCheck_5092_;
goto v_resetjp_5086_;
}
else
{
lean_inc(v_a_5085_);
lean_dec(v___x_5057_);
v___x_5087_ = lean_box(0);
v_isShared_5088_ = v_isSharedCheck_5092_;
goto v_resetjp_5086_;
}
v_resetjp_5086_:
{
lean_object* v___x_5090_; 
if (v_isShared_5088_ == 0)
{
v___x_5090_ = v___x_5087_;
goto v_reusejp_5089_;
}
else
{
lean_object* v_reuseFailAlloc_5091_; 
v_reuseFailAlloc_5091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5091_, 0, v_a_5085_);
v___x_5090_ = v_reuseFailAlloc_5091_;
goto v_reusejp_5089_;
}
v_reusejp_5089_:
{
return v___x_5090_;
}
}
}
}
else
{
lean_object* v_a_5093_; lean_object* v___x_5095_; uint8_t v_isShared_5096_; uint8_t v_isSharedCheck_5100_; 
lean_dec(v_a_5041_);
lean_dec(v_a_5033_);
lean_dec(v_a_5028_);
lean_dec(v_orderedAddInst_x3f_5008_);
lean_dec(v_a_5006_);
lean_dec(v_a_4996_);
lean_dec(v_a_4994_);
lean_dec(v_a_4992_);
lean_dec(v_a_4990_);
lean_dec(v_a_4987_);
lean_del_object(v___x_4983_);
lean_dec(v_val_4981_);
lean_dec(v_a_4978_);
lean_dec(v_val_4969_);
lean_dec(v_a_4963_);
lean_dec_ref(v_type_4950_);
v_a_5093_ = lean_ctor_get(v___x_5050_, 0);
v_isSharedCheck_5100_ = !lean_is_exclusive(v___x_5050_);
if (v_isSharedCheck_5100_ == 0)
{
v___x_5095_ = v___x_5050_;
v_isShared_5096_ = v_isSharedCheck_5100_;
goto v_resetjp_5094_;
}
else
{
lean_inc(v_a_5093_);
lean_dec(v___x_5050_);
v___x_5095_ = lean_box(0);
v_isShared_5096_ = v_isSharedCheck_5100_;
goto v_resetjp_5094_;
}
v_resetjp_5094_:
{
lean_object* v___x_5098_; 
if (v_isShared_5096_ == 0)
{
v___x_5098_ = v___x_5095_;
goto v_reusejp_5097_;
}
else
{
lean_object* v_reuseFailAlloc_5099_; 
v_reuseFailAlloc_5099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5099_, 0, v_a_5093_);
v___x_5098_ = v_reuseFailAlloc_5099_;
goto v_reusejp_5097_;
}
v_reusejp_5097_:
{
return v___x_5098_;
}
}
}
}
else
{
lean_object* v_a_5101_; lean_object* v___x_5103_; uint8_t v_isShared_5104_; uint8_t v_isSharedCheck_5108_; 
lean_dec(v_a_5041_);
lean_dec(v_a_5033_);
lean_dec(v_a_5028_);
lean_dec(v_orderedAddInst_x3f_5008_);
lean_dec(v_a_5006_);
lean_dec_ref_known(v___x_5001_, 2);
lean_dec(v_a_4996_);
lean_dec(v_a_4994_);
lean_dec(v_a_4992_);
lean_dec(v_a_4990_);
lean_dec(v_a_4987_);
lean_del_object(v___x_4983_);
lean_dec(v_val_4981_);
lean_dec(v_a_4978_);
lean_dec(v_val_4969_);
lean_dec(v_a_4963_);
lean_dec_ref(v_type_4950_);
v_a_5101_ = lean_ctor_get(v___x_5042_, 0);
v_isSharedCheck_5108_ = !lean_is_exclusive(v___x_5042_);
if (v_isSharedCheck_5108_ == 0)
{
v___x_5103_ = v___x_5042_;
v_isShared_5104_ = v_isSharedCheck_5108_;
goto v_resetjp_5102_;
}
else
{
lean_inc(v_a_5101_);
lean_dec(v___x_5042_);
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
lean_object* v_a_5109_; lean_object* v___x_5111_; uint8_t v_isShared_5112_; uint8_t v_isSharedCheck_5116_; 
lean_dec(v_a_5033_);
lean_dec(v_a_5028_);
lean_dec(v_orderedAddInst_x3f_5008_);
lean_dec(v_a_5006_);
lean_dec_ref_known(v___x_5001_, 2);
lean_dec(v_a_4996_);
lean_dec(v_a_4994_);
lean_dec(v_a_4992_);
lean_dec(v_a_4990_);
lean_dec(v_a_4987_);
lean_del_object(v___x_4983_);
lean_dec(v_val_4981_);
lean_dec(v_a_4978_);
lean_dec(v_val_4969_);
lean_dec(v_a_4963_);
lean_dec_ref(v_type_4950_);
v_a_5109_ = lean_ctor_get(v___x_5040_, 0);
v_isSharedCheck_5116_ = !lean_is_exclusive(v___x_5040_);
if (v_isSharedCheck_5116_ == 0)
{
v___x_5111_ = v___x_5040_;
v_isShared_5112_ = v_isSharedCheck_5116_;
goto v_resetjp_5110_;
}
else
{
lean_inc(v_a_5109_);
lean_dec(v___x_5040_);
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
lean_dec(v_a_5033_);
lean_dec(v_a_5028_);
lean_dec(v_orderedAddInst_x3f_5008_);
lean_dec(v_a_5006_);
lean_dec_ref_known(v___x_5001_, 2);
lean_dec(v_a_4996_);
lean_dec(v_a_4994_);
lean_dec(v_a_4992_);
lean_dec(v_a_4990_);
lean_dec(v_a_4987_);
lean_del_object(v___x_4983_);
lean_dec(v_val_4981_);
lean_dec(v_a_4978_);
lean_dec_ref_known(v___x_4972_, 2);
lean_dec(v_val_4969_);
lean_dec(v_a_4963_);
lean_dec_ref(v_type_4950_);
v_a_5117_ = lean_ctor_get(v___x_5035_, 0);
v_isSharedCheck_5124_ = !lean_is_exclusive(v___x_5035_);
if (v_isSharedCheck_5124_ == 0)
{
v___x_5119_ = v___x_5035_;
v_isShared_5120_ = v_isSharedCheck_5124_;
goto v_resetjp_5118_;
}
else
{
lean_inc(v_a_5117_);
lean_dec(v___x_5035_);
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
lean_dec(v_a_5028_);
lean_dec(v_orderedAddInst_x3f_5008_);
lean_dec(v_a_5006_);
lean_dec_ref_known(v___x_5001_, 2);
lean_dec(v_a_4996_);
lean_dec(v_a_4994_);
lean_dec(v_a_4992_);
lean_dec(v_a_4990_);
lean_dec(v_a_4987_);
lean_del_object(v___x_4983_);
lean_dec(v_val_4981_);
lean_dec(v_a_4978_);
lean_dec_ref_known(v___x_4972_, 2);
lean_dec(v_val_4969_);
lean_dec(v_a_4963_);
lean_dec_ref(v_type_4950_);
v_a_5125_ = lean_ctor_get(v___x_5032_, 0);
v_isSharedCheck_5132_ = !lean_is_exclusive(v___x_5032_);
if (v_isSharedCheck_5132_ == 0)
{
v___x_5127_ = v___x_5032_;
v_isShared_5128_ = v_isSharedCheck_5132_;
goto v_resetjp_5126_;
}
else
{
lean_inc(v_a_5125_);
lean_dec(v___x_5032_);
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
lean_dec(v_orderedAddInst_x3f_5008_);
lean_dec(v_a_5006_);
lean_dec_ref_known(v___x_5001_, 2);
lean_dec(v_a_4996_);
lean_dec(v_a_4994_);
lean_dec(v_a_4992_);
lean_dec(v_a_4990_);
lean_dec(v_a_4987_);
lean_del_object(v___x_4983_);
lean_dec(v_val_4981_);
lean_dec(v_a_4978_);
lean_dec_ref_known(v___x_4972_, 2);
lean_dec(v_val_4969_);
lean_dec(v_a_4963_);
lean_dec_ref(v_type_4950_);
v_a_5133_ = lean_ctor_get(v___x_5027_, 0);
v_isSharedCheck_5140_ = !lean_is_exclusive(v___x_5027_);
if (v_isSharedCheck_5140_ == 0)
{
v___x_5135_ = v___x_5027_;
v_isShared_5136_ = v_isSharedCheck_5140_;
goto v_resetjp_5134_;
}
else
{
lean_inc(v_a_5133_);
lean_dec(v___x_5027_);
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
lean_dec(v_orderedAddInst_x3f_5008_);
lean_dec(v_a_5006_);
lean_dec_ref_known(v___x_5001_, 2);
lean_dec(v_a_4996_);
lean_dec(v_a_4994_);
lean_dec(v_a_4992_);
lean_dec(v_a_4990_);
lean_dec(v_a_4987_);
lean_del_object(v___x_4983_);
lean_dec(v_val_4981_);
lean_dec(v_a_4978_);
lean_dec_ref_known(v___x_4972_, 2);
lean_dec(v_val_4969_);
lean_dec(v_a_4963_);
lean_dec_ref(v_type_4950_);
v_a_5141_ = lean_ctor_get(v___x_5022_, 0);
v_isSharedCheck_5148_ = !lean_is_exclusive(v___x_5022_);
if (v_isSharedCheck_5148_ == 0)
{
v___x_5143_ = v___x_5022_;
v_isShared_5144_ = v_isSharedCheck_5148_;
goto v_resetjp_5142_;
}
else
{
lean_inc(v_a_5141_);
lean_dec(v___x_5022_);
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
v___jp_5149_:
{
lean_object* v___x_5160_; 
v___x_5160_ = lean_box(0);
v_orderedAddInst_x3f_5008_ = v___x_5160_;
v___y_5009_ = v___y_5150_;
v___y_5010_ = v___y_5151_;
v___y_5011_ = v___y_5152_;
v___y_5012_ = v___y_5153_;
v___y_5013_ = v___y_5154_;
v___y_5014_ = v___y_5155_;
v___y_5015_ = v___y_5156_;
v___y_5016_ = v___y_5157_;
v___y_5017_ = v___y_5158_;
v___y_5018_ = v___y_5159_;
goto v___jp_5007_;
}
}
else
{
lean_object* v_a_5176_; lean_object* v___x_5178_; uint8_t v_isShared_5179_; uint8_t v_isSharedCheck_5183_; 
lean_dec_ref_known(v___x_5001_, 2);
lean_dec(v_a_4999_);
lean_dec(v_a_4996_);
lean_dec(v_a_4994_);
lean_dec(v_a_4992_);
lean_dec(v_a_4990_);
lean_dec(v_a_4987_);
lean_del_object(v___x_4983_);
lean_dec(v_val_4981_);
lean_dec(v_a_4978_);
lean_dec_ref_known(v___x_4972_, 2);
lean_dec(v_val_4969_);
lean_dec(v_a_4963_);
lean_dec_ref(v_type_4950_);
v_a_5176_ = lean_ctor_get(v___x_5005_, 0);
v_isSharedCheck_5183_ = !lean_is_exclusive(v___x_5005_);
if (v_isSharedCheck_5183_ == 0)
{
v___x_5178_ = v___x_5005_;
v_isShared_5179_ = v_isSharedCheck_5183_;
goto v_resetjp_5177_;
}
else
{
lean_inc(v_a_5176_);
lean_dec(v___x_5005_);
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
lean_object* v_a_5184_; lean_object* v___x_5186_; uint8_t v_isShared_5187_; uint8_t v_isSharedCheck_5191_; 
lean_dec(v_a_4996_);
lean_dec(v_a_4994_);
lean_dec(v_a_4992_);
lean_dec(v_a_4990_);
lean_dec(v_a_4987_);
lean_del_object(v___x_4983_);
lean_dec(v_val_4981_);
lean_dec(v_a_4978_);
lean_dec_ref_known(v___x_4972_, 2);
lean_dec(v_val_4969_);
lean_dec(v_a_4963_);
lean_dec_ref(v_type_4950_);
v_a_5184_ = lean_ctor_get(v___x_4998_, 0);
v_isSharedCheck_5191_ = !lean_is_exclusive(v___x_4998_);
if (v_isSharedCheck_5191_ == 0)
{
v___x_5186_ = v___x_4998_;
v_isShared_5187_ = v_isSharedCheck_5191_;
goto v_resetjp_5185_;
}
else
{
lean_inc(v_a_5184_);
lean_dec(v___x_4998_);
v___x_5186_ = lean_box(0);
v_isShared_5187_ = v_isSharedCheck_5191_;
goto v_resetjp_5185_;
}
v_resetjp_5185_:
{
lean_object* v___x_5189_; 
if (v_isShared_5187_ == 0)
{
v___x_5189_ = v___x_5186_;
goto v_reusejp_5188_;
}
else
{
lean_object* v_reuseFailAlloc_5190_; 
v_reuseFailAlloc_5190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5190_, 0, v_a_5184_);
v___x_5189_ = v_reuseFailAlloc_5190_;
goto v_reusejp_5188_;
}
v_reusejp_5188_:
{
return v___x_5189_;
}
}
}
}
else
{
lean_object* v_a_5192_; lean_object* v___x_5194_; uint8_t v_isShared_5195_; uint8_t v_isSharedCheck_5199_; 
lean_dec(v_a_4994_);
lean_dec(v_a_4992_);
lean_dec(v_a_4990_);
lean_dec(v_a_4987_);
lean_del_object(v___x_4983_);
lean_dec(v_val_4981_);
lean_dec(v_a_4978_);
lean_dec_ref_known(v___x_4972_, 2);
lean_dec(v_val_4969_);
lean_dec(v_a_4963_);
lean_dec_ref(v_type_4950_);
v_a_5192_ = lean_ctor_get(v___x_4995_, 0);
v_isSharedCheck_5199_ = !lean_is_exclusive(v___x_4995_);
if (v_isSharedCheck_5199_ == 0)
{
v___x_5194_ = v___x_4995_;
v_isShared_5195_ = v_isSharedCheck_5199_;
goto v_resetjp_5193_;
}
else
{
lean_inc(v_a_5192_);
lean_dec(v___x_4995_);
v___x_5194_ = lean_box(0);
v_isShared_5195_ = v_isSharedCheck_5199_;
goto v_resetjp_5193_;
}
v_resetjp_5193_:
{
lean_object* v___x_5197_; 
if (v_isShared_5195_ == 0)
{
v___x_5197_ = v___x_5194_;
goto v_reusejp_5196_;
}
else
{
lean_object* v_reuseFailAlloc_5198_; 
v_reuseFailAlloc_5198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5198_, 0, v_a_5192_);
v___x_5197_ = v_reuseFailAlloc_5198_;
goto v_reusejp_5196_;
}
v_reusejp_5196_:
{
return v___x_5197_;
}
}
}
}
else
{
lean_object* v_a_5200_; lean_object* v___x_5202_; uint8_t v_isShared_5203_; uint8_t v_isSharedCheck_5207_; 
lean_dec(v_a_4992_);
lean_dec(v_a_4990_);
lean_dec(v_a_4987_);
lean_del_object(v___x_4983_);
lean_dec(v_val_4981_);
lean_dec(v_a_4978_);
lean_dec_ref_known(v___x_4972_, 2);
lean_dec(v_val_4969_);
lean_dec(v_a_4963_);
lean_dec_ref(v_type_4950_);
v_a_5200_ = lean_ctor_get(v___x_4993_, 0);
v_isSharedCheck_5207_ = !lean_is_exclusive(v___x_4993_);
if (v_isSharedCheck_5207_ == 0)
{
v___x_5202_ = v___x_4993_;
v_isShared_5203_ = v_isSharedCheck_5207_;
goto v_resetjp_5201_;
}
else
{
lean_inc(v_a_5200_);
lean_dec(v___x_4993_);
v___x_5202_ = lean_box(0);
v_isShared_5203_ = v_isSharedCheck_5207_;
goto v_resetjp_5201_;
}
v_resetjp_5201_:
{
lean_object* v___x_5205_; 
if (v_isShared_5203_ == 0)
{
v___x_5205_ = v___x_5202_;
goto v_reusejp_5204_;
}
else
{
lean_object* v_reuseFailAlloc_5206_; 
v_reuseFailAlloc_5206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5206_, 0, v_a_5200_);
v___x_5205_ = v_reuseFailAlloc_5206_;
goto v_reusejp_5204_;
}
v_reusejp_5204_:
{
return v___x_5205_;
}
}
}
}
else
{
lean_object* v_a_5208_; lean_object* v___x_5210_; uint8_t v_isShared_5211_; uint8_t v_isSharedCheck_5215_; 
lean_dec(v_a_4990_);
lean_dec(v_a_4987_);
lean_del_object(v___x_4983_);
lean_dec(v_val_4981_);
lean_dec(v_a_4978_);
lean_dec_ref_known(v___x_4972_, 2);
lean_dec(v_val_4969_);
lean_dec(v_a_4963_);
lean_dec_ref(v_type_4950_);
v_a_5208_ = lean_ctor_get(v___x_4991_, 0);
v_isSharedCheck_5215_ = !lean_is_exclusive(v___x_4991_);
if (v_isSharedCheck_5215_ == 0)
{
v___x_5210_ = v___x_4991_;
v_isShared_5211_ = v_isSharedCheck_5215_;
goto v_resetjp_5209_;
}
else
{
lean_inc(v_a_5208_);
lean_dec(v___x_4991_);
v___x_5210_ = lean_box(0);
v_isShared_5211_ = v_isSharedCheck_5215_;
goto v_resetjp_5209_;
}
v_resetjp_5209_:
{
lean_object* v___x_5213_; 
if (v_isShared_5211_ == 0)
{
v___x_5213_ = v___x_5210_;
goto v_reusejp_5212_;
}
else
{
lean_object* v_reuseFailAlloc_5214_; 
v_reuseFailAlloc_5214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5214_, 0, v_a_5208_);
v___x_5213_ = v_reuseFailAlloc_5214_;
goto v_reusejp_5212_;
}
v_reusejp_5212_:
{
return v___x_5213_;
}
}
}
}
else
{
lean_object* v_a_5216_; lean_object* v___x_5218_; uint8_t v_isShared_5219_; uint8_t v_isSharedCheck_5223_; 
lean_dec(v_a_4987_);
lean_del_object(v___x_4983_);
lean_dec(v_val_4981_);
lean_dec(v_a_4978_);
lean_dec_ref_known(v___x_4972_, 2);
lean_dec(v_val_4969_);
lean_dec(v_a_4963_);
lean_dec_ref(v_type_4950_);
v_a_5216_ = lean_ctor_get(v___x_4989_, 0);
v_isSharedCheck_5223_ = !lean_is_exclusive(v___x_4989_);
if (v_isSharedCheck_5223_ == 0)
{
v___x_5218_ = v___x_4989_;
v_isShared_5219_ = v_isSharedCheck_5223_;
goto v_resetjp_5217_;
}
else
{
lean_inc(v_a_5216_);
lean_dec(v___x_4989_);
v___x_5218_ = lean_box(0);
v_isShared_5219_ = v_isSharedCheck_5223_;
goto v_resetjp_5217_;
}
v_resetjp_5217_:
{
lean_object* v___x_5221_; 
if (v_isShared_5219_ == 0)
{
v___x_5221_ = v___x_5218_;
goto v_reusejp_5220_;
}
else
{
lean_object* v_reuseFailAlloc_5222_; 
v_reuseFailAlloc_5222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5222_, 0, v_a_5216_);
v___x_5221_ = v_reuseFailAlloc_5222_;
goto v_reusejp_5220_;
}
v_reusejp_5220_:
{
return v___x_5221_;
}
}
}
}
else
{
lean_object* v_a_5224_; lean_object* v___x_5226_; uint8_t v_isShared_5227_; uint8_t v_isSharedCheck_5231_; 
lean_del_object(v___x_4983_);
lean_dec(v_val_4981_);
lean_dec(v_a_4978_);
lean_dec_ref_known(v___x_4972_, 2);
lean_dec(v_val_4969_);
lean_dec(v_a_4963_);
lean_dec_ref(v_type_4950_);
v_a_5224_ = lean_ctor_get(v___x_4986_, 0);
v_isSharedCheck_5231_ = !lean_is_exclusive(v___x_4986_);
if (v_isSharedCheck_5231_ == 0)
{
v___x_5226_ = v___x_4986_;
v_isShared_5227_ = v_isSharedCheck_5231_;
goto v_resetjp_5225_;
}
else
{
lean_inc(v_a_5224_);
lean_dec(v___x_4986_);
v___x_5226_ = lean_box(0);
v_isShared_5227_ = v_isSharedCheck_5231_;
goto v_resetjp_5225_;
}
v_resetjp_5225_:
{
lean_object* v___x_5229_; 
if (v_isShared_5227_ == 0)
{
v___x_5229_ = v___x_5226_;
goto v_reusejp_5228_;
}
else
{
lean_object* v_reuseFailAlloc_5230_; 
v_reuseFailAlloc_5230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5230_, 0, v_a_5224_);
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
}
else
{
lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; 
lean_dec(v_a_4980_);
lean_dec_ref_known(v___x_4972_, 2);
lean_dec(v_val_4969_);
lean_dec(v_a_4963_);
lean_dec_ref(v_type_4950_);
v___x_5233_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7);
v___x_5234_ = l_Lean_indentExpr(v_a_4978_);
v___x_5235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5235_, 0, v___x_5233_);
lean_ctor_set(v___x_5235_, 1, v___x_5234_);
v___x_5236_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v___x_5235_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_);
return v___x_5236_;
}
}
else
{
lean_dec(v_a_4978_);
lean_dec_ref_known(v___x_4972_, 2);
lean_dec(v_val_4969_);
lean_dec(v_a_4963_);
lean_dec_ref(v_type_4950_);
return v___x_4979_;
}
}
else
{
lean_object* v_a_5237_; lean_object* v___x_5239_; uint8_t v_isShared_5240_; uint8_t v_isSharedCheck_5244_; 
lean_dec_ref_known(v___x_4972_, 2);
lean_dec(v_val_4969_);
lean_dec(v_a_4963_);
lean_dec_ref(v_type_4950_);
v_a_5237_ = lean_ctor_get(v___x_4977_, 0);
v_isSharedCheck_5244_ = !lean_is_exclusive(v___x_4977_);
if (v_isSharedCheck_5244_ == 0)
{
v___x_5239_ = v___x_4977_;
v_isShared_5240_ = v_isSharedCheck_5244_;
goto v_resetjp_5238_;
}
else
{
lean_inc(v_a_5237_);
lean_dec(v___x_4977_);
v___x_5239_ = lean_box(0);
v_isShared_5240_ = v_isSharedCheck_5244_;
goto v_resetjp_5238_;
}
v_resetjp_5238_:
{
lean_object* v___x_5242_; 
if (v_isShared_5240_ == 0)
{
v___x_5242_ = v___x_5239_;
goto v_reusejp_5241_;
}
else
{
lean_object* v_reuseFailAlloc_5243_; 
v_reuseFailAlloc_5243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5243_, 0, v_a_5237_);
v___x_5242_ = v_reuseFailAlloc_5243_;
goto v_reusejp_5241_;
}
v_reusejp_5241_:
{
return v___x_5242_;
}
}
}
}
else
{
lean_object* v_a_5245_; lean_object* v___x_5247_; uint8_t v_isShared_5248_; uint8_t v_isSharedCheck_5252_; 
lean_dec_ref_known(v___x_4972_, 2);
lean_dec(v_val_4969_);
lean_dec(v_a_4963_);
lean_dec_ref(v_type_4950_);
v_a_5245_ = lean_ctor_get(v___x_4975_, 0);
v_isSharedCheck_5252_ = !lean_is_exclusive(v___x_4975_);
if (v_isSharedCheck_5252_ == 0)
{
v___x_5247_ = v___x_4975_;
v_isShared_5248_ = v_isSharedCheck_5252_;
goto v_resetjp_5246_;
}
else
{
lean_inc(v_a_5245_);
lean_dec(v___x_4975_);
v___x_5247_ = lean_box(0);
v_isShared_5248_ = v_isSharedCheck_5252_;
goto v_resetjp_5246_;
}
v_resetjp_5246_:
{
lean_object* v___x_5250_; 
if (v_isShared_5248_ == 0)
{
v___x_5250_ = v___x_5247_;
goto v_reusejp_5249_;
}
else
{
lean_object* v_reuseFailAlloc_5251_; 
v_reuseFailAlloc_5251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5251_, 0, v_a_5245_);
v___x_5250_ = v_reuseFailAlloc_5251_;
goto v_reusejp_5249_;
}
v_reusejp_5249_:
{
return v___x_5250_;
}
}
}
}
else
{
lean_object* v___x_5253_; lean_object* v___x_5255_; 
lean_dec(v_a_4965_);
lean_dec(v_a_4963_);
lean_dec_ref(v_type_4950_);
v___x_5253_ = lean_box(0);
if (v_isShared_4968_ == 0)
{
lean_ctor_set(v___x_4967_, 0, v___x_5253_);
v___x_5255_ = v___x_4967_;
goto v_reusejp_5254_;
}
else
{
lean_object* v_reuseFailAlloc_5256_; 
v_reuseFailAlloc_5256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5256_, 0, v___x_5253_);
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
else
{
lean_object* v_a_5258_; lean_object* v___x_5260_; uint8_t v_isShared_5261_; uint8_t v_isSharedCheck_5265_; 
lean_dec(v_a_4963_);
lean_dec_ref(v_type_4950_);
v_a_5258_ = lean_ctor_get(v___x_4964_, 0);
v_isSharedCheck_5265_ = !lean_is_exclusive(v___x_4964_);
if (v_isSharedCheck_5265_ == 0)
{
v___x_5260_ = v___x_4964_;
v_isShared_5261_ = v_isSharedCheck_5265_;
goto v_resetjp_5259_;
}
else
{
lean_inc(v_a_5258_);
lean_dec(v___x_4964_);
v___x_5260_ = lean_box(0);
v_isShared_5261_ = v_isSharedCheck_5265_;
goto v_resetjp_5259_;
}
v_resetjp_5259_:
{
lean_object* v___x_5263_; 
if (v_isShared_5261_ == 0)
{
v___x_5263_ = v___x_5260_;
goto v_reusejp_5262_;
}
else
{
lean_object* v_reuseFailAlloc_5264_; 
v_reuseFailAlloc_5264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5264_, 0, v_a_5258_);
v___x_5263_ = v_reuseFailAlloc_5264_;
goto v_reusejp_5262_;
}
v_reusejp_5262_:
{
return v___x_5263_;
}
}
}
}
else
{
lean_object* v_a_5266_; lean_object* v___x_5268_; uint8_t v_isShared_5269_; uint8_t v_isSharedCheck_5273_; 
lean_dec_ref(v_type_4950_);
v_a_5266_ = lean_ctor_get(v___x_4962_, 0);
v_isSharedCheck_5273_ = !lean_is_exclusive(v___x_4962_);
if (v_isSharedCheck_5273_ == 0)
{
v___x_5268_ = v___x_4962_;
v_isShared_5269_ = v_isSharedCheck_5273_;
goto v_resetjp_5267_;
}
else
{
lean_inc(v_a_5266_);
lean_dec(v___x_4962_);
v___x_5268_ = lean_box(0);
v_isShared_5269_ = v_isSharedCheck_5273_;
goto v_resetjp_5267_;
}
v_resetjp_5267_:
{
lean_object* v___x_5271_; 
if (v_isShared_5269_ == 0)
{
v___x_5271_ = v___x_5268_;
goto v_reusejp_5270_;
}
else
{
lean_object* v_reuseFailAlloc_5272_; 
v_reuseFailAlloc_5272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5272_, 0, v_a_5266_);
v___x_5271_ = v_reuseFailAlloc_5272_;
goto v_reusejp_5270_;
}
v_reusejp_5270_:
{
return v___x_5271_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_4950_ = stack[0].m_obj;
lean_object* v_a_4951_ = stack[1].m_obj;
lean_object* v_a_4952_ = stack[2].m_obj;
lean_object* v_a_4953_ = stack[3].m_obj;
lean_object* v_a_4954_ = stack[4].m_obj;
lean_object* v_a_4955_ = stack[5].m_obj;
lean_object* v_a_4956_ = stack[6].m_obj;
lean_object* v_a_4957_ = stack[7].m_obj;
lean_object* v_a_4958_ = stack[8].m_obj;
lean_object* v_a_4959_ = stack[9].m_obj;
lean_object* v_a_4960_ = stack[10].m_obj;
lean_object* v_res_5274_;
v_res_5274_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(v_type_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_);
stack->m_obj
 = v_res_5274_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___boxed(lean_object* v_type_5275_, lean_object* v_a_5276_, lean_object* v_a_5277_, lean_object* v_a_5278_, lean_object* v_a_5279_, lean_object* v_a_5280_, lean_object* v_a_5281_, lean_object* v_a_5282_, lean_object* v_a_5283_, lean_object* v_a_5284_, lean_object* v_a_5285_, lean_object* v_a_5286_){
_start:
{
lean_object* v_res_5287_; 
v_res_5287_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(v_type_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_, v_a_5280_, v_a_5281_, v_a_5282_, v_a_5283_, v_a_5284_, v_a_5285_);
lean_dec(v_a_5285_);
lean_dec_ref(v_a_5284_);
lean_dec(v_a_5283_);
lean_dec_ref(v_a_5282_);
lean_dec(v_a_5281_);
lean_dec_ref(v_a_5280_);
lean_dec(v_a_5279_);
lean_dec_ref(v_a_5278_);
lean_dec(v_a_5277_);
lean_dec(v_a_5276_);
return v_res_5287_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0(lean_object* v_00_u03b1_5288_, lean_object* v_msg_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_){
_start:
{
lean_object* v___x_5301_; 
v___x_5301_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v_msg_5289_, v___y_5296_, v___y_5297_, v___y_5298_, v___y_5299_);
return v___x_5301_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_5289_ = stack[1].m_obj;
lean_object* v___y_5290_ = stack[2].m_obj;
lean_object* v___y_5291_ = stack[3].m_obj;
lean_object* v___y_5292_ = stack[4].m_obj;
lean_object* v___y_5293_ = stack[5].m_obj;
lean_object* v___y_5294_ = stack[6].m_obj;
lean_object* v___y_5295_ = stack[7].m_obj;
lean_object* v___y_5296_ = stack[8].m_obj;
lean_object* v___y_5297_ = stack[9].m_obj;
lean_object* v___y_5298_ = stack[10].m_obj;
lean_object* v___y_5299_ = stack[11].m_obj;
lean_object* v_res_5302_;
v_res_5302_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0(lean_box(0), v_msg_5289_, v___y_5290_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_, v___y_5295_, v___y_5296_, v___y_5297_, v___y_5298_, v___y_5299_);
stack->m_obj
 = v_res_5302_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___boxed(lean_object* v_00_u03b1_5303_, lean_object* v_msg_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_){
_start:
{
lean_object* v_res_5316_; 
v_res_5316_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0(v_00_u03b1_5303_, v_msg_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_, v___y_5313_, v___y_5314_);
lean_dec(v___y_5314_);
lean_dec_ref(v___y_5313_);
lean_dec(v___y_5312_);
lean_dec_ref(v___y_5311_);
lean_dec(v___y_5310_);
lean_dec_ref(v___y_5309_);
lean_dec(v___y_5308_);
lean_dec_ref(v___y_5307_);
lean_dec(v___y_5306_);
lean_dec(v___y_5305_);
return v_res_5316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___lam__0(lean_object* v_type_5317_, lean_object* v_a_5318_, lean_object* v_s_5319_){
_start:
{
lean_object* v_structs_5320_; lean_object* v_typeIdOf_5321_; lean_object* v_exprToStructId_5322_; lean_object* v_exprToStructIdEntries_5323_; lean_object* v_forbiddenNatModules_5324_; lean_object* v_natStructs_5325_; lean_object* v_natTypeIdOf_5326_; lean_object* v_exprToNatStructId_5327_; lean_object* v___x_5329_; uint8_t v_isShared_5330_; uint8_t v_isSharedCheck_5335_; 
v_structs_5320_ = lean_ctor_get(v_s_5319_, 0);
v_typeIdOf_5321_ = lean_ctor_get(v_s_5319_, 1);
v_exprToStructId_5322_ = lean_ctor_get(v_s_5319_, 2);
v_exprToStructIdEntries_5323_ = lean_ctor_get(v_s_5319_, 3);
v_forbiddenNatModules_5324_ = lean_ctor_get(v_s_5319_, 4);
v_natStructs_5325_ = lean_ctor_get(v_s_5319_, 5);
v_natTypeIdOf_5326_ = lean_ctor_get(v_s_5319_, 6);
v_exprToNatStructId_5327_ = lean_ctor_get(v_s_5319_, 7);
v_isSharedCheck_5335_ = !lean_is_exclusive(v_s_5319_);
if (v_isSharedCheck_5335_ == 0)
{
v___x_5329_ = v_s_5319_;
v_isShared_5330_ = v_isSharedCheck_5335_;
goto v_resetjp_5328_;
}
else
{
lean_inc(v_exprToNatStructId_5327_);
lean_inc(v_natTypeIdOf_5326_);
lean_inc(v_natStructs_5325_);
lean_inc(v_forbiddenNatModules_5324_);
lean_inc(v_exprToStructIdEntries_5323_);
lean_inc(v_exprToStructId_5322_);
lean_inc(v_typeIdOf_5321_);
lean_inc(v_structs_5320_);
lean_dec(v_s_5319_);
v___x_5329_ = lean_box(0);
v_isShared_5330_ = v_isSharedCheck_5335_;
goto v_resetjp_5328_;
}
v_resetjp_5328_:
{
lean_object* v___x_5331_; lean_object* v___x_5333_; 
v___x_5331_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_natTypeIdOf_5326_, v_type_5317_, v_a_5318_);
if (v_isShared_5330_ == 0)
{
lean_ctor_set(v___x_5329_, 6, v___x_5331_);
v___x_5333_ = v___x_5329_;
goto v_reusejp_5332_;
}
else
{
lean_object* v_reuseFailAlloc_5334_; 
v_reuseFailAlloc_5334_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_5334_, 0, v_structs_5320_);
lean_ctor_set(v_reuseFailAlloc_5334_, 1, v_typeIdOf_5321_);
lean_ctor_set(v_reuseFailAlloc_5334_, 2, v_exprToStructId_5322_);
lean_ctor_set(v_reuseFailAlloc_5334_, 3, v_exprToStructIdEntries_5323_);
lean_ctor_set(v_reuseFailAlloc_5334_, 4, v_forbiddenNatModules_5324_);
lean_ctor_set(v_reuseFailAlloc_5334_, 5, v_natStructs_5325_);
lean_ctor_set(v_reuseFailAlloc_5334_, 6, v___x_5331_);
lean_ctor_set(v_reuseFailAlloc_5334_, 7, v_exprToNatStructId_5327_);
v___x_5333_ = v_reuseFailAlloc_5334_;
goto v_reusejp_5332_;
}
v_reusejp_5332_:
{
return v___x_5333_;
}
}
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_5336_, lean_object* v_i_5337_, lean_object* v_k_5338_){
_start:
{
lean_object* v___x_5339_; uint8_t v___x_5340_; 
v___x_5339_ = lean_array_get_size(v_keys_5336_);
v___x_5340_ = lean_nat_dec_lt(v_i_5337_, v___x_5339_);
if (v___x_5340_ == 0)
{
lean_dec(v_i_5337_);
return v___x_5340_;
}
else
{
lean_object* v_k_x27_5341_; size_t v___x_5342_; size_t v___x_5343_; uint8_t v___x_5344_; 
v_k_x27_5341_ = lean_array_fget_borrowed(v_keys_5336_, v_i_5337_);
v___x_5342_ = lean_ptr_addr(v_k_5338_);
v___x_5343_ = lean_ptr_addr(v_k_x27_5341_);
v___x_5344_ = lean_usize_dec_eq(v___x_5342_, v___x_5343_);
if (v___x_5344_ == 0)
{
lean_object* v___x_5345_; lean_object* v___x_5346_; 
v___x_5345_ = lean_unsigned_to_nat(1u);
v___x_5346_ = lean_nat_add(v_i_5337_, v___x_5345_);
lean_dec(v_i_5337_);
v_i_5337_ = v___x_5346_;
goto _start;
}
else
{
lean_dec(v_i_5337_);
return v___x_5340_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_5336_ = stack[0].m_obj;
lean_object* v_i_5337_ = stack[1].m_obj;
lean_object* v_k_5338_ = stack[2].m_obj;
uint8_t v_res_5348_;
v_res_5348_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5336_, v_i_5337_, v_k_5338_);
stack->m_num = v_res_5348_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_5349_, lean_object* v_i_5350_, lean_object* v_k_5351_){
_start:
{
uint8_t v_res_5352_; lean_object* v_r_5353_; 
v_res_5352_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5349_, v_i_5350_, v_k_5351_);
lean_dec_ref(v_k_5351_);
lean_dec_ref(v_keys_5349_);
v_r_5353_ = lean_box(v_res_5352_);
return v_r_5353_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_5354_, size_t v_x_5355_, lean_object* v_x_5356_){
_start:
{
if (lean_obj_tag(v_x_5354_) == 0)
{
lean_object* v_es_5357_; lean_object* v___x_5358_; size_t v___x_5359_; size_t v___x_5360_; lean_object* v_j_5361_; lean_object* v___x_5362_; 
v_es_5357_ = lean_ctor_get(v_x_5354_, 0);
v___x_5358_ = lean_box(2);
v___x_5359_ = ((size_t)31ULL);
v___x_5360_ = lean_usize_land(v_x_5355_, v___x_5359_);
v_j_5361_ = lean_usize_to_nat(v___x_5360_);
v___x_5362_ = lean_array_get_borrowed(v___x_5358_, v_es_5357_, v_j_5361_);
lean_dec(v_j_5361_);
switch(lean_obj_tag(v___x_5362_))
{
case 0:
{
lean_object* v_key_5363_; size_t v___x_5364_; size_t v___x_5365_; uint8_t v___x_5366_; 
v_key_5363_ = lean_ctor_get(v___x_5362_, 0);
v___x_5364_ = lean_ptr_addr(v_x_5356_);
v___x_5365_ = lean_ptr_addr(v_key_5363_);
v___x_5366_ = lean_usize_dec_eq(v___x_5364_, v___x_5365_);
return v___x_5366_;
}
case 1:
{
lean_object* v_node_5367_; size_t v___x_5368_; size_t v___x_5369_; 
v_node_5367_ = lean_ctor_get(v___x_5362_, 0);
v___x_5368_ = ((size_t)5ULL);
v___x_5369_ = lean_usize_shift_right(v_x_5355_, v___x_5368_);
v_x_5354_ = v_node_5367_;
v_x_5355_ = v___x_5369_;
goto _start;
}
default: 
{
uint8_t v___x_5371_; 
v___x_5371_ = 0;
return v___x_5371_;
}
}
}
else
{
lean_object* v_ks_5372_; lean_object* v___x_5373_; uint8_t v___x_5374_; 
v_ks_5372_ = lean_ctor_get(v_x_5354_, 0);
v___x_5373_ = lean_unsigned_to_nat(0u);
v___x_5374_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_5372_, v___x_5373_, v_x_5356_);
return v___x_5374_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5354_ = stack[0].m_obj;
size_t v_x_5355_ = stack[1].m_num;
lean_object* v_x_5356_ = stack[2].m_obj;
uint8_t v_res_5375_;
v_res_5375_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_5354_, v_x_5355_, v_x_5356_);
stack->m_num = v_res_5375_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_5376_, lean_object* v_x_5377_, lean_object* v_x_5378_){
_start:
{
size_t v_x_8695__boxed_5379_; uint8_t v_res_5380_; lean_object* v_r_5381_; 
v_x_8695__boxed_5379_ = lean_unbox_usize(v_x_5377_);
lean_dec(v_x_5377_);
v_res_5380_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_5376_, v_x_8695__boxed_5379_, v_x_5378_);
lean_dec_ref(v_x_5378_);
lean_dec_ref(v_x_5376_);
v_r_5381_ = lean_box(v_res_5380_);
return v_r_5381_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(lean_object* v_x_5382_, lean_object* v_x_5383_){
_start:
{
size_t v___x_5384_; size_t v___x_5385_; size_t v___x_5386_; uint64_t v___x_5387_; size_t v___x_5388_; uint8_t v___x_5389_; 
v___x_5384_ = lean_ptr_addr(v_x_5383_);
v___x_5385_ = ((size_t)3ULL);
v___x_5386_ = lean_usize_shift_right(v___x_5384_, v___x_5385_);
v___x_5387_ = lean_usize_to_uint64(v___x_5386_);
v___x_5388_ = lean_uint64_to_usize(v___x_5387_);
v___x_5389_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_5382_, v___x_5388_, v_x_5383_);
return v___x_5389_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5382_ = stack[0].m_obj;
lean_object* v_x_5383_ = stack[1].m_obj;
uint8_t v_res_5390_;
v_res_5390_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_x_5382_, v_x_5383_);
stack->m_num = v_res_5390_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_5391_, lean_object* v_x_5392_){
_start:
{
uint8_t v_res_5393_; lean_object* v_r_5394_; 
v_res_5393_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_x_5391_, v_x_5392_);
lean_dec_ref(v_x_5392_);
lean_dec_ref(v_x_5391_);
v_r_5394_ = lean_box(v_res_5393_);
return v_r_5394_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(lean_object* v_type_5395_, lean_object* v_a_5396_, lean_object* v_a_5397_, lean_object* v_a_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_, lean_object* v_a_5403_, lean_object* v_a_5404_, lean_object* v_a_5405_){
_start:
{
lean_object* v___x_5407_; 
v___x_5407_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_5398_);
if (lean_obj_tag(v___x_5407_) == 0)
{
lean_object* v_a_5408_; lean_object* v___x_5410_; uint8_t v_isShared_5411_; uint8_t v_isSharedCheck_5497_; 
v_a_5408_ = lean_ctor_get(v___x_5407_, 0);
v_isSharedCheck_5497_ = !lean_is_exclusive(v___x_5407_);
if (v_isSharedCheck_5497_ == 0)
{
v___x_5410_ = v___x_5407_;
v_isShared_5411_ = v_isSharedCheck_5497_;
goto v_resetjp_5409_;
}
else
{
lean_inc(v_a_5408_);
lean_dec(v___x_5407_);
v___x_5410_ = lean_box(0);
v_isShared_5411_ = v_isSharedCheck_5497_;
goto v_resetjp_5409_;
}
v_resetjp_5409_:
{
uint8_t v_linarith_5412_; 
v_linarith_5412_ = lean_ctor_get_uint8(v_a_5408_, sizeof(void*)*14 + 22);
lean_dec(v_a_5408_);
if (v_linarith_5412_ == 0)
{
lean_object* v___x_5413_; lean_object* v___x_5415_; 
lean_dec_ref(v_type_5395_);
v___x_5413_ = lean_box(0);
if (v_isShared_5411_ == 0)
{
lean_ctor_set(v___x_5410_, 0, v___x_5413_);
v___x_5415_ = v___x_5410_;
goto v_reusejp_5414_;
}
else
{
lean_object* v_reuseFailAlloc_5416_; 
v_reuseFailAlloc_5416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5416_, 0, v___x_5413_);
v___x_5415_ = v_reuseFailAlloc_5416_;
goto v_reusejp_5414_;
}
v_reusejp_5414_:
{
return v___x_5415_;
}
}
else
{
lean_object* v___x_5417_; 
lean_del_object(v___x_5410_);
v___x_5417_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_5396_, v_a_5404_);
if (lean_obj_tag(v___x_5417_) == 0)
{
lean_object* v_a_5418_; lean_object* v___x_5420_; uint8_t v_isShared_5421_; uint8_t v_isSharedCheck_5488_; 
v_a_5418_ = lean_ctor_get(v___x_5417_, 0);
v_isSharedCheck_5488_ = !lean_is_exclusive(v___x_5417_);
if (v_isSharedCheck_5488_ == 0)
{
v___x_5420_ = v___x_5417_;
v_isShared_5421_ = v_isSharedCheck_5488_;
goto v_resetjp_5419_;
}
else
{
lean_inc(v_a_5418_);
lean_dec(v___x_5417_);
v___x_5420_ = lean_box(0);
v_isShared_5421_ = v_isSharedCheck_5488_;
goto v_resetjp_5419_;
}
v_resetjp_5419_:
{
lean_object* v_forbiddenNatModules_5422_; uint8_t v___x_5423_; 
v_forbiddenNatModules_5422_ = lean_ctor_get(v_a_5418_, 4);
lean_inc_ref(v_forbiddenNatModules_5422_);
lean_dec(v_a_5418_);
v___x_5423_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_forbiddenNatModules_5422_, v_type_5395_);
lean_dec_ref(v_forbiddenNatModules_5422_);
if (v___x_5423_ == 0)
{
lean_object* v___x_5424_; 
lean_del_object(v___x_5420_);
lean_inc_ref(v_type_5395_);
v___x_5424_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___redArg(v_type_5395_, v_a_5398_, v_a_5403_);
if (lean_obj_tag(v___x_5424_) == 0)
{
lean_object* v_a_5425_; lean_object* v___x_5427_; uint8_t v_isShared_5428_; uint8_t v_isSharedCheck_5475_; 
v_a_5425_ = lean_ctor_get(v___x_5424_, 0);
v_isSharedCheck_5475_ = !lean_is_exclusive(v___x_5424_);
if (v_isSharedCheck_5475_ == 0)
{
v___x_5427_ = v___x_5424_;
v_isShared_5428_ = v_isSharedCheck_5475_;
goto v_resetjp_5426_;
}
else
{
lean_inc(v_a_5425_);
lean_dec(v___x_5424_);
v___x_5427_ = lean_box(0);
v_isShared_5428_ = v_isSharedCheck_5475_;
goto v_resetjp_5426_;
}
v_resetjp_5426_:
{
uint8_t v___x_5429_; 
v___x_5429_ = lean_unbox(v_a_5425_);
lean_dec(v_a_5425_);
if (v___x_5429_ == 0)
{
lean_object* v___x_5430_; 
lean_del_object(v___x_5427_);
v___x_5430_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_5396_, v_a_5404_);
if (lean_obj_tag(v___x_5430_) == 0)
{
lean_object* v_a_5431_; lean_object* v___x_5433_; uint8_t v_isShared_5434_; uint8_t v_isSharedCheck_5462_; 
v_a_5431_ = lean_ctor_get(v___x_5430_, 0);
v_isSharedCheck_5462_ = !lean_is_exclusive(v___x_5430_);
if (v_isSharedCheck_5462_ == 0)
{
v___x_5433_ = v___x_5430_;
v_isShared_5434_ = v_isSharedCheck_5462_;
goto v_resetjp_5432_;
}
else
{
lean_inc(v_a_5431_);
lean_dec(v___x_5430_);
v___x_5433_ = lean_box(0);
v_isShared_5434_ = v_isSharedCheck_5462_;
goto v_resetjp_5432_;
}
v_resetjp_5432_:
{
lean_object* v_natTypeIdOf_5435_; lean_object* v___x_5436_; 
v_natTypeIdOf_5435_ = lean_ctor_get(v_a_5431_, 6);
lean_inc_ref(v_natTypeIdOf_5435_);
lean_dec(v_a_5431_);
v___x_5436_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_natTypeIdOf_5435_, v_type_5395_);
lean_dec_ref(v_natTypeIdOf_5435_);
if (lean_obj_tag(v___x_5436_) == 1)
{
lean_object* v_val_5437_; lean_object* v___x_5439_; 
lean_dec_ref(v_type_5395_);
v_val_5437_ = lean_ctor_get(v___x_5436_, 0);
lean_inc(v_val_5437_);
lean_dec_ref_known(v___x_5436_, 1);
if (v_isShared_5434_ == 0)
{
lean_ctor_set(v___x_5433_, 0, v_val_5437_);
v___x_5439_ = v___x_5433_;
goto v_reusejp_5438_;
}
else
{
lean_object* v_reuseFailAlloc_5440_; 
v_reuseFailAlloc_5440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5440_, 0, v_val_5437_);
v___x_5439_ = v_reuseFailAlloc_5440_;
goto v_reusejp_5438_;
}
v_reusejp_5438_:
{
return v___x_5439_;
}
}
else
{
lean_object* v___x_5441_; 
lean_dec(v___x_5436_);
lean_del_object(v___x_5433_);
lean_inc_ref(v_type_5395_);
v___x_5441_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(v_type_5395_, v_a_5396_, v_a_5397_, v_a_5398_, v_a_5399_, v_a_5400_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_);
if (lean_obj_tag(v___x_5441_) == 0)
{
lean_object* v_a_5442_; lean_object* v___f_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; 
v_a_5442_ = lean_ctor_get(v___x_5441_, 0);
lean_inc_n(v_a_5442_, 2);
lean_dec_ref_known(v___x_5441_, 1);
v___f_5443_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_5443_, 0, v_type_5395_);
lean_closure_set(v___f_5443_, 1, v_a_5442_);
v___x_5444_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_5445_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_5444_, v___f_5443_, v_a_5396_);
if (lean_obj_tag(v___x_5445_) == 0)
{
lean_object* v___x_5447_; uint8_t v_isShared_5448_; uint8_t v_isSharedCheck_5452_; 
v_isSharedCheck_5452_ = !lean_is_exclusive(v___x_5445_);
if (v_isSharedCheck_5452_ == 0)
{
lean_object* v_unused_5453_; 
v_unused_5453_ = lean_ctor_get(v___x_5445_, 0);
lean_dec(v_unused_5453_);
v___x_5447_ = v___x_5445_;
v_isShared_5448_ = v_isSharedCheck_5452_;
goto v_resetjp_5446_;
}
else
{
lean_dec(v___x_5445_);
v___x_5447_ = lean_box(0);
v_isShared_5448_ = v_isSharedCheck_5452_;
goto v_resetjp_5446_;
}
v_resetjp_5446_:
{
lean_object* v___x_5450_; 
if (v_isShared_5448_ == 0)
{
lean_ctor_set(v___x_5447_, 0, v_a_5442_);
v___x_5450_ = v___x_5447_;
goto v_reusejp_5449_;
}
else
{
lean_object* v_reuseFailAlloc_5451_; 
v_reuseFailAlloc_5451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5451_, 0, v_a_5442_);
v___x_5450_ = v_reuseFailAlloc_5451_;
goto v_reusejp_5449_;
}
v_reusejp_5449_:
{
return v___x_5450_;
}
}
}
else
{
lean_object* v_a_5454_; lean_object* v___x_5456_; uint8_t v_isShared_5457_; uint8_t v_isSharedCheck_5461_; 
lean_dec(v_a_5442_);
v_a_5454_ = lean_ctor_get(v___x_5445_, 0);
v_isSharedCheck_5461_ = !lean_is_exclusive(v___x_5445_);
if (v_isSharedCheck_5461_ == 0)
{
v___x_5456_ = v___x_5445_;
v_isShared_5457_ = v_isSharedCheck_5461_;
goto v_resetjp_5455_;
}
else
{
lean_inc(v_a_5454_);
lean_dec(v___x_5445_);
v___x_5456_ = lean_box(0);
v_isShared_5457_ = v_isSharedCheck_5461_;
goto v_resetjp_5455_;
}
v_resetjp_5455_:
{
lean_object* v___x_5459_; 
if (v_isShared_5457_ == 0)
{
v___x_5459_ = v___x_5456_;
goto v_reusejp_5458_;
}
else
{
lean_object* v_reuseFailAlloc_5460_; 
v_reuseFailAlloc_5460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5460_, 0, v_a_5454_);
v___x_5459_ = v_reuseFailAlloc_5460_;
goto v_reusejp_5458_;
}
v_reusejp_5458_:
{
return v___x_5459_;
}
}
}
}
else
{
lean_dec_ref(v_type_5395_);
return v___x_5441_;
}
}
}
}
else
{
lean_object* v_a_5463_; lean_object* v___x_5465_; uint8_t v_isShared_5466_; uint8_t v_isSharedCheck_5470_; 
lean_dec_ref(v_type_5395_);
v_a_5463_ = lean_ctor_get(v___x_5430_, 0);
v_isSharedCheck_5470_ = !lean_is_exclusive(v___x_5430_);
if (v_isSharedCheck_5470_ == 0)
{
v___x_5465_ = v___x_5430_;
v_isShared_5466_ = v_isSharedCheck_5470_;
goto v_resetjp_5464_;
}
else
{
lean_inc(v_a_5463_);
lean_dec(v___x_5430_);
v___x_5465_ = lean_box(0);
v_isShared_5466_ = v_isSharedCheck_5470_;
goto v_resetjp_5464_;
}
v_resetjp_5464_:
{
lean_object* v___x_5468_; 
if (v_isShared_5466_ == 0)
{
v___x_5468_ = v___x_5465_;
goto v_reusejp_5467_;
}
else
{
lean_object* v_reuseFailAlloc_5469_; 
v_reuseFailAlloc_5469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5469_, 0, v_a_5463_);
v___x_5468_ = v_reuseFailAlloc_5469_;
goto v_reusejp_5467_;
}
v_reusejp_5467_:
{
return v___x_5468_;
}
}
}
}
else
{
lean_object* v___x_5471_; lean_object* v___x_5473_; 
lean_dec_ref(v_type_5395_);
v___x_5471_ = lean_box(0);
if (v_isShared_5428_ == 0)
{
lean_ctor_set(v___x_5427_, 0, v___x_5471_);
v___x_5473_ = v___x_5427_;
goto v_reusejp_5472_;
}
else
{
lean_object* v_reuseFailAlloc_5474_; 
v_reuseFailAlloc_5474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5474_, 0, v___x_5471_);
v___x_5473_ = v_reuseFailAlloc_5474_;
goto v_reusejp_5472_;
}
v_reusejp_5472_:
{
return v___x_5473_;
}
}
}
}
else
{
lean_object* v_a_5476_; lean_object* v___x_5478_; uint8_t v_isShared_5479_; uint8_t v_isSharedCheck_5483_; 
lean_dec_ref(v_type_5395_);
v_a_5476_ = lean_ctor_get(v___x_5424_, 0);
v_isSharedCheck_5483_ = !lean_is_exclusive(v___x_5424_);
if (v_isSharedCheck_5483_ == 0)
{
v___x_5478_ = v___x_5424_;
v_isShared_5479_ = v_isSharedCheck_5483_;
goto v_resetjp_5477_;
}
else
{
lean_inc(v_a_5476_);
lean_dec(v___x_5424_);
v___x_5478_ = lean_box(0);
v_isShared_5479_ = v_isSharedCheck_5483_;
goto v_resetjp_5477_;
}
v_resetjp_5477_:
{
lean_object* v___x_5481_; 
if (v_isShared_5479_ == 0)
{
v___x_5481_ = v___x_5478_;
goto v_reusejp_5480_;
}
else
{
lean_object* v_reuseFailAlloc_5482_; 
v_reuseFailAlloc_5482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5482_, 0, v_a_5476_);
v___x_5481_ = v_reuseFailAlloc_5482_;
goto v_reusejp_5480_;
}
v_reusejp_5480_:
{
return v___x_5481_;
}
}
}
}
else
{
lean_object* v___x_5484_; lean_object* v___x_5486_; 
lean_dec_ref(v_type_5395_);
v___x_5484_ = lean_box(0);
if (v_isShared_5421_ == 0)
{
lean_ctor_set(v___x_5420_, 0, v___x_5484_);
v___x_5486_ = v___x_5420_;
goto v_reusejp_5485_;
}
else
{
lean_object* v_reuseFailAlloc_5487_; 
v_reuseFailAlloc_5487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5487_, 0, v___x_5484_);
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
else
{
lean_object* v_a_5489_; lean_object* v___x_5491_; uint8_t v_isShared_5492_; uint8_t v_isSharedCheck_5496_; 
lean_dec_ref(v_type_5395_);
v_a_5489_ = lean_ctor_get(v___x_5417_, 0);
v_isSharedCheck_5496_ = !lean_is_exclusive(v___x_5417_);
if (v_isSharedCheck_5496_ == 0)
{
v___x_5491_ = v___x_5417_;
v_isShared_5492_ = v_isSharedCheck_5496_;
goto v_resetjp_5490_;
}
else
{
lean_inc(v_a_5489_);
lean_dec(v___x_5417_);
v___x_5491_ = lean_box(0);
v_isShared_5492_ = v_isSharedCheck_5496_;
goto v_resetjp_5490_;
}
v_resetjp_5490_:
{
lean_object* v___x_5494_; 
if (v_isShared_5492_ == 0)
{
v___x_5494_ = v___x_5491_;
goto v_reusejp_5493_;
}
else
{
lean_object* v_reuseFailAlloc_5495_; 
v_reuseFailAlloc_5495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5495_, 0, v_a_5489_);
v___x_5494_ = v_reuseFailAlloc_5495_;
goto v_reusejp_5493_;
}
v_reusejp_5493_:
{
return v___x_5494_;
}
}
}
}
}
}
else
{
lean_object* v_a_5498_; lean_object* v___x_5500_; uint8_t v_isShared_5501_; uint8_t v_isSharedCheck_5505_; 
lean_dec_ref(v_type_5395_);
v_a_5498_ = lean_ctor_get(v___x_5407_, 0);
v_isSharedCheck_5505_ = !lean_is_exclusive(v___x_5407_);
if (v_isSharedCheck_5505_ == 0)
{
v___x_5500_ = v___x_5407_;
v_isShared_5501_ = v_isSharedCheck_5505_;
goto v_resetjp_5499_;
}
else
{
lean_inc(v_a_5498_);
lean_dec(v___x_5407_);
v___x_5500_ = lean_box(0);
v_isShared_5501_ = v_isSharedCheck_5505_;
goto v_resetjp_5499_;
}
v_resetjp_5499_:
{
lean_object* v___x_5503_; 
if (v_isShared_5501_ == 0)
{
v___x_5503_ = v___x_5500_;
goto v_reusejp_5502_;
}
else
{
lean_object* v_reuseFailAlloc_5504_; 
v_reuseFailAlloc_5504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5504_, 0, v_a_5498_);
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
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_5395_ = stack[0].m_obj;
lean_object* v_a_5396_ = stack[1].m_obj;
lean_object* v_a_5397_ = stack[2].m_obj;
lean_object* v_a_5398_ = stack[3].m_obj;
lean_object* v_a_5399_ = stack[4].m_obj;
lean_object* v_a_5400_ = stack[5].m_obj;
lean_object* v_a_5401_ = stack[6].m_obj;
lean_object* v_a_5402_ = stack[7].m_obj;
lean_object* v_a_5403_ = stack[8].m_obj;
lean_object* v_a_5404_ = stack[9].m_obj;
lean_object* v_a_5405_ = stack[10].m_obj;
lean_object* v_res_5506_;
v_res_5506_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(v_type_5395_, v_a_5396_, v_a_5397_, v_a_5398_, v_a_5399_, v_a_5400_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_);
stack->m_obj
 = v_res_5506_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___boxed(lean_object* v_type_5507_, lean_object* v_a_5508_, lean_object* v_a_5509_, lean_object* v_a_5510_, lean_object* v_a_5511_, lean_object* v_a_5512_, lean_object* v_a_5513_, lean_object* v_a_5514_, lean_object* v_a_5515_, lean_object* v_a_5516_, lean_object* v_a_5517_, lean_object* v_a_5518_){
_start:
{
lean_object* v_res_5519_; 
v_res_5519_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(v_type_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_, v_a_5516_, v_a_5517_);
lean_dec(v_a_5517_);
lean_dec_ref(v_a_5516_);
lean_dec(v_a_5515_);
lean_dec_ref(v_a_5514_);
lean_dec(v_a_5513_);
lean_dec_ref(v_a_5512_);
lean_dec(v_a_5511_);
lean_dec_ref(v_a_5510_);
lean_dec(v_a_5509_);
lean_dec(v_a_5508_);
return v_res_5519_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0(lean_object* v_00_u03b2_5520_, lean_object* v_x_5521_, lean_object* v_x_5522_){
_start:
{
uint8_t v___x_5523_; 
v___x_5523_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_x_5521_, v_x_5522_);
return v___x_5523_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5521_ = stack[1].m_obj;
lean_object* v_x_5522_ = stack[2].m_obj;
uint8_t v_res_5524_;
v_res_5524_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0(lean_box(0), v_x_5521_, v_x_5522_);
stack->m_num = v_res_5524_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_5525_, lean_object* v_x_5526_, lean_object* v_x_5527_){
_start:
{
uint8_t v_res_5528_; lean_object* v_r_5529_; 
v_res_5528_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0(v_00_u03b2_5525_, v_x_5526_, v_x_5527_);
lean_dec_ref(v_x_5527_);
lean_dec_ref(v_x_5526_);
v_r_5529_ = lean_box(v_res_5528_);
return v_r_5529_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_5530_, lean_object* v_x_5531_, size_t v_x_5532_, lean_object* v_x_5533_){
_start:
{
uint8_t v___x_5534_; 
v___x_5534_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_5531_, v_x_5532_, v_x_5533_);
return v___x_5534_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5531_ = stack[1].m_obj;
size_t v_x_5532_ = stack[2].m_num;
lean_object* v_x_5533_ = stack[3].m_obj;
uint8_t v_res_5535_;
v_res_5535_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0(lean_box(0), v_x_5531_, v_x_5532_, v_x_5533_);
stack->m_num = v_res_5535_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5536_, lean_object* v_x_5537_, lean_object* v_x_5538_, lean_object* v_x_5539_){
_start:
{
size_t v_x_9099__boxed_5540_; uint8_t v_res_5541_; lean_object* v_r_5542_; 
v_x_9099__boxed_5540_ = lean_unbox_usize(v_x_5538_);
lean_dec(v_x_5538_);
v_res_5541_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0(v_00_u03b2_5536_, v_x_5537_, v_x_9099__boxed_5540_, v_x_5539_);
lean_dec_ref(v_x_5539_);
lean_dec_ref(v_x_5537_);
v_r_5542_ = lean_box(v_res_5541_);
return v_r_5542_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5543_, lean_object* v_keys_5544_, lean_object* v_vals_5545_, lean_object* v_heq_5546_, lean_object* v_i_5547_, lean_object* v_k_5548_){
_start:
{
uint8_t v___x_5549_; 
v___x_5549_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5544_, v_i_5547_, v_k_5548_);
return v___x_5549_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_5544_ = stack[1].m_obj;
lean_object* v_vals_5545_ = stack[2].m_obj;
lean_object* v_i_5547_ = stack[4].m_obj;
lean_object* v_k_5548_ = stack[5].m_obj;
uint8_t v_res_5550_;
v_res_5550_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1(lean_box(0), v_keys_5544_, v_vals_5545_, lean_box(0), v_i_5547_, v_k_5548_);
stack->m_num = v_res_5550_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5551_, lean_object* v_keys_5552_, lean_object* v_vals_5553_, lean_object* v_heq_5554_, lean_object* v_i_5555_, lean_object* v_k_5556_){
_start:
{
uint8_t v_res_5557_; lean_object* v_r_5558_; 
v_res_5557_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_5551_, v_keys_5552_, v_vals_5553_, v_heq_5554_, v_i_5555_, v_k_5556_);
lean_dec_ref(v_k_5556_);
lean_dec_ref(v_vals_5553_);
lean_dec_ref(v_keys_5552_);
v_r_5558_ = lean_box(v_res_5557_);
return v_r_5558_;
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
