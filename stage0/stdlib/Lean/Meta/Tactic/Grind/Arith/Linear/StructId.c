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
lean_object* lean_grind_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocessConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocessConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "`grind linarith` expected"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "\nto be definitionally equal to"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__2_value;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__3;
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1;
lean_object* lean_int_neg(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__2;
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst___boxed(lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(247, 129, 99, 43, 16, 237, 154, 169)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__5_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6_value;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 85, 184, 168, 121, 55, 74, 19)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "one"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__2_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 85, 184, 168, 121, 55, 74, 19)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(31, 134, 200, 93, 163, 253, 252, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__3_value;
lean_object* l_Lean_Meta_mkNumeral(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3;
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "HSMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(226, 107, 25, 48, 80, 144, 236, 217)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__1_value;
lean_object* l_Lean_Level_ofNat(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2;
extern lean_object* l_Lean_Int_mkType;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkType;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "hSMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(226, 107, 25, 48, 80, 144, 236, 217)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(23, 127, 6, 115, 121, 139, 223, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__1_value;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__0;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__2;
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__1(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__3_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__5;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__6;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__14_value),LEAN_SCALAR_PTR_LITERAL(192, 171, 244, 106, 217, 72, 118, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__14_value),LEAN_SCALAR_PTR_LITERAL(192, 171, 244, 106, 217, 72, 118, 253)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__16_value),LEAN_SCALAR_PTR_LITERAL(172, 37, 33, 120, 251, 36, 203, 36)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__18_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__18_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__19_value;
lean_object* l_Lean_mkRawNatLit(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__20;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__21_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__18_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__21_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__22_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__23_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__24_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__23_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__26_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__25_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__26_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__27_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__27_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__28_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__29_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__27_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__30_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__29_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__30_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "AddCommMonoid"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__31 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__31_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toZero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__32 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__32_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__33 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__33_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__34 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__34_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__34_value),LEAN_SCALAR_PTR_LITERAL(229, 81, 239, 34, 203, 244, 36, 133)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__35 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__35_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__36 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__36_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__37 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__37_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__37_value),LEAN_SCALAR_PTR_LITERAL(32, 225, 92, 14, 170, 61, 170, 140)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__38 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__38_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNeg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__39 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__39_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "zsmul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__40 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__40_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instHSMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__41 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__41_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__41_value),LEAN_SCALAR_PTR_LITERAL(131, 168, 246, 170, 1, 89, 173, 16)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__42 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__42_value;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__43;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "nsmul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__44 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__44_value;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__45;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__46 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__46_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__47_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__46_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__47 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__47_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__48 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__48_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "IsPartialOrder"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__49 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__49_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toIsPreorder"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__50 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__50_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__48_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__51_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__49_value),LEAN_SCALAR_PTR_LITERAL(196, 84, 36, 174, 137, 182, 135, 55)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__51_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__50_value),LEAN_SCALAR_PTR_LITERAL(75, 224, 25, 76, 51, 82, 222, 202)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__51 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__51_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "IsLinearOrder"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__52 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__52_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "toIsPartialOrder"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__53 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__53_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__48_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__54_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__52_value),LEAN_SCALAR_PTR_LITERAL(111, 211, 224, 54, 22, 32, 255, 113)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__54_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__53_value),LEAN_SCALAR_PTR_LITERAL(83, 108, 214, 71, 226, 119, 72, 107)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__54 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__54_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "toAddCommGroup"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__55 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__55_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__56_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__56_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__56_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__55_value),LEAN_SCALAR_PTR_LITERAL(205, 72, 3, 192, 99, 106, 67, 167)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__56 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__56_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "AddCommGroup"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__57 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__57_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "toAddCommMonoid"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__58 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__58_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__59_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__59_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__59_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__59_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__59_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__57_value),LEAN_SCALAR_PTR_LITERAL(64, 158, 132, 153, 136, 140, 172, 182)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__59_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__58_value),LEAN_SCALAR_PTR_LITERAL(143, 195, 31, 215, 150, 195, 138, 195)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__59 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__59_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Field"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__60 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__60_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__61_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__61_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__60_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__61 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__61_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__62 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__62_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__62_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__63 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__63_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__64 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__64_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__65_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__62_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__65_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__64_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__65 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__65_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "OrderedAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__66 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__66_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__67_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__67_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__67_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__67_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__66_value),LEAN_SCALAR_PTR_LITERAL(93, 134, 71, 250, 19, 181, 172, 227)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__67 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__67_value;
lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__12;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__13;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "`grind` unexpected failure, failure to initialize auxiliary `IntModule`"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__14_value;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__15;
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
lean_inc(x_7);
x_13 = lean_grind_canon(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_Meta_Sym_shareCommon___redArg(x_14, x_7);
lean_dec(x_7);
return x_15;
}
else
{
lean_dec(x_7);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocessConst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_box(0);
lean_inc(x_14);
x_17 = lean_grind_internalize(x_14, x_15, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_14);
return x_17;
}
else
{
lean_object* x_20; 
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_14);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_14);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocessConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocessConst(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = lean_grind_canon(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_Meta_Sym_shareCommon___redArg(x_14, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_box(0);
lean_inc(x_16);
x_19 = lean_grind_internalize(x_16, x_17, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_16);
return x_19;
}
else
{
lean_object* x_22; 
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_16);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_16);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__1;
x_5 = l_Lean_indentExpr(x_1);
x_6 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__3;
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_indentExpr(x_2);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(x_1, x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_8 = l_Lean_Meta_isDefEqD(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_free_object(x_8);
x_12 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(x_1, x_2);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(x_13, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_15 = lean_box(0);
lean_ctor_set(x_8, 0, x_15);
return x_8;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(x_1, x_2);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(x_19, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_23 = !lean_is_exclusive(x_8);
if (x_23 == 0)
{
return x_8;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_8, 0);
lean_inc(x_24);
lean_dec(x_8);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_usize_shift_right(x_3, x_4);
x_7 = lean_usize_to_nat(x_6);
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_10; 
lean_inc_ref(x_5);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = lean_ctor_get(x_2, 0);
lean_dec(x_11);
x_12 = 1;
x_13 = lean_usize_shift_left(x_12, x_4);
x_14 = lean_usize_sub(x_13, x_12);
x_15 = lean_usize_land(x_3, x_14);
x_16 = 5;
x_17 = lean_usize_sub(x_4, x_16);
x_18 = lean_array_fget(x_5, x_7);
x_19 = lean_box(0);
x_20 = lean_array_fset(x_5, x_7, x_19);
x_21 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0___redArg(x_1, x_18, x_15, x_17);
x_22 = lean_array_fset(x_20, x_7, x_21);
lean_dec(x_7);
lean_ctor_set(x_2, 0, x_22);
return x_2;
}
else
{
size_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_2);
x_23 = 1;
x_24 = lean_usize_shift_left(x_23, x_4);
x_25 = lean_usize_sub(x_24, x_23);
x_26 = lean_usize_land(x_3, x_25);
x_27 = 5;
x_28 = lean_usize_sub(x_4, x_27);
x_29 = lean_array_fget(x_5, x_7);
x_30 = lean_box(0);
x_31 = lean_array_fset(x_5, x_7, x_30);
x_32 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0___redArg(x_1, x_29, x_26, x_28);
x_33 = lean_array_fset(x_31, x_7, x_32);
lean_dec(x_7);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_2, 0);
x_36 = lean_usize_to_nat(x_3);
x_37 = lean_array_get_size(x_35);
x_38 = lean_nat_dec_lt(x_36, x_37);
if (x_38 == 0)
{
lean_dec(x_36);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_39; 
lean_inc_ref(x_35);
x_39 = !lean_is_exclusive(x_2);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_2, 0);
lean_dec(x_40);
x_41 = lean_array_fget(x_35, x_36);
x_42 = lean_box(0);
x_43 = lean_array_fset(x_35, x_36, x_42);
x_44 = lean_box(9);
x_45 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*2, x_38);
x_46 = l_Lean_PersistentArray_push___redArg(x_41, x_45);
x_47 = lean_array_fset(x_43, x_36, x_46);
lean_dec(x_36);
lean_ctor_set(x_2, 0, x_47);
return x_2;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_2);
x_48 = lean_array_fget(x_35, x_36);
x_49 = lean_box(0);
x_50 = lean_array_fset(x_35, x_36, x_49);
x_51 = lean_box(9);
x_52 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_38);
x_53 = l_Lean_PersistentArray_push___redArg(x_48, x_52);
x_54 = lean_array_fset(x_50, x_36, x_53);
lean_dec(x_36);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0___redArg(x_1, x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get_usize(x_3, 4);
x_9 = lean_ctor_get(x_3, 3);
x_10 = lean_nat_dec_le(x_9, x_4);
if (x_10 == 0)
{
size_t x_11; lean_object* x_12; 
x_11 = lean_usize_of_nat(x_4);
x_12 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0___redArg(x_1, x_6, x_11, x_8);
lean_ctor_set(x_3, 0, x_12);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_nat_sub(x_4, x_9);
x_14 = lean_array_get_size(x_7);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_array_fget(x_7, x_13);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_7, x_13, x_17);
x_19 = lean_box(9);
x_20 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_15);
x_21 = l_Lean_PersistentArray_push___redArg(x_16, x_20);
x_22 = lean_array_fset(x_18, x_13, x_21);
lean_dec(x_13);
lean_ctor_set(x_3, 1, x_22);
return x_3;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 1);
x_25 = lean_ctor_get(x_3, 2);
x_26 = lean_ctor_get_usize(x_3, 4);
x_27 = lean_ctor_get(x_3, 3);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
x_28 = lean_nat_dec_le(x_27, x_4);
if (x_28 == 0)
{
size_t x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_usize_of_nat(x_4);
x_30 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0___redArg(x_1, x_23, x_29, x_26);
x_31 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
lean_ctor_set(x_31, 2, x_25);
lean_ctor_set(x_31, 3, x_27);
lean_ctor_set_usize(x_31, 4, x_26);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_nat_sub(x_4, x_27);
x_33 = lean_array_get_size(x_24);
x_34 = lean_nat_dec_lt(x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_32);
lean_dec(x_1);
x_35 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_24);
lean_ctor_set(x_35, 2, x_25);
lean_ctor_set(x_35, 3, x_27);
lean_ctor_set_usize(x_35, 4, x_26);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_array_fget(x_24, x_32);
x_37 = lean_box(0);
x_38 = lean_array_fset(x_24, x_32, x_37);
x_39 = lean_box(9);
x_40 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_34);
x_41 = l_Lean_PersistentArray_push___redArg(x_36, x_40);
x_42 = lean_array_fset(x_38, x_32, x_41);
lean_dec(x_32);
x_43 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_43, 0, x_23);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_25);
lean_ctor_set(x_43, 3, x_27);
lean_ctor_set_usize(x_43, 4, x_26);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 2);
x_9 = lean_ctor_get(x_5, 3);
x_10 = lean_ctor_get(x_5, 4);
x_11 = lean_ctor_get(x_5, 5);
x_12 = lean_ctor_get(x_5, 6);
x_13 = lean_ctor_get(x_5, 7);
x_14 = lean_array_get_size(x_6);
x_15 = lean_nat_dec_lt(x_1, x_14);
if (x_15 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
uint8_t x_16; 
lean_inc_ref(x_13);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_17 = lean_ctor_get(x_5, 7);
lean_dec(x_17);
x_18 = lean_ctor_get(x_5, 6);
lean_dec(x_18);
x_19 = lean_ctor_get(x_5, 5);
lean_dec(x_19);
x_20 = lean_ctor_get(x_5, 4);
lean_dec(x_20);
x_21 = lean_ctor_get(x_5, 3);
lean_dec(x_21);
x_22 = lean_ctor_get(x_5, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_5, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_5, 0);
lean_dec(x_24);
x_25 = lean_array_fget(x_6, x_1);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_25, 32);
x_28 = lean_box(0);
x_29 = lean_array_fset(x_6, x_1, x_28);
x_30 = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0(x_2, x_3, x_27, x_4);
lean_ctor_set(x_25, 32, x_30);
x_31 = lean_array_fset(x_29, x_1, x_25);
lean_ctor_set(x_5, 0, x_31);
return x_5;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
x_34 = lean_ctor_get(x_25, 2);
x_35 = lean_ctor_get(x_25, 3);
x_36 = lean_ctor_get(x_25, 4);
x_37 = lean_ctor_get(x_25, 5);
x_38 = lean_ctor_get(x_25, 6);
x_39 = lean_ctor_get(x_25, 7);
x_40 = lean_ctor_get(x_25, 8);
x_41 = lean_ctor_get(x_25, 9);
x_42 = lean_ctor_get(x_25, 10);
x_43 = lean_ctor_get(x_25, 11);
x_44 = lean_ctor_get(x_25, 12);
x_45 = lean_ctor_get(x_25, 13);
x_46 = lean_ctor_get(x_25, 14);
x_47 = lean_ctor_get(x_25, 15);
x_48 = lean_ctor_get(x_25, 16);
x_49 = lean_ctor_get(x_25, 17);
x_50 = lean_ctor_get(x_25, 18);
x_51 = lean_ctor_get(x_25, 19);
x_52 = lean_ctor_get(x_25, 20);
x_53 = lean_ctor_get(x_25, 21);
x_54 = lean_ctor_get(x_25, 22);
x_55 = lean_ctor_get(x_25, 23);
x_56 = lean_ctor_get(x_25, 24);
x_57 = lean_ctor_get(x_25, 25);
x_58 = lean_ctor_get(x_25, 26);
x_59 = lean_ctor_get(x_25, 27);
x_60 = lean_ctor_get(x_25, 28);
x_61 = lean_ctor_get(x_25, 29);
x_62 = lean_ctor_get(x_25, 30);
x_63 = lean_ctor_get(x_25, 31);
x_64 = lean_ctor_get(x_25, 32);
x_65 = lean_ctor_get(x_25, 33);
x_66 = lean_ctor_get(x_25, 34);
x_67 = lean_ctor_get(x_25, 35);
x_68 = lean_ctor_get_uint8(x_25, sizeof(void*)*42);
x_69 = lean_ctor_get(x_25, 36);
x_70 = lean_ctor_get(x_25, 37);
x_71 = lean_ctor_get(x_25, 38);
x_72 = lean_ctor_get(x_25, 39);
x_73 = lean_ctor_get(x_25, 40);
x_74 = lean_ctor_get(x_25, 41);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_75 = lean_box(0);
x_76 = lean_array_fset(x_6, x_1, x_75);
x_77 = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0(x_2, x_3, x_64, x_4);
x_78 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_78, 0, x_32);
lean_ctor_set(x_78, 1, x_33);
lean_ctor_set(x_78, 2, x_34);
lean_ctor_set(x_78, 3, x_35);
lean_ctor_set(x_78, 4, x_36);
lean_ctor_set(x_78, 5, x_37);
lean_ctor_set(x_78, 6, x_38);
lean_ctor_set(x_78, 7, x_39);
lean_ctor_set(x_78, 8, x_40);
lean_ctor_set(x_78, 9, x_41);
lean_ctor_set(x_78, 10, x_42);
lean_ctor_set(x_78, 11, x_43);
lean_ctor_set(x_78, 12, x_44);
lean_ctor_set(x_78, 13, x_45);
lean_ctor_set(x_78, 14, x_46);
lean_ctor_set(x_78, 15, x_47);
lean_ctor_set(x_78, 16, x_48);
lean_ctor_set(x_78, 17, x_49);
lean_ctor_set(x_78, 18, x_50);
lean_ctor_set(x_78, 19, x_51);
lean_ctor_set(x_78, 20, x_52);
lean_ctor_set(x_78, 21, x_53);
lean_ctor_set(x_78, 22, x_54);
lean_ctor_set(x_78, 23, x_55);
lean_ctor_set(x_78, 24, x_56);
lean_ctor_set(x_78, 25, x_57);
lean_ctor_set(x_78, 26, x_58);
lean_ctor_set(x_78, 27, x_59);
lean_ctor_set(x_78, 28, x_60);
lean_ctor_set(x_78, 29, x_61);
lean_ctor_set(x_78, 30, x_62);
lean_ctor_set(x_78, 31, x_63);
lean_ctor_set(x_78, 32, x_77);
lean_ctor_set(x_78, 33, x_65);
lean_ctor_set(x_78, 34, x_66);
lean_ctor_set(x_78, 35, x_67);
lean_ctor_set(x_78, 36, x_69);
lean_ctor_set(x_78, 37, x_70);
lean_ctor_set(x_78, 38, x_71);
lean_ctor_set(x_78, 39, x_72);
lean_ctor_set(x_78, 40, x_73);
lean_ctor_set(x_78, 41, x_74);
lean_ctor_set_uint8(x_78, sizeof(void*)*42, x_68);
x_79 = lean_array_fset(x_76, x_1, x_78);
lean_ctor_set(x_5, 0, x_79);
return x_5;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_5);
x_80 = lean_array_fget(x_6, x_1);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_80, 2);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_80, 3);
lean_inc(x_84);
x_85 = lean_ctor_get(x_80, 4);
lean_inc_ref(x_85);
x_86 = lean_ctor_get(x_80, 5);
lean_inc(x_86);
x_87 = lean_ctor_get(x_80, 6);
lean_inc(x_87);
x_88 = lean_ctor_get(x_80, 7);
lean_inc(x_88);
x_89 = lean_ctor_get(x_80, 8);
lean_inc(x_89);
x_90 = lean_ctor_get(x_80, 9);
lean_inc(x_90);
x_91 = lean_ctor_get(x_80, 10);
lean_inc(x_91);
x_92 = lean_ctor_get(x_80, 11);
lean_inc(x_92);
x_93 = lean_ctor_get(x_80, 12);
lean_inc(x_93);
x_94 = lean_ctor_get(x_80, 13);
lean_inc(x_94);
x_95 = lean_ctor_get(x_80, 14);
lean_inc(x_95);
x_96 = lean_ctor_get(x_80, 15);
lean_inc(x_96);
x_97 = lean_ctor_get(x_80, 16);
lean_inc(x_97);
x_98 = lean_ctor_get(x_80, 17);
lean_inc_ref(x_98);
x_99 = lean_ctor_get(x_80, 18);
lean_inc_ref(x_99);
x_100 = lean_ctor_get(x_80, 19);
lean_inc(x_100);
x_101 = lean_ctor_get(x_80, 20);
lean_inc(x_101);
x_102 = lean_ctor_get(x_80, 21);
lean_inc(x_102);
x_103 = lean_ctor_get(x_80, 22);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_80, 23);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_80, 24);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_80, 25);
lean_inc(x_106);
x_107 = lean_ctor_get(x_80, 26);
lean_inc(x_107);
x_108 = lean_ctor_get(x_80, 27);
lean_inc(x_108);
x_109 = lean_ctor_get(x_80, 28);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_80, 29);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_80, 30);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_80, 31);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_80, 32);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_80, 33);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_80, 34);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_80, 35);
lean_inc_ref(x_116);
x_117 = lean_ctor_get_uint8(x_80, sizeof(void*)*42);
x_118 = lean_ctor_get(x_80, 36);
lean_inc(x_118);
x_119 = lean_ctor_get(x_80, 37);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_80, 38);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_80, 39);
lean_inc(x_121);
x_122 = lean_ctor_get(x_80, 40);
lean_inc_ref(x_122);
x_123 = lean_ctor_get(x_80, 41);
lean_inc_ref(x_123);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 lean_ctor_release(x_80, 2);
 lean_ctor_release(x_80, 3);
 lean_ctor_release(x_80, 4);
 lean_ctor_release(x_80, 5);
 lean_ctor_release(x_80, 6);
 lean_ctor_release(x_80, 7);
 lean_ctor_release(x_80, 8);
 lean_ctor_release(x_80, 9);
 lean_ctor_release(x_80, 10);
 lean_ctor_release(x_80, 11);
 lean_ctor_release(x_80, 12);
 lean_ctor_release(x_80, 13);
 lean_ctor_release(x_80, 14);
 lean_ctor_release(x_80, 15);
 lean_ctor_release(x_80, 16);
 lean_ctor_release(x_80, 17);
 lean_ctor_release(x_80, 18);
 lean_ctor_release(x_80, 19);
 lean_ctor_release(x_80, 20);
 lean_ctor_release(x_80, 21);
 lean_ctor_release(x_80, 22);
 lean_ctor_release(x_80, 23);
 lean_ctor_release(x_80, 24);
 lean_ctor_release(x_80, 25);
 lean_ctor_release(x_80, 26);
 lean_ctor_release(x_80, 27);
 lean_ctor_release(x_80, 28);
 lean_ctor_release(x_80, 29);
 lean_ctor_release(x_80, 30);
 lean_ctor_release(x_80, 31);
 lean_ctor_release(x_80, 32);
 lean_ctor_release(x_80, 33);
 lean_ctor_release(x_80, 34);
 lean_ctor_release(x_80, 35);
 lean_ctor_release(x_80, 36);
 lean_ctor_release(x_80, 37);
 lean_ctor_release(x_80, 38);
 lean_ctor_release(x_80, 39);
 lean_ctor_release(x_80, 40);
 lean_ctor_release(x_80, 41);
 x_124 = x_80;
} else {
 lean_dec_ref(x_80);
 x_124 = lean_box(0);
}
x_125 = lean_box(0);
x_126 = lean_array_fset(x_6, x_1, x_125);
x_127 = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0(x_2, x_3, x_113, x_4);
if (lean_is_scalar(x_124)) {
 x_128 = lean_alloc_ctor(0, 42, 1);
} else {
 x_128 = x_124;
}
lean_ctor_set(x_128, 0, x_81);
lean_ctor_set(x_128, 1, x_82);
lean_ctor_set(x_128, 2, x_83);
lean_ctor_set(x_128, 3, x_84);
lean_ctor_set(x_128, 4, x_85);
lean_ctor_set(x_128, 5, x_86);
lean_ctor_set(x_128, 6, x_87);
lean_ctor_set(x_128, 7, x_88);
lean_ctor_set(x_128, 8, x_89);
lean_ctor_set(x_128, 9, x_90);
lean_ctor_set(x_128, 10, x_91);
lean_ctor_set(x_128, 11, x_92);
lean_ctor_set(x_128, 12, x_93);
lean_ctor_set(x_128, 13, x_94);
lean_ctor_set(x_128, 14, x_95);
lean_ctor_set(x_128, 15, x_96);
lean_ctor_set(x_128, 16, x_97);
lean_ctor_set(x_128, 17, x_98);
lean_ctor_set(x_128, 18, x_99);
lean_ctor_set(x_128, 19, x_100);
lean_ctor_set(x_128, 20, x_101);
lean_ctor_set(x_128, 21, x_102);
lean_ctor_set(x_128, 22, x_103);
lean_ctor_set(x_128, 23, x_104);
lean_ctor_set(x_128, 24, x_105);
lean_ctor_set(x_128, 25, x_106);
lean_ctor_set(x_128, 26, x_107);
lean_ctor_set(x_128, 27, x_108);
lean_ctor_set(x_128, 28, x_109);
lean_ctor_set(x_128, 29, x_110);
lean_ctor_set(x_128, 30, x_111);
lean_ctor_set(x_128, 31, x_112);
lean_ctor_set(x_128, 32, x_127);
lean_ctor_set(x_128, 33, x_114);
lean_ctor_set(x_128, 34, x_115);
lean_ctor_set(x_128, 35, x_116);
lean_ctor_set(x_128, 36, x_118);
lean_ctor_set(x_128, 37, x_119);
lean_ctor_set(x_128, 38, x_120);
lean_ctor_set(x_128, 39, x_121);
lean_ctor_set(x_128, 40, x_122);
lean_ctor_set(x_128, 41, x_123);
lean_ctor_set_uint8(x_128, sizeof(void*)*42, x_117);
x_129 = lean_array_fset(x_126, x_1, x_128);
x_130 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_7);
lean_ctor_set(x_130, 2, x_8);
lean_ctor_set(x_130, 3, x_9);
lean_ctor_set(x_130, 4, x_10);
lean_ctor_set(x_130, 5, x_11);
lean_ctor_set(x_130, 6, x_12);
lean_ctor_set(x_130, 7, x_13);
return x_130;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0;
x_6 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__2;
x_7 = lean_box(0);
lean_inc(x_1);
x_8 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_5);
lean_closure_set(x_9, 3, x_1);
x_10 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_11 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_10, x_9, x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(x_1, x_2, x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0(x_1, x_2, x_3, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_usize_shift_right(x_3, x_4);
x_7 = lean_usize_to_nat(x_6);
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_10; 
lean_inc_ref(x_5);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = lean_ctor_get(x_2, 0);
lean_dec(x_11);
x_12 = 1;
x_13 = lean_usize_shift_left(x_12, x_4);
x_14 = lean_usize_sub(x_13, x_12);
x_15 = lean_usize_land(x_3, x_14);
x_16 = 5;
x_17 = lean_usize_sub(x_4, x_16);
x_18 = lean_array_fget(x_5, x_7);
x_19 = lean_box(0);
x_20 = lean_array_fset(x_5, x_7, x_19);
x_21 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0___redArg(x_1, x_18, x_15, x_17);
x_22 = lean_array_fset(x_20, x_7, x_21);
lean_dec(x_7);
lean_ctor_set(x_2, 0, x_22);
return x_2;
}
else
{
size_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_2);
x_23 = 1;
x_24 = lean_usize_shift_left(x_23, x_4);
x_25 = lean_usize_sub(x_24, x_23);
x_26 = lean_usize_land(x_3, x_25);
x_27 = 5;
x_28 = lean_usize_sub(x_4, x_27);
x_29 = lean_array_fget(x_5, x_7);
x_30 = lean_box(0);
x_31 = lean_array_fset(x_5, x_7, x_30);
x_32 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0___redArg(x_1, x_29, x_26, x_28);
x_33 = lean_array_fset(x_31, x_7, x_32);
lean_dec(x_7);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_2, 0);
x_36 = lean_usize_to_nat(x_3);
x_37 = lean_array_get_size(x_35);
x_38 = lean_nat_dec_lt(x_36, x_37);
if (x_38 == 0)
{
lean_dec(x_36);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_39; 
lean_inc_ref(x_35);
x_39 = !lean_is_exclusive(x_2);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_2, 0);
lean_dec(x_40);
x_41 = lean_array_fget(x_35, x_36);
x_42 = lean_box(0);
x_43 = lean_array_fset(x_35, x_36, x_42);
x_44 = lean_box(6);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_PersistentArray_push___redArg(x_41, x_45);
x_47 = lean_array_fset(x_43, x_36, x_46);
lean_dec(x_36);
lean_ctor_set(x_2, 0, x_47);
return x_2;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_2);
x_48 = lean_array_fget(x_35, x_36);
x_49 = lean_box(0);
x_50 = lean_array_fset(x_35, x_36, x_49);
x_51 = lean_box(6);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_PersistentArray_push___redArg(x_48, x_52);
x_54 = lean_array_fset(x_50, x_36, x_53);
lean_dec(x_36);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0___redArg(x_1, x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get_usize(x_3, 4);
x_9 = lean_ctor_get(x_3, 3);
x_10 = lean_nat_dec_le(x_9, x_4);
if (x_10 == 0)
{
size_t x_11; lean_object* x_12; 
x_11 = lean_usize_of_nat(x_4);
x_12 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0___redArg(x_1, x_6, x_11, x_8);
lean_ctor_set(x_3, 0, x_12);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_nat_sub(x_4, x_9);
x_14 = lean_array_get_size(x_7);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_array_fget(x_7, x_13);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_7, x_13, x_17);
x_19 = lean_box(6);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_PersistentArray_push___redArg(x_16, x_20);
x_22 = lean_array_fset(x_18, x_13, x_21);
lean_dec(x_13);
lean_ctor_set(x_3, 1, x_22);
return x_3;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 1);
x_25 = lean_ctor_get(x_3, 2);
x_26 = lean_ctor_get_usize(x_3, 4);
x_27 = lean_ctor_get(x_3, 3);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
x_28 = lean_nat_dec_le(x_27, x_4);
if (x_28 == 0)
{
size_t x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_usize_of_nat(x_4);
x_30 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0___redArg(x_1, x_23, x_29, x_26);
x_31 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
lean_ctor_set(x_31, 2, x_25);
lean_ctor_set(x_31, 3, x_27);
lean_ctor_set_usize(x_31, 4, x_26);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_nat_sub(x_4, x_27);
x_33 = lean_array_get_size(x_24);
x_34 = lean_nat_dec_lt(x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_32);
lean_dec(x_1);
x_35 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_24);
lean_ctor_set(x_35, 2, x_25);
lean_ctor_set(x_35, 3, x_27);
lean_ctor_set_usize(x_35, 4, x_26);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_array_fget(x_24, x_32);
x_37 = lean_box(0);
x_38 = lean_array_fset(x_24, x_32, x_37);
x_39 = lean_box(6);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_PersistentArray_push___redArg(x_36, x_40);
x_42 = lean_array_fset(x_38, x_32, x_41);
lean_dec(x_32);
x_43 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_43, 0, x_23);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_25);
lean_ctor_set(x_43, 3, x_27);
lean_ctor_set_usize(x_43, 4, x_26);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 2);
x_9 = lean_ctor_get(x_5, 3);
x_10 = lean_ctor_get(x_5, 4);
x_11 = lean_ctor_get(x_5, 5);
x_12 = lean_ctor_get(x_5, 6);
x_13 = lean_ctor_get(x_5, 7);
x_14 = lean_array_get_size(x_6);
x_15 = lean_nat_dec_lt(x_1, x_14);
if (x_15 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
uint8_t x_16; 
lean_inc_ref(x_13);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_17 = lean_ctor_get(x_5, 7);
lean_dec(x_17);
x_18 = lean_ctor_get(x_5, 6);
lean_dec(x_18);
x_19 = lean_ctor_get(x_5, 5);
lean_dec(x_19);
x_20 = lean_ctor_get(x_5, 4);
lean_dec(x_20);
x_21 = lean_ctor_get(x_5, 3);
lean_dec(x_21);
x_22 = lean_ctor_get(x_5, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_5, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_5, 0);
lean_dec(x_24);
x_25 = lean_array_fget(x_6, x_1);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_25, 34);
x_28 = lean_box(0);
x_29 = lean_array_fset(x_6, x_1, x_28);
x_30 = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0(x_2, x_3, x_27, x_4);
lean_ctor_set(x_25, 34, x_30);
x_31 = lean_array_fset(x_29, x_1, x_25);
lean_ctor_set(x_5, 0, x_31);
return x_5;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
x_34 = lean_ctor_get(x_25, 2);
x_35 = lean_ctor_get(x_25, 3);
x_36 = lean_ctor_get(x_25, 4);
x_37 = lean_ctor_get(x_25, 5);
x_38 = lean_ctor_get(x_25, 6);
x_39 = lean_ctor_get(x_25, 7);
x_40 = lean_ctor_get(x_25, 8);
x_41 = lean_ctor_get(x_25, 9);
x_42 = lean_ctor_get(x_25, 10);
x_43 = lean_ctor_get(x_25, 11);
x_44 = lean_ctor_get(x_25, 12);
x_45 = lean_ctor_get(x_25, 13);
x_46 = lean_ctor_get(x_25, 14);
x_47 = lean_ctor_get(x_25, 15);
x_48 = lean_ctor_get(x_25, 16);
x_49 = lean_ctor_get(x_25, 17);
x_50 = lean_ctor_get(x_25, 18);
x_51 = lean_ctor_get(x_25, 19);
x_52 = lean_ctor_get(x_25, 20);
x_53 = lean_ctor_get(x_25, 21);
x_54 = lean_ctor_get(x_25, 22);
x_55 = lean_ctor_get(x_25, 23);
x_56 = lean_ctor_get(x_25, 24);
x_57 = lean_ctor_get(x_25, 25);
x_58 = lean_ctor_get(x_25, 26);
x_59 = lean_ctor_get(x_25, 27);
x_60 = lean_ctor_get(x_25, 28);
x_61 = lean_ctor_get(x_25, 29);
x_62 = lean_ctor_get(x_25, 30);
x_63 = lean_ctor_get(x_25, 31);
x_64 = lean_ctor_get(x_25, 32);
x_65 = lean_ctor_get(x_25, 33);
x_66 = lean_ctor_get(x_25, 34);
x_67 = lean_ctor_get(x_25, 35);
x_68 = lean_ctor_get_uint8(x_25, sizeof(void*)*42);
x_69 = lean_ctor_get(x_25, 36);
x_70 = lean_ctor_get(x_25, 37);
x_71 = lean_ctor_get(x_25, 38);
x_72 = lean_ctor_get(x_25, 39);
x_73 = lean_ctor_get(x_25, 40);
x_74 = lean_ctor_get(x_25, 41);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_75 = lean_box(0);
x_76 = lean_array_fset(x_6, x_1, x_75);
x_77 = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0(x_2, x_3, x_66, x_4);
x_78 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_78, 0, x_32);
lean_ctor_set(x_78, 1, x_33);
lean_ctor_set(x_78, 2, x_34);
lean_ctor_set(x_78, 3, x_35);
lean_ctor_set(x_78, 4, x_36);
lean_ctor_set(x_78, 5, x_37);
lean_ctor_set(x_78, 6, x_38);
lean_ctor_set(x_78, 7, x_39);
lean_ctor_set(x_78, 8, x_40);
lean_ctor_set(x_78, 9, x_41);
lean_ctor_set(x_78, 10, x_42);
lean_ctor_set(x_78, 11, x_43);
lean_ctor_set(x_78, 12, x_44);
lean_ctor_set(x_78, 13, x_45);
lean_ctor_set(x_78, 14, x_46);
lean_ctor_set(x_78, 15, x_47);
lean_ctor_set(x_78, 16, x_48);
lean_ctor_set(x_78, 17, x_49);
lean_ctor_set(x_78, 18, x_50);
lean_ctor_set(x_78, 19, x_51);
lean_ctor_set(x_78, 20, x_52);
lean_ctor_set(x_78, 21, x_53);
lean_ctor_set(x_78, 22, x_54);
lean_ctor_set(x_78, 23, x_55);
lean_ctor_set(x_78, 24, x_56);
lean_ctor_set(x_78, 25, x_57);
lean_ctor_set(x_78, 26, x_58);
lean_ctor_set(x_78, 27, x_59);
lean_ctor_set(x_78, 28, x_60);
lean_ctor_set(x_78, 29, x_61);
lean_ctor_set(x_78, 30, x_62);
lean_ctor_set(x_78, 31, x_63);
lean_ctor_set(x_78, 32, x_64);
lean_ctor_set(x_78, 33, x_65);
lean_ctor_set(x_78, 34, x_77);
lean_ctor_set(x_78, 35, x_67);
lean_ctor_set(x_78, 36, x_69);
lean_ctor_set(x_78, 37, x_70);
lean_ctor_set(x_78, 38, x_71);
lean_ctor_set(x_78, 39, x_72);
lean_ctor_set(x_78, 40, x_73);
lean_ctor_set(x_78, 41, x_74);
lean_ctor_set_uint8(x_78, sizeof(void*)*42, x_68);
x_79 = lean_array_fset(x_76, x_1, x_78);
lean_ctor_set(x_5, 0, x_79);
return x_5;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_5);
x_80 = lean_array_fget(x_6, x_1);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_80, 2);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_80, 3);
lean_inc(x_84);
x_85 = lean_ctor_get(x_80, 4);
lean_inc_ref(x_85);
x_86 = lean_ctor_get(x_80, 5);
lean_inc(x_86);
x_87 = lean_ctor_get(x_80, 6);
lean_inc(x_87);
x_88 = lean_ctor_get(x_80, 7);
lean_inc(x_88);
x_89 = lean_ctor_get(x_80, 8);
lean_inc(x_89);
x_90 = lean_ctor_get(x_80, 9);
lean_inc(x_90);
x_91 = lean_ctor_get(x_80, 10);
lean_inc(x_91);
x_92 = lean_ctor_get(x_80, 11);
lean_inc(x_92);
x_93 = lean_ctor_get(x_80, 12);
lean_inc(x_93);
x_94 = lean_ctor_get(x_80, 13);
lean_inc(x_94);
x_95 = lean_ctor_get(x_80, 14);
lean_inc(x_95);
x_96 = lean_ctor_get(x_80, 15);
lean_inc(x_96);
x_97 = lean_ctor_get(x_80, 16);
lean_inc(x_97);
x_98 = lean_ctor_get(x_80, 17);
lean_inc_ref(x_98);
x_99 = lean_ctor_get(x_80, 18);
lean_inc_ref(x_99);
x_100 = lean_ctor_get(x_80, 19);
lean_inc(x_100);
x_101 = lean_ctor_get(x_80, 20);
lean_inc(x_101);
x_102 = lean_ctor_get(x_80, 21);
lean_inc(x_102);
x_103 = lean_ctor_get(x_80, 22);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_80, 23);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_80, 24);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_80, 25);
lean_inc(x_106);
x_107 = lean_ctor_get(x_80, 26);
lean_inc(x_107);
x_108 = lean_ctor_get(x_80, 27);
lean_inc(x_108);
x_109 = lean_ctor_get(x_80, 28);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_80, 29);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_80, 30);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_80, 31);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_80, 32);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_80, 33);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_80, 34);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_80, 35);
lean_inc_ref(x_116);
x_117 = lean_ctor_get_uint8(x_80, sizeof(void*)*42);
x_118 = lean_ctor_get(x_80, 36);
lean_inc(x_118);
x_119 = lean_ctor_get(x_80, 37);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_80, 38);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_80, 39);
lean_inc(x_121);
x_122 = lean_ctor_get(x_80, 40);
lean_inc_ref(x_122);
x_123 = lean_ctor_get(x_80, 41);
lean_inc_ref(x_123);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 lean_ctor_release(x_80, 2);
 lean_ctor_release(x_80, 3);
 lean_ctor_release(x_80, 4);
 lean_ctor_release(x_80, 5);
 lean_ctor_release(x_80, 6);
 lean_ctor_release(x_80, 7);
 lean_ctor_release(x_80, 8);
 lean_ctor_release(x_80, 9);
 lean_ctor_release(x_80, 10);
 lean_ctor_release(x_80, 11);
 lean_ctor_release(x_80, 12);
 lean_ctor_release(x_80, 13);
 lean_ctor_release(x_80, 14);
 lean_ctor_release(x_80, 15);
 lean_ctor_release(x_80, 16);
 lean_ctor_release(x_80, 17);
 lean_ctor_release(x_80, 18);
 lean_ctor_release(x_80, 19);
 lean_ctor_release(x_80, 20);
 lean_ctor_release(x_80, 21);
 lean_ctor_release(x_80, 22);
 lean_ctor_release(x_80, 23);
 lean_ctor_release(x_80, 24);
 lean_ctor_release(x_80, 25);
 lean_ctor_release(x_80, 26);
 lean_ctor_release(x_80, 27);
 lean_ctor_release(x_80, 28);
 lean_ctor_release(x_80, 29);
 lean_ctor_release(x_80, 30);
 lean_ctor_release(x_80, 31);
 lean_ctor_release(x_80, 32);
 lean_ctor_release(x_80, 33);
 lean_ctor_release(x_80, 34);
 lean_ctor_release(x_80, 35);
 lean_ctor_release(x_80, 36);
 lean_ctor_release(x_80, 37);
 lean_ctor_release(x_80, 38);
 lean_ctor_release(x_80, 39);
 lean_ctor_release(x_80, 40);
 lean_ctor_release(x_80, 41);
 x_124 = x_80;
} else {
 lean_dec_ref(x_80);
 x_124 = lean_box(0);
}
x_125 = lean_box(0);
x_126 = lean_array_fset(x_6, x_1, x_125);
x_127 = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0(x_2, x_3, x_115, x_4);
if (lean_is_scalar(x_124)) {
 x_128 = lean_alloc_ctor(0, 42, 1);
} else {
 x_128 = x_124;
}
lean_ctor_set(x_128, 0, x_81);
lean_ctor_set(x_128, 1, x_82);
lean_ctor_set(x_128, 2, x_83);
lean_ctor_set(x_128, 3, x_84);
lean_ctor_set(x_128, 4, x_85);
lean_ctor_set(x_128, 5, x_86);
lean_ctor_set(x_128, 6, x_87);
lean_ctor_set(x_128, 7, x_88);
lean_ctor_set(x_128, 8, x_89);
lean_ctor_set(x_128, 9, x_90);
lean_ctor_set(x_128, 10, x_91);
lean_ctor_set(x_128, 11, x_92);
lean_ctor_set(x_128, 12, x_93);
lean_ctor_set(x_128, 13, x_94);
lean_ctor_set(x_128, 14, x_95);
lean_ctor_set(x_128, 15, x_96);
lean_ctor_set(x_128, 16, x_97);
lean_ctor_set(x_128, 17, x_98);
lean_ctor_set(x_128, 18, x_99);
lean_ctor_set(x_128, 19, x_100);
lean_ctor_set(x_128, 20, x_101);
lean_ctor_set(x_128, 21, x_102);
lean_ctor_set(x_128, 22, x_103);
lean_ctor_set(x_128, 23, x_104);
lean_ctor_set(x_128, 24, x_105);
lean_ctor_set(x_128, 25, x_106);
lean_ctor_set(x_128, 26, x_107);
lean_ctor_set(x_128, 27, x_108);
lean_ctor_set(x_128, 28, x_109);
lean_ctor_set(x_128, 29, x_110);
lean_ctor_set(x_128, 30, x_111);
lean_ctor_set(x_128, 31, x_112);
lean_ctor_set(x_128, 32, x_113);
lean_ctor_set(x_128, 33, x_114);
lean_ctor_set(x_128, 34, x_127);
lean_ctor_set(x_128, 35, x_116);
lean_ctor_set(x_128, 36, x_118);
lean_ctor_set(x_128, 37, x_119);
lean_ctor_set(x_128, 38, x_120);
lean_ctor_set(x_128, 39, x_121);
lean_ctor_set(x_128, 40, x_122);
lean_ctor_set(x_128, 41, x_123);
lean_ctor_set_uint8(x_128, sizeof(void*)*42, x_117);
x_129 = lean_array_fset(x_126, x_1, x_128);
x_130 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_7);
lean_ctor_set(x_130, 2, x_8);
lean_ctor_set(x_130, 3, x_9);
lean_ctor_set(x_130, 4, x_10);
lean_ctor_set(x_130, 5, x_11);
lean_ctor_set(x_130, 6, x_12);
lean_ctor_set(x_130, 7, x_13);
return x_130;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0;
x_6 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1;
x_7 = lean_box(0);
lean_inc(x_1);
x_8 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_5);
lean_closure_set(x_9, 3, x_1);
x_10 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_11 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_10, x_9, x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(x_1, x_2, x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0(x_1, x_2, x_3, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_18; 
x_18 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*11 + 22);
lean_dec(x_19);
if (x_20 == 0)
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_21; 
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_dec_ref(x_21);
x_13 = lean_box(0);
goto block_17;
}
else
{
return x_21;
}
}
else
{
return x_21;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
block_17:
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = 0;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
x_17 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 4);
lean_inc_ref(x_20);
lean_dec(x_19);
lean_ctor_set(x_1, 0, x_20);
lean_ctor_set(x_17, 0, x_1);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_ctor_get(x_21, 4);
lean_inc_ref(x_22);
lean_dec(x_21);
lean_ctor_set(x_1, 0, x_22);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_1);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_free_object(x_1);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = 0;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_30 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_31, 4);
lean_inc_ref(x_33);
lean_dec(x_31);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
if (lean_is_scalar(x_32)) {
 x_35 = lean_alloc_ctor(0, 1, 0);
} else {
 x_35 = x_32;
}
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 1, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_36);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_1);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
uint8_t x_9; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4));
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_mkConst(x_11, x_13);
x_15 = l_Lean_mkAppB(x_14, x_2, x_10);
lean_ctor_set(x_3, 0, x_15);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_dec(x_3);
x_18 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4));
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_mkConst(x_18, x_20);
x_22 = l_Lean_mkAppB(x_21, x_2, x_17);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_3);
x_25 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6));
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_mkConst(x_25, x_27);
x_29 = l_Lean_Expr_app___override(x_28, x_2);
x_30 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_29, x_4, x_5, x_6, x_7);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(x_1, x_2, x_3, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
uint8_t x_9; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1));
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_mkConst(x_11, x_13);
x_15 = l_Lean_mkAppB(x_14, x_2, x_10);
lean_ctor_set(x_3, 0, x_15);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_dec(x_3);
x_18 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1));
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_mkConst(x_18, x_20);
x_22 = l_Lean_mkAppB(x_21, x_2, x_17);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_3);
x_25 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3));
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_mkConst(x_25, x_27);
x_29 = l_Lean_Expr_app___override(x_28, x_2);
x_30 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_29, x_4, x_5, x_6, x_7);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(x_1, x_2, x_3, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
uint8_t x_9; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1));
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_mkConst(x_11, x_13);
x_15 = l_Lean_mkAppB(x_14, x_2, x_10);
lean_ctor_set(x_3, 0, x_15);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_dec(x_3);
x_18 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1));
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_mkConst(x_18, x_20);
x_22 = l_Lean_mkAppB(x_21, x_2, x_17);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_3);
x_25 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__3));
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_mkConst(x_25, x_27);
x_29 = l_Lean_Expr_app___override(x_28, x_2);
x_30 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_29, x_4, x_5, x_6, x_7);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(x_1, x_2, x_3, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__1));
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
lean_inc_ref(x_16);
x_17 = l_Lean_mkConst(x_14, x_16);
lean_inc_ref(x_2);
x_18 = l_Lean_Expr_app___override(x_17, x_2);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_19 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_18, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_free_object(x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_23 = x_21;
} else {
 lean_dec_ref(x_21);
 x_23 = lean_box(0);
}
x_24 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__3));
x_25 = l_Lean_mkConst(x_24, x_16);
lean_inc_ref(x_2);
x_26 = l_Lean_mkAppB(x_25, x_2, x_22);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_27 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
x_34 = lean_unsigned_to_nat(1u);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_35 = l_Lean_Meta_mkNumeral(x_2, x_34, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_36);
lean_inc(x_28);
x_37 = l_Lean_Meta_isDefEqD(x_28, x_36, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = l_Lean_Meta_Grind_getConfig___redArg(x_5);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = lean_ctor_get_uint8(x_41, sizeof(void*)*11 + 14);
lean_dec(x_41);
if (x_42 == 0)
{
lean_dec(x_36);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_30 = lean_box(0);
goto block_33;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_inc(x_28);
x_43 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(x_28, x_36);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = l_Lean_Meta_Grind_reportIssue(x_44, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_45) == 0)
{
lean_dec_ref(x_45);
x_30 = lean_box(0);
goto block_33;
}
else
{
uint8_t x_46; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_23);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
return x_45;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_36);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_49 = !lean_is_exclusive(x_40);
if (x_49 == 0)
{
return x_40;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_40, 0);
lean_inc(x_50);
lean_dec(x_40);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
else
{
lean_dec(x_36);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_30 = lean_box(0);
goto block_33;
}
}
else
{
uint8_t x_52; 
lean_dec(x_36);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_52 = !lean_is_exclusive(x_37);
if (x_52 == 0)
{
return x_37;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_37, 0);
lean_inc(x_53);
lean_dec(x_37);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_35);
if (x_55 == 0)
{
return x_35;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_35, 0);
lean_inc(x_56);
lean_dec(x_35);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
block_33:
{
lean_object* x_31; lean_object* x_32; 
if (lean_is_scalar(x_23)) {
 x_31 = lean_alloc_ctor(1, 1, 0);
} else {
 x_31 = x_23;
}
lean_ctor_set(x_31, 0, x_28);
if (lean_is_scalar(x_29)) {
 x_32 = lean_alloc_ctor(0, 1, 0);
} else {
 x_32 = x_29;
}
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
else
{
uint8_t x_58; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_58 = !lean_is_exclusive(x_27);
if (x_58 == 0)
{
return x_27;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_27, 0);
lean_inc(x_59);
lean_dec(x_27);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; 
lean_dec(x_21);
lean_dec_ref(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_61 = lean_box(0);
lean_ctor_set(x_19, 0, x_61);
return x_19;
}
}
else
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_19, 0);
lean_inc(x_62);
lean_dec(x_19);
if (lean_obj_tag(x_62) == 1)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__3));
x_66 = l_Lean_mkConst(x_65, x_16);
lean_inc_ref(x_2);
x_67 = l_Lean_mkAppB(x_66, x_2, x_63);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_68 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(x_67, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
x_75 = lean_unsigned_to_nat(1u);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_76 = l_Lean_Meta_mkNumeral(x_2, x_75, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_77);
lean_inc(x_69);
x_78 = l_Lean_Meta_isDefEqD(x_69, x_77, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
x_80 = lean_unbox(x_79);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = l_Lean_Meta_Grind_getConfig___redArg(x_5);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
x_83 = lean_ctor_get_uint8(x_82, sizeof(void*)*11 + 14);
lean_dec(x_82);
if (x_83 == 0)
{
lean_dec(x_77);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_71 = lean_box(0);
goto block_74;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_inc(x_69);
x_84 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(x_69, x_77);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
x_86 = l_Lean_Meta_Grind_reportIssue(x_85, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_86) == 0)
{
lean_dec_ref(x_86);
x_71 = lean_box(0);
goto block_74;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_64);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 1, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_87);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_77);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_64);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_90 = lean_ctor_get(x_81, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_91 = x_81;
} else {
 lean_dec_ref(x_81);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 1, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_90);
return x_92;
}
}
else
{
lean_dec(x_77);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_71 = lean_box(0);
goto block_74;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_77);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_64);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_93 = lean_ctor_get(x_78, 0);
lean_inc(x_93);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 x_94 = x_78;
} else {
 lean_dec_ref(x_78);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 1, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_93);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_64);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_96 = lean_ctor_get(x_76, 0);
lean_inc(x_96);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_97 = x_76;
} else {
 lean_dec_ref(x_76);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 1, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_96);
return x_98;
}
block_74:
{
lean_object* x_72; lean_object* x_73; 
if (lean_is_scalar(x_64)) {
 x_72 = lean_alloc_ctor(1, 1, 0);
} else {
 x_72 = x_64;
}
lean_ctor_set(x_72, 0, x_69);
if (lean_is_scalar(x_70)) {
 x_73 = lean_alloc_ctor(0, 1, 0);
} else {
 x_73 = x_70;
}
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_64);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_99 = lean_ctor_get(x_68, 0);
lean_inc(x_99);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_100 = x_68;
} else {
 lean_dec_ref(x_68);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 1, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_99);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_62);
lean_dec_ref(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_102 = lean_box(0);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
}
}
else
{
lean_dec_ref(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
if (lean_obj_tag(x_3) == 1)
{
if (lean_obj_tag(x_4) == 1)
{
if (lean_obj_tag(x_5) == 1)
{
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_3, 0);
lean_inc(x_21);
lean_dec_ref(x_3);
x_22 = lean_ctor_get(x_4, 0);
lean_inc(x_22);
lean_dec_ref(x_4);
x_23 = lean_ctor_get(x_5, 0);
lean_inc(x_23);
lean_dec_ref(x_5);
x_24 = lean_ctor_get(x_6, 0);
lean_inc(x_24);
lean_dec_ref(x_6);
x_25 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__1));
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_mkConst(x_25, x_27);
x_29 = l_Lean_mkApp5(x_28, x_2, x_21, x_22, x_23, x_24);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc_ref(x_29);
x_30 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_29, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 1)
{
lean_dec_ref(x_31);
lean_dec_ref(x_29);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
return x_30;
}
else
{
lean_object* x_32; 
lean_dec(x_31);
lean_dec_ref(x_30);
x_32 = l_Lean_Meta_Grind_getConfig___redArg(x_8);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_ctor_get_uint8(x_33, sizeof(void*)*11 + 14);
lean_dec(x_33);
if (x_34 == 0)
{
lean_dec_ref(x_29);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
x_17 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3;
x_36 = l_Lean_indentExpr(x_29);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Meta_Grind_reportIssue(x_37, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
if (lean_obj_tag(x_38) == 0)
{
lean_dec_ref(x_38);
x_17 = lean_box(0);
goto block_20;
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec_ref(x_29);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
x_42 = !lean_is_exclusive(x_32);
if (x_42 == 0)
{
return x_32;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_32, 0);
lean_inc(x_43);
lean_dec(x_32);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
}
else
{
lean_dec_ref(x_29);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
return x_30;
}
}
else
{
uint8_t x_45; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_5);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_5, 0);
lean_dec(x_46);
x_47 = lean_box(0);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_47);
return x_5;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_5);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_4);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_4, 0);
lean_dec(x_51);
x_52 = lean_box(0);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_52);
return x_4;
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_4);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_3);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_3, 0);
lean_dec(x_56);
x_57 = lean_box(0);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_57);
return x_3;
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_3);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
block_20:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
x_18 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1));
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
lean_inc_ref(x_10);
x_11 = l_Lean_mkConst(x_8, x_10);
lean_inc_ref(x_2);
x_12 = l_Lean_Expr_app___override(x_11, x_2);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_13 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_12, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3));
x_18 = l_Lean_mkConst(x_17, x_10);
x_19 = l_Lean_mkAppB(x_18, x_2, x_16);
x_20 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_19, x_3, x_4, x_5, x_6);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_15);
lean_dec_ref(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_21 = lean_box(0);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3));
x_25 = l_Lean_mkConst(x_24, x_10);
x_26 = l_Lean_mkAppB(x_25, x_2, x_23);
x_27 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_26, x_3, x_4, x_5, x_6);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_22);
lean_dec_ref(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
lean_dec_ref(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(x_1, x_2, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_mkConst(x_1, x_10);
x_12 = l_Lean_Expr_app___override(x_11, x_3);
x_13 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_12, x_4, x_5, x_6, x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(x_1, x_2, x_3, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_mkConst(x_1, x_16);
x_18 = l_Lean_Expr_app___override(x_17, x_3);
x_19 = l_Lean_Meta_Grind_synthInstance(x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_box(0);
lean_inc(x_2);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
lean_inc(x_2);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_mkConst(x_1, x_18);
lean_inc_ref_n(x_3, 2);
x_20 = l_Lean_mkApp3(x_19, x_3, x_3, x_3);
x_21 = l_Lean_Meta_Grind_synthInstance(x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_21;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__1));
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2;
x_16 = lean_box(0);
lean_inc(x_1);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_mkConst(x_14, x_19);
x_21 = l_Lean_Int_mkType;
lean_inc_ref(x_2);
x_22 = l_Lean_mkApp3(x_20, x_21, x_2, x_2);
x_23 = l_Lean_Meta_Grind_synthInstance(x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_23;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__1));
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2;
x_16 = lean_box(0);
lean_inc(x_1);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_mkConst(x_14, x_19);
x_21 = l_Lean_Nat_mkType;
lean_inc_ref(x_2);
x_22 = l_Lean_mkApp3(x_20, x_21, x_2, x_2);
x_23 = l_Lean_Meta_Grind_synthInstance(x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_23;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
if (lean_obj_tag(x_1) == 1)
{
if (lean_obj_tag(x_2) == 1)
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec_ref(x_1);
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
lean_dec_ref(x_2);
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_mkConst(x_4, x_25);
lean_inc(x_23);
x_27 = l_Lean_mkApp3(x_26, x_6, x_21, x_23);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc_ref(x_27);
lean_inc(x_22);
x_28 = l_Lean_Meta_isDefEqD(x_22, x_27, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_free_object(x_28);
lean_dec_ref(x_3);
x_32 = l_Lean_Meta_Grind_getConfig___redArg(x_8);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_ctor_get_uint8(x_33, sizeof(void*)*11 + 14);
lean_dec(x_33);
if (x_34 == 0)
{
lean_dec_ref(x_27);
lean_dec(x_22);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
x_17 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(x_22, x_27);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = l_Lean_Meta_Grind_reportIssue(x_36, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
if (lean_obj_tag(x_37) == 0)
{
lean_dec_ref(x_37);
x_17 = lean_box(0);
goto block_20;
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
}
else
{
uint8_t x_41; 
lean_dec_ref(x_27);
lean_dec(x_22);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
return x_32;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_32, 0);
lean_inc(x_42);
lean_dec(x_32);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
else
{
lean_dec_ref(x_27);
lean_dec(x_22);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_ctor_set(x_28, 0, x_3);
return x_28;
}
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_28, 0);
lean_inc(x_44);
lean_dec(x_28);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec_ref(x_3);
x_46 = l_Lean_Meta_Grind_getConfig___redArg(x_8);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = lean_ctor_get_uint8(x_47, sizeof(void*)*11 + 14);
lean_dec(x_47);
if (x_48 == 0)
{
lean_dec_ref(x_27);
lean_dec(x_22);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
x_17 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(x_22, x_27);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = l_Lean_Meta_Grind_reportIssue(x_50, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
if (lean_obj_tag(x_51) == 0)
{
lean_dec_ref(x_51);
x_17 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 1, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_52);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec_ref(x_27);
lean_dec(x_22);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
x_55 = lean_ctor_get(x_46, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_56 = x_46;
} else {
 lean_dec_ref(x_46);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_55);
return x_57;
}
}
else
{
lean_object* x_58; 
lean_dec_ref(x_27);
lean_dec(x_22);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_3);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec_ref(x_27);
lean_dec(x_22);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_3);
x_59 = !lean_is_exclusive(x_28);
if (x_59 == 0)
{
return x_28;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_28, 0);
lean_inc(x_60);
lean_dec(x_28);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_62 = !lean_is_exclusive(x_2);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_2, 0);
lean_dec(x_63);
x_64 = lean_box(0);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_64);
return x_2;
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_2);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_1);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_1, 0);
lean_dec(x_68);
x_69 = lean_box(0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_69);
return x_1;
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_1);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
block_20:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
x_18 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_mkConst(x_3, x_12);
x_14 = l_Lean_mkAppB(x_13, x_5, x_2);
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(x_1, x_14, x_6, x_7, x_8, x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(x_1, x_2, x_3, x_4, x_5, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_13);
lean_inc_ref(x_14);
x_15 = l_Lean_mkConst(x_3, x_14);
lean_inc_ref(x_6);
x_16 = l_Lean_mkAppB(x_15, x_6, x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = l_Lean_mkConst(x_4, x_14);
x_18 = l_Lean_mkAppB(x_17, x_6, x_16);
x_19 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(x_1, x_18, x_8, x_9, x_10, x_11);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_7, 0);
lean_inc(x_20);
lean_dec_ref(x_7);
x_21 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2;
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_14);
x_23 = l_Lean_mkConst(x_4, x_22);
x_24 = l_Lean_mkApp3(x_23, x_20, x_6, x_16);
x_25 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(x_1, x_24, x_8, x_9, x_10, x_11);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; 
x_19 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14, x_15, x_16, x_17);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
lean_object* x_19; 
x_19 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__1));
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2;
x_16 = lean_box(0);
lean_inc(x_1);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
lean_inc_ref(x_19);
x_20 = l_Lean_mkConst(x_14, x_19);
x_21 = l_Lean_Int_mkType;
lean_inc_ref_n(x_2, 2);
x_22 = l_Lean_mkApp3(x_20, x_21, x_2, x_2);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_23 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_22, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
if (lean_obj_tag(x_25) == 1)
{
uint8_t x_26; 
lean_free_object(x_23);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__1));
x_29 = l_Lean_mkConst(x_28, x_19);
lean_inc_ref(x_2);
x_30 = l_Lean_mkApp4(x_29, x_21, x_2, x_2, x_27);
x_31 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_ctor_set(x_25, 0, x_33);
lean_ctor_set(x_31, 0, x_25);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
lean_dec(x_31);
lean_ctor_set(x_25, 0, x_34);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_25);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_free_object(x_25);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_25, 0);
lean_inc(x_39);
lean_dec(x_25);
x_40 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__1));
x_41 = l_Lean_mkConst(x_40, x_19);
lean_inc_ref(x_2);
x_42 = l_Lean_mkApp4(x_41, x_21, x_2, x_2, x_39);
x_43 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_44);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_43, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_49 = x_43;
} else {
 lean_dec_ref(x_43);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 1, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_48);
return x_50;
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_25);
lean_dec_ref(x_19);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_51 = lean_box(0);
lean_ctor_set(x_23, 0, x_51);
return x_23;
}
}
else
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_23, 0);
lean_inc(x_52);
lean_dec(x_23);
if (lean_obj_tag(x_52) == 1)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__1));
x_56 = l_Lean_mkConst(x_55, x_19);
lean_inc_ref(x_2);
x_57 = l_Lean_mkApp4(x_56, x_21, x_2, x_2, x_53);
x_58 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_61 = lean_alloc_ctor(1, 1, 0);
} else {
 x_61 = x_54;
}
lean_ctor_set(x_61, 0, x_59);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 1, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_54);
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_64 = x_58;
} else {
 lean_dec_ref(x_58);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_63);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_52);
lean_dec_ref(x_19);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
else
{
lean_dec_ref(x_19);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__1));
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2;
x_16 = lean_box(0);
lean_inc(x_1);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
lean_inc_ref(x_19);
x_20 = l_Lean_mkConst(x_14, x_19);
x_21 = l_Lean_Nat_mkType;
lean_inc_ref_n(x_2, 2);
x_22 = l_Lean_mkApp3(x_20, x_21, x_2, x_2);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_23 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_22, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
if (lean_obj_tag(x_25) == 1)
{
uint8_t x_26; 
lean_free_object(x_23);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__1));
x_29 = l_Lean_mkConst(x_28, x_19);
lean_inc_ref(x_2);
x_30 = l_Lean_mkApp4(x_29, x_21, x_2, x_2, x_27);
x_31 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_ctor_set(x_25, 0, x_33);
lean_ctor_set(x_31, 0, x_25);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
lean_dec(x_31);
lean_ctor_set(x_25, 0, x_34);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_25);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_free_object(x_25);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_25, 0);
lean_inc(x_39);
lean_dec(x_25);
x_40 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__1));
x_41 = l_Lean_mkConst(x_40, x_19);
lean_inc_ref(x_2);
x_42 = l_Lean_mkApp4(x_41, x_21, x_2, x_2, x_39);
x_43 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_44);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_43, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_49 = x_43;
} else {
 lean_dec_ref(x_43);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 1, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_48);
return x_50;
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_25);
lean_dec_ref(x_19);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_51 = lean_box(0);
lean_ctor_set(x_23, 0, x_51);
return x_23;
}
}
else
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_23, 0);
lean_inc(x_52);
lean_dec(x_23);
if (lean_obj_tag(x_52) == 1)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__1));
x_56 = l_Lean_mkConst(x_55, x_19);
lean_inc_ref(x_2);
x_57 = l_Lean_mkApp4(x_56, x_21, x_2, x_2, x_53);
x_58 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_61 = lean_alloc_ctor(1, 1, 0);
} else {
 x_61 = x_54;
}
lean_ctor_set(x_61, 0, x_59);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 1, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_54);
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_64 = x_58;
} else {
 lean_dec_ref(x_58);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_63);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_52);
lean_dec_ref(x_19);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
else
{
lean_dec_ref(x_19);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_array_push(x_6, x_3);
x_11 = lean_array_push(x_7, x_4);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_fget_borrowed(x_6, x_2);
x_13 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fset(x_6, x_2, x_3);
x_18 = lean_array_fset(x_7, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_23 = lean_array_push(x_19, x_3);
x_24 = lean_array_push(x_20, x_4);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_array_fget_borrowed(x_19, x_2);
x_27 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_2, x_29);
lean_dec(x_2);
x_1 = x_28;
x_2 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_array_fset(x_19, x_2, x_3);
x_33 = lean_array_fset(x_20, x_2, x_4);
lean_dec(x_2);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1_spec__2___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1;
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc_ref(x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_14 = x_1;
} else {
 lean_dec_ref(x_1);
 x_14 = lean_box(0);
}
x_15 = lean_array_fget(x_6, x_11);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_6, x_11, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
x_25 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_4, x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_15);
x_26 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_23, x_24, x_4, x_5);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_18 = x_27;
goto block_21;
}
else
{
lean_dec(x_24);
lean_dec(x_23);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_18 = x_15;
goto block_21;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_4, x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_28, x_29, x_4, x_5);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_18 = x_32;
goto block_21;
}
else
{
lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_5);
x_18 = x_33;
goto block_21;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_7);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_18 = x_15;
goto block_21;
}
else
{
lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_15, 0);
lean_inc(x_39);
lean_dec(x_15);
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg(x_39, x_40, x_41, x_4, x_5);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_18 = x_43;
goto block_21;
}
}
default: 
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_5);
x_18 = x_44;
goto block_21;
}
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fset(x_17, x_11, x_18);
lean_dec(x_11);
if (lean_is_scalar(x_14)) {
 x_20 = lean_alloc_ctor(0, 1, 0);
} else {
 x_20 = x_14;
}
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_1);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; size_t x_54; uint8_t x_55; 
x_46 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1___redArg(x_1, x_4, x_5);
x_54 = 7;
x_55 = lean_usize_dec_le(x_54, x_3);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_46);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_dec_lt(x_56, x_57);
lean_dec(x_56);
x_47 = x_58;
goto block_53;
}
else
{
x_47 = x_55;
goto block_53;
}
block_53:
{
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_46, 0);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_49);
lean_dec_ref(x_46);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__2;
x_52 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2___redArg(x_3, x_48, x_49, x_50, x_51);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
return x_52;
}
else
{
return x_46;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; size_t x_70; uint8_t x_71; 
x_59 = lean_ctor_get(x_1, 0);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_1);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1___redArg(x_61, x_4, x_5);
x_70 = 7;
x_71 = lean_usize_dec_le(x_70, x_3);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_62);
x_73 = lean_unsigned_to_nat(4u);
x_74 = lean_nat_dec_lt(x_72, x_73);
lean_dec(x_72);
x_63 = x_74;
goto block_69;
}
else
{
x_63 = x_71;
goto block_69;
}
block_69:
{
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_65);
lean_dec_ref(x_62);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__2;
x_68 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2___redArg(x_3, x_64, x_65, x_66, x_67);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
return x_68;
}
else
{
return x_62;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
x_10 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_8);
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 4);
x_5 = lean_box(0);
x_6 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0___redArg(x_4, x_1, x_5);
lean_ctor_set(x_2, 4, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 7);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0___redArg(x_11, x_1, x_15);
x_17 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_8);
lean_ctor_set(x_17, 2, x_9);
lean_ctor_set(x_17, 3, x_10);
lean_ctor_set(x_17, 4, x_16);
lean_ctor_set(x_17, 5, x_12);
lean_ctor_set(x_17, 6, x_13);
lean_ctor_set(x_17, 7, x_14);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_array_push(x_4, x_1);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get(x_2, 4);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_ctor_get(x_2, 6);
x_13 = lean_ctor_get(x_2, 7);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_14 = lean_array_push(x_6, x_1);
x_15 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
lean_ctor_set(x_15, 2, x_8);
lean_ctor_set(x_15, 3, x_9);
lean_ctor_set(x_15, 4, x_10);
lean_ctor_set(x_15, 5, x_11);
lean_ctor_set(x_15, 6, x_12);
lean_ctor_set(x_15, 7, x_13);
return x_15;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_mkRawNatLit(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Int_mkType;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Nat_mkType;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_18; lean_object* x_19; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_67; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
x_67 = l_Lean_Meta_getDecLevel_x3f(x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_67, 0);
if (lean_obj_tag(x_69) == 1)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_free_object(x_67);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_72 = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
x_75 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1));
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
lean_inc(x_70);
x_76 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(x_75, x_70, x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__3));
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
lean_inc(x_70);
x_79 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(x_78, x_70, x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_77);
lean_inc(x_80);
lean_inc_ref(x_1);
lean_inc(x_70);
x_81 = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(x_70, x_1, x_80, x_77, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_689; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_77);
lean_inc_ref(x_1);
lean_inc(x_70);
x_689 = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(x_70, x_1, x_77, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_689) == 0)
{
lean_object* x_690; lean_object* x_691; 
x_690 = lean_ctor_get(x_689, 0);
lean_inc(x_690);
lean_dec_ref(x_689);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_77);
lean_inc_ref(x_1);
lean_inc(x_70);
x_691 = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(x_70, x_1, x_77, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_691) == 0)
{
lean_object* x_692; lean_object* x_693; 
x_692 = lean_ctor_get(x_691, 0);
lean_inc(x_692);
lean_dec_ref(x_691);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_77);
lean_inc_ref(x_1);
lean_inc(x_70);
x_693 = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(x_70, x_1, x_77, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_693) == 0)
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; uint8_t x_716; lean_object* x_769; 
x_694 = lean_ctor_get(x_693, 0);
lean_inc(x_694);
lean_dec_ref(x_693);
x_769 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_769) == 0)
{
lean_object* x_770; uint8_t x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; uint8_t x_794; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; uint8_t x_826; lean_object* x_827; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; uint8_t x_855; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; uint8_t x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; uint8_t x_880; 
x_770 = lean_ctor_get(x_769, 0);
lean_inc(x_770);
lean_dec_ref(x_769);
x_771 = lean_ctor_get_uint8(x_770, sizeof(void*)*11 + 20);
lean_dec(x_770);
lean_inc_ref(x_1);
x_772 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(x_772, 0, x_1);
if (x_771 == 0)
{
x_880 = x_771;
goto block_963;
}
else
{
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_964; 
x_964 = 0;
x_880 = x_964;
goto block_963;
}
else
{
if (lean_obj_tag(x_690) == 0)
{
lean_object* x_965; lean_object* x_966; 
lean_dec(x_694);
lean_dec(x_692);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_965 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_966 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_965, x_772, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_966) == 0)
{
uint8_t x_967; 
x_967 = !lean_is_exclusive(x_966);
if (x_967 == 0)
{
lean_object* x_968; lean_object* x_969; 
x_968 = lean_ctor_get(x_966, 0);
lean_dec(x_968);
x_969 = lean_box(0);
lean_ctor_set(x_966, 0, x_969);
return x_966;
}
else
{
lean_object* x_970; lean_object* x_971; 
lean_dec(x_966);
x_970 = lean_box(0);
x_971 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_971, 0, x_970);
return x_971;
}
}
else
{
uint8_t x_972; 
x_972 = !lean_is_exclusive(x_966);
if (x_972 == 0)
{
return x_966;
}
else
{
lean_object* x_973; lean_object* x_974; 
x_973 = lean_ctor_get(x_966, 0);
lean_inc(x_973);
lean_dec(x_966);
x_974 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_974, 0, x_973);
return x_974;
}
}
}
else
{
uint8_t x_975; 
x_975 = 0;
x_880 = x_975;
goto block_963;
}
}
}
block_805:
{
if (lean_obj_tag(x_780) == 0)
{
lean_object* x_795; lean_object* x_796; 
lean_dec(x_792);
lean_dec(x_790);
lean_dec(x_789);
lean_dec_ref(x_788);
lean_dec(x_787);
lean_dec_ref(x_786);
lean_dec_ref(x_785);
lean_dec_ref(x_784);
lean_dec(x_783);
lean_dec_ref(x_782);
lean_dec(x_781);
lean_dec(x_779);
lean_dec(x_778);
lean_dec(x_777);
lean_dec_ref(x_776);
lean_dec(x_775);
lean_dec_ref(x_774);
lean_dec(x_773);
lean_dec(x_694);
lean_dec(x_692);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_795 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_796 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_795, x_772, x_793);
lean_dec(x_793);
if (lean_obj_tag(x_796) == 0)
{
uint8_t x_797; 
x_797 = !lean_is_exclusive(x_796);
if (x_797 == 0)
{
lean_object* x_798; lean_object* x_799; 
x_798 = lean_ctor_get(x_796, 0);
lean_dec(x_798);
x_799 = lean_box(0);
lean_ctor_set(x_796, 0, x_799);
return x_796;
}
else
{
lean_object* x_800; lean_object* x_801; 
lean_dec(x_796);
x_800 = lean_box(0);
x_801 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_801, 0, x_800);
return x_801;
}
}
else
{
uint8_t x_802; 
x_802 = !lean_is_exclusive(x_796);
if (x_802 == 0)
{
return x_796;
}
else
{
lean_object* x_803; lean_object* x_804; 
x_803 = lean_ctor_get(x_796, 0);
lean_inc(x_803);
lean_dec(x_796);
x_804 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_804, 0, x_803);
return x_804;
}
}
}
else
{
lean_dec_ref(x_772);
x_695 = x_773;
x_696 = x_774;
x_697 = x_775;
x_698 = x_776;
x_699 = x_777;
x_700 = x_778;
x_701 = x_779;
x_702 = x_780;
x_703 = x_781;
x_704 = x_782;
x_705 = x_784;
x_706 = x_783;
x_707 = x_785;
x_708 = x_787;
x_709 = x_786;
x_710 = x_788;
x_711 = x_789;
x_712 = x_790;
x_713 = lean_box(0);
x_714 = x_792;
x_715 = x_793;
x_716 = x_794;
goto block_768;
}
}
block_834:
{
lean_object* x_828; 
x_828 = l_Lean_Meta_Grind_getConfig___redArg(x_807);
if (lean_obj_tag(x_828) == 0)
{
lean_object* x_829; uint8_t x_830; 
x_829 = lean_ctor_get(x_828, 0);
lean_inc(x_829);
lean_dec_ref(x_828);
x_830 = lean_ctor_get_uint8(x_829, sizeof(void*)*11 + 20);
lean_dec(x_829);
if (x_830 == 0)
{
lean_dec_ref(x_772);
x_695 = x_806;
x_696 = x_807;
x_697 = x_808;
x_698 = x_809;
x_699 = x_810;
x_700 = x_812;
x_701 = x_813;
x_702 = x_827;
x_703 = x_814;
x_704 = x_815;
x_705 = x_816;
x_706 = x_817;
x_707 = x_818;
x_708 = x_820;
x_709 = x_819;
x_710 = x_821;
x_711 = x_822;
x_712 = x_823;
x_713 = lean_box(0);
x_714 = x_824;
x_715 = x_825;
x_716 = x_830;
goto block_768;
}
else
{
if (lean_obj_tag(x_73) == 0)
{
if (x_826 == 0)
{
lean_dec_ref(x_772);
x_695 = x_806;
x_696 = x_807;
x_697 = x_808;
x_698 = x_809;
x_699 = x_810;
x_700 = x_812;
x_701 = x_813;
x_702 = x_827;
x_703 = x_814;
x_704 = x_815;
x_705 = x_816;
x_706 = x_817;
x_707 = x_818;
x_708 = x_820;
x_709 = x_819;
x_710 = x_821;
x_711 = x_822;
x_712 = x_823;
x_713 = lean_box(0);
x_714 = x_824;
x_715 = x_825;
x_716 = x_826;
goto block_768;
}
else
{
x_773 = x_806;
x_774 = x_807;
x_775 = x_808;
x_776 = x_809;
x_777 = x_810;
x_778 = x_812;
x_779 = x_813;
x_780 = x_827;
x_781 = x_814;
x_782 = x_815;
x_783 = x_817;
x_784 = x_816;
x_785 = x_818;
x_786 = x_819;
x_787 = x_820;
x_788 = x_821;
x_789 = x_822;
x_790 = x_823;
x_791 = lean_box(0);
x_792 = x_824;
x_793 = x_825;
x_794 = x_826;
goto block_805;
}
}
else
{
x_773 = x_806;
x_774 = x_807;
x_775 = x_808;
x_776 = x_809;
x_777 = x_810;
x_778 = x_812;
x_779 = x_813;
x_780 = x_827;
x_781 = x_814;
x_782 = x_815;
x_783 = x_817;
x_784 = x_816;
x_785 = x_818;
x_786 = x_819;
x_787 = x_820;
x_788 = x_821;
x_789 = x_822;
x_790 = x_823;
x_791 = lean_box(0);
x_792 = x_824;
x_793 = x_825;
x_794 = x_826;
goto block_805;
}
}
}
else
{
uint8_t x_831; 
lean_dec(x_827);
lean_dec(x_825);
lean_dec(x_824);
lean_dec(x_823);
lean_dec(x_822);
lean_dec_ref(x_821);
lean_dec(x_820);
lean_dec_ref(x_819);
lean_dec_ref(x_818);
lean_dec(x_817);
lean_dec_ref(x_816);
lean_dec_ref(x_815);
lean_dec(x_814);
lean_dec(x_813);
lean_dec(x_812);
lean_dec(x_810);
lean_dec_ref(x_809);
lean_dec(x_808);
lean_dec_ref(x_807);
lean_dec(x_806);
lean_dec_ref(x_772);
lean_dec(x_694);
lean_dec(x_692);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_831 = !lean_is_exclusive(x_828);
if (x_831 == 0)
{
return x_828;
}
else
{
lean_object* x_832; lean_object* x_833; 
x_832 = lean_ctor_get(x_828, 0);
lean_inc(x_832);
lean_dec(x_828);
x_833 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_833, 0, x_832);
return x_833;
}
}
}
block_857:
{
lean_object* x_856; 
x_856 = lean_box(0);
x_806 = x_835;
x_807 = x_836;
x_808 = x_837;
x_809 = x_838;
x_810 = x_839;
x_811 = lean_box(0);
x_812 = x_841;
x_813 = x_842;
x_814 = x_843;
x_815 = x_844;
x_816 = x_845;
x_817 = x_846;
x_818 = x_847;
x_819 = x_849;
x_820 = x_848;
x_821 = x_850;
x_822 = x_851;
x_823 = x_852;
x_824 = x_853;
x_825 = x_854;
x_826 = x_855;
x_827 = x_856;
goto block_834;
}
block_879:
{
lean_object* x_878; 
x_878 = lean_box(0);
x_835 = x_876;
x_836 = x_869;
x_837 = x_874;
x_838 = x_873;
x_839 = x_863;
x_840 = lean_box(0);
x_841 = x_870;
x_842 = x_878;
x_843 = x_868;
x_844 = x_866;
x_845 = x_858;
x_846 = x_859;
x_847 = x_875;
x_848 = x_861;
x_849 = x_860;
x_850 = x_871;
x_851 = x_862;
x_852 = x_872;
x_853 = x_864;
x_854 = x_867;
x_855 = x_865;
goto block_857;
}
block_963:
{
lean_object* x_881; 
lean_inc(x_73);
x_881 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(x_73, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_881) == 0)
{
lean_object* x_882; lean_object* x_883; 
x_882 = lean_ctor_get(x_881, 0);
lean_inc(x_882);
lean_dec_ref(x_881);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_882);
lean_inc_ref(x_1);
lean_inc(x_70);
x_883 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(x_70, x_1, x_882, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_883) == 0)
{
lean_object* x_884; lean_object* x_885; 
x_884 = lean_ctor_get(x_883, 0);
lean_inc(x_884);
lean_dec_ref(x_883);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_884);
lean_inc_ref(x_1);
lean_inc(x_70);
x_885 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(x_70, x_1, x_884, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_885) == 0)
{
uint8_t x_886; 
x_886 = !lean_is_exclusive(x_885);
if (x_886 == 0)
{
lean_object* x_887; 
x_887 = lean_ctor_get(x_885, 0);
if (lean_obj_tag(x_887) == 1)
{
lean_object* x_888; lean_object* x_889; lean_object* x_890; 
lean_free_object(x_885);
x_888 = lean_ctor_get(x_887, 0);
lean_inc(x_888);
lean_dec_ref(x_887);
x_889 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__63));
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
lean_inc(x_70);
x_890 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(x_889, x_70, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_890) == 0)
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; 
x_891 = lean_ctor_get(x_890, 0);
lean_inc(x_891);
lean_dec_ref(x_890);
x_892 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__65));
x_893 = lean_box(0);
lean_inc(x_70);
x_894 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_894, 0, x_70);
lean_ctor_set(x_894, 1, x_893);
lean_inc_ref(x_894);
lean_inc(x_70);
x_895 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_895, 0, x_70);
lean_ctor_set(x_895, 1, x_894);
lean_inc_ref(x_895);
lean_inc(x_70);
x_896 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_896, 0, x_70);
lean_ctor_set(x_896, 1, x_895);
lean_inc_ref(x_896);
x_897 = l_Lean_mkConst(x_892, x_896);
lean_inc(x_891);
lean_inc_ref_n(x_1, 3);
x_898 = l_Lean_mkApp4(x_897, x_1, x_1, x_1, x_891);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_899 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_898, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_899) == 0)
{
if (lean_obj_tag(x_77) == 1)
{
if (lean_obj_tag(x_690) == 1)
{
lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; 
x_900 = lean_ctor_get(x_899, 0);
lean_inc(x_900);
lean_dec_ref(x_899);
x_901 = lean_ctor_get(x_77, 0);
x_902 = lean_ctor_get(x_690, 0);
x_903 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__67));
lean_inc_ref(x_894);
x_904 = l_Lean_mkConst(x_903, x_894);
lean_inc(x_902);
lean_inc(x_901);
lean_inc(x_891);
lean_inc_ref(x_1);
x_905 = l_Lean_mkApp4(x_904, x_1, x_891, x_901, x_902);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_906 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_905, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_906) == 0)
{
lean_object* x_907; 
x_907 = lean_ctor_get(x_906, 0);
lean_inc(x_907);
lean_dec_ref(x_906);
if (lean_obj_tag(x_907) == 0)
{
lean_dec_ref(x_690);
x_835 = x_11;
x_836 = x_4;
x_837 = x_9;
x_838 = x_8;
x_839 = x_882;
x_840 = lean_box(0);
x_841 = x_5;
x_842 = x_907;
x_843 = x_3;
x_844 = x_888;
x_845 = x_900;
x_846 = x_894;
x_847 = x_10;
x_848 = x_896;
x_849 = x_891;
x_850 = x_6;
x_851 = x_895;
x_852 = x_7;
x_853 = x_884;
x_854 = x_2;
x_855 = x_880;
goto block_857;
}
else
{
if (x_880 == 0)
{
x_806 = x_11;
x_807 = x_4;
x_808 = x_9;
x_809 = x_8;
x_810 = x_882;
x_811 = lean_box(0);
x_812 = x_5;
x_813 = x_907;
x_814 = x_3;
x_815 = x_888;
x_816 = x_900;
x_817 = x_894;
x_818 = x_10;
x_819 = x_891;
x_820 = x_896;
x_821 = x_6;
x_822 = x_895;
x_823 = x_7;
x_824 = x_884;
x_825 = x_2;
x_826 = x_880;
x_827 = x_690;
goto block_834;
}
else
{
lean_dec_ref(x_690);
x_835 = x_11;
x_836 = x_4;
x_837 = x_9;
x_838 = x_8;
x_839 = x_882;
x_840 = lean_box(0);
x_841 = x_5;
x_842 = x_907;
x_843 = x_3;
x_844 = x_888;
x_845 = x_900;
x_846 = x_894;
x_847 = x_10;
x_848 = x_896;
x_849 = x_891;
x_850 = x_6;
x_851 = x_895;
x_852 = x_7;
x_853 = x_884;
x_854 = x_2;
x_855 = x_880;
goto block_857;
}
}
}
else
{
uint8_t x_908; 
lean_dec(x_900);
lean_dec_ref(x_896);
lean_dec_ref(x_895);
lean_dec_ref(x_894);
lean_dec(x_891);
lean_dec(x_888);
lean_dec(x_884);
lean_dec(x_882);
lean_dec_ref(x_772);
lean_dec(x_694);
lean_dec(x_692);
lean_dec_ref(x_690);
lean_dec(x_82);
lean_dec(x_80);
lean_dec_ref(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_908 = !lean_is_exclusive(x_906);
if (x_908 == 0)
{
return x_906;
}
else
{
lean_object* x_909; lean_object* x_910; 
x_909 = lean_ctor_get(x_906, 0);
lean_inc(x_909);
lean_dec(x_906);
x_910 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_910, 0, x_909);
return x_910;
}
}
}
else
{
lean_object* x_911; 
lean_dec(x_690);
x_911 = lean_ctor_get(x_899, 0);
lean_inc(x_911);
lean_dec_ref(x_899);
x_858 = x_911;
x_859 = x_894;
x_860 = x_891;
x_861 = x_896;
x_862 = x_895;
x_863 = x_882;
x_864 = x_884;
x_865 = x_880;
x_866 = x_888;
x_867 = x_2;
x_868 = x_3;
x_869 = x_4;
x_870 = x_5;
x_871 = x_6;
x_872 = x_7;
x_873 = x_8;
x_874 = x_9;
x_875 = x_10;
x_876 = x_11;
x_877 = lean_box(0);
goto block_879;
}
}
else
{
lean_object* x_912; 
lean_dec(x_690);
x_912 = lean_ctor_get(x_899, 0);
lean_inc(x_912);
lean_dec_ref(x_899);
x_858 = x_912;
x_859 = x_894;
x_860 = x_891;
x_861 = x_896;
x_862 = x_895;
x_863 = x_882;
x_864 = x_884;
x_865 = x_880;
x_866 = x_888;
x_867 = x_2;
x_868 = x_3;
x_869 = x_4;
x_870 = x_5;
x_871 = x_6;
x_872 = x_7;
x_873 = x_8;
x_874 = x_9;
x_875 = x_10;
x_876 = x_11;
x_877 = lean_box(0);
goto block_879;
}
}
else
{
uint8_t x_913; 
lean_dec_ref(x_896);
lean_dec_ref(x_895);
lean_dec_ref(x_894);
lean_dec(x_891);
lean_dec(x_888);
lean_dec(x_884);
lean_dec(x_882);
lean_dec_ref(x_772);
lean_dec(x_694);
lean_dec(x_692);
lean_dec(x_690);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_913 = !lean_is_exclusive(x_899);
if (x_913 == 0)
{
return x_899;
}
else
{
lean_object* x_914; lean_object* x_915; 
x_914 = lean_ctor_get(x_899, 0);
lean_inc(x_914);
lean_dec(x_899);
x_915 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_915, 0, x_914);
return x_915;
}
}
}
else
{
uint8_t x_916; 
lean_dec(x_888);
lean_dec(x_884);
lean_dec(x_882);
lean_dec_ref(x_772);
lean_dec(x_694);
lean_dec(x_692);
lean_dec(x_690);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_916 = !lean_is_exclusive(x_890);
if (x_916 == 0)
{
return x_890;
}
else
{
lean_object* x_917; lean_object* x_918; 
x_917 = lean_ctor_get(x_890, 0);
lean_inc(x_917);
lean_dec(x_890);
x_918 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_918, 0, x_917);
return x_918;
}
}
}
else
{
lean_object* x_919; 
lean_dec(x_887);
lean_dec(x_884);
lean_dec(x_882);
lean_dec_ref(x_772);
lean_dec(x_694);
lean_dec(x_692);
lean_dec(x_690);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_919 = lean_box(0);
lean_ctor_set(x_885, 0, x_919);
return x_885;
}
}
else
{
lean_object* x_920; 
x_920 = lean_ctor_get(x_885, 0);
lean_inc(x_920);
lean_dec(x_885);
if (lean_obj_tag(x_920) == 1)
{
lean_object* x_921; lean_object* x_922; lean_object* x_923; 
x_921 = lean_ctor_get(x_920, 0);
lean_inc(x_921);
lean_dec_ref(x_920);
x_922 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__63));
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
lean_inc(x_70);
x_923 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(x_922, x_70, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_923) == 0)
{
lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; 
x_924 = lean_ctor_get(x_923, 0);
lean_inc(x_924);
lean_dec_ref(x_923);
x_925 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__65));
x_926 = lean_box(0);
lean_inc(x_70);
x_927 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_927, 0, x_70);
lean_ctor_set(x_927, 1, x_926);
lean_inc_ref(x_927);
lean_inc(x_70);
x_928 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_928, 0, x_70);
lean_ctor_set(x_928, 1, x_927);
lean_inc_ref(x_928);
lean_inc(x_70);
x_929 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_929, 0, x_70);
lean_ctor_set(x_929, 1, x_928);
lean_inc_ref(x_929);
x_930 = l_Lean_mkConst(x_925, x_929);
lean_inc(x_924);
lean_inc_ref_n(x_1, 3);
x_931 = l_Lean_mkApp4(x_930, x_1, x_1, x_1, x_924);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_932 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_931, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_932) == 0)
{
if (lean_obj_tag(x_77) == 1)
{
if (lean_obj_tag(x_690) == 1)
{
lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; 
x_933 = lean_ctor_get(x_932, 0);
lean_inc(x_933);
lean_dec_ref(x_932);
x_934 = lean_ctor_get(x_77, 0);
x_935 = lean_ctor_get(x_690, 0);
x_936 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__67));
lean_inc_ref(x_927);
x_937 = l_Lean_mkConst(x_936, x_927);
lean_inc(x_935);
lean_inc(x_934);
lean_inc(x_924);
lean_inc_ref(x_1);
x_938 = l_Lean_mkApp4(x_937, x_1, x_924, x_934, x_935);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_939 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_938, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_939) == 0)
{
lean_object* x_940; 
x_940 = lean_ctor_get(x_939, 0);
lean_inc(x_940);
lean_dec_ref(x_939);
if (lean_obj_tag(x_940) == 0)
{
lean_dec_ref(x_690);
x_835 = x_11;
x_836 = x_4;
x_837 = x_9;
x_838 = x_8;
x_839 = x_882;
x_840 = lean_box(0);
x_841 = x_5;
x_842 = x_940;
x_843 = x_3;
x_844 = x_921;
x_845 = x_933;
x_846 = x_927;
x_847 = x_10;
x_848 = x_929;
x_849 = x_924;
x_850 = x_6;
x_851 = x_928;
x_852 = x_7;
x_853 = x_884;
x_854 = x_2;
x_855 = x_880;
goto block_857;
}
else
{
if (x_880 == 0)
{
x_806 = x_11;
x_807 = x_4;
x_808 = x_9;
x_809 = x_8;
x_810 = x_882;
x_811 = lean_box(0);
x_812 = x_5;
x_813 = x_940;
x_814 = x_3;
x_815 = x_921;
x_816 = x_933;
x_817 = x_927;
x_818 = x_10;
x_819 = x_924;
x_820 = x_929;
x_821 = x_6;
x_822 = x_928;
x_823 = x_7;
x_824 = x_884;
x_825 = x_2;
x_826 = x_880;
x_827 = x_690;
goto block_834;
}
else
{
lean_dec_ref(x_690);
x_835 = x_11;
x_836 = x_4;
x_837 = x_9;
x_838 = x_8;
x_839 = x_882;
x_840 = lean_box(0);
x_841 = x_5;
x_842 = x_940;
x_843 = x_3;
x_844 = x_921;
x_845 = x_933;
x_846 = x_927;
x_847 = x_10;
x_848 = x_929;
x_849 = x_924;
x_850 = x_6;
x_851 = x_928;
x_852 = x_7;
x_853 = x_884;
x_854 = x_2;
x_855 = x_880;
goto block_857;
}
}
}
else
{
lean_object* x_941; lean_object* x_942; lean_object* x_943; 
lean_dec(x_933);
lean_dec_ref(x_929);
lean_dec_ref(x_928);
lean_dec_ref(x_927);
lean_dec(x_924);
lean_dec(x_921);
lean_dec(x_884);
lean_dec(x_882);
lean_dec_ref(x_772);
lean_dec(x_694);
lean_dec(x_692);
lean_dec_ref(x_690);
lean_dec(x_82);
lean_dec(x_80);
lean_dec_ref(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_941 = lean_ctor_get(x_939, 0);
lean_inc(x_941);
if (lean_is_exclusive(x_939)) {
 lean_ctor_release(x_939, 0);
 x_942 = x_939;
} else {
 lean_dec_ref(x_939);
 x_942 = lean_box(0);
}
if (lean_is_scalar(x_942)) {
 x_943 = lean_alloc_ctor(1, 1, 0);
} else {
 x_943 = x_942;
}
lean_ctor_set(x_943, 0, x_941);
return x_943;
}
}
else
{
lean_object* x_944; 
lean_dec(x_690);
x_944 = lean_ctor_get(x_932, 0);
lean_inc(x_944);
lean_dec_ref(x_932);
x_858 = x_944;
x_859 = x_927;
x_860 = x_924;
x_861 = x_929;
x_862 = x_928;
x_863 = x_882;
x_864 = x_884;
x_865 = x_880;
x_866 = x_921;
x_867 = x_2;
x_868 = x_3;
x_869 = x_4;
x_870 = x_5;
x_871 = x_6;
x_872 = x_7;
x_873 = x_8;
x_874 = x_9;
x_875 = x_10;
x_876 = x_11;
x_877 = lean_box(0);
goto block_879;
}
}
else
{
lean_object* x_945; 
lean_dec(x_690);
x_945 = lean_ctor_get(x_932, 0);
lean_inc(x_945);
lean_dec_ref(x_932);
x_858 = x_945;
x_859 = x_927;
x_860 = x_924;
x_861 = x_929;
x_862 = x_928;
x_863 = x_882;
x_864 = x_884;
x_865 = x_880;
x_866 = x_921;
x_867 = x_2;
x_868 = x_3;
x_869 = x_4;
x_870 = x_5;
x_871 = x_6;
x_872 = x_7;
x_873 = x_8;
x_874 = x_9;
x_875 = x_10;
x_876 = x_11;
x_877 = lean_box(0);
goto block_879;
}
}
else
{
lean_object* x_946; lean_object* x_947; lean_object* x_948; 
lean_dec_ref(x_929);
lean_dec_ref(x_928);
lean_dec_ref(x_927);
lean_dec(x_924);
lean_dec(x_921);
lean_dec(x_884);
lean_dec(x_882);
lean_dec_ref(x_772);
lean_dec(x_694);
lean_dec(x_692);
lean_dec(x_690);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_946 = lean_ctor_get(x_932, 0);
lean_inc(x_946);
if (lean_is_exclusive(x_932)) {
 lean_ctor_release(x_932, 0);
 x_947 = x_932;
} else {
 lean_dec_ref(x_932);
 x_947 = lean_box(0);
}
if (lean_is_scalar(x_947)) {
 x_948 = lean_alloc_ctor(1, 1, 0);
} else {
 x_948 = x_947;
}
lean_ctor_set(x_948, 0, x_946);
return x_948;
}
}
else
{
lean_object* x_949; lean_object* x_950; lean_object* x_951; 
lean_dec(x_921);
lean_dec(x_884);
lean_dec(x_882);
lean_dec_ref(x_772);
lean_dec(x_694);
lean_dec(x_692);
lean_dec(x_690);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_949 = lean_ctor_get(x_923, 0);
lean_inc(x_949);
if (lean_is_exclusive(x_923)) {
 lean_ctor_release(x_923, 0);
 x_950 = x_923;
} else {
 lean_dec_ref(x_923);
 x_950 = lean_box(0);
}
if (lean_is_scalar(x_950)) {
 x_951 = lean_alloc_ctor(1, 1, 0);
} else {
 x_951 = x_950;
}
lean_ctor_set(x_951, 0, x_949);
return x_951;
}
}
else
{
lean_object* x_952; lean_object* x_953; 
lean_dec(x_920);
lean_dec(x_884);
lean_dec(x_882);
lean_dec_ref(x_772);
lean_dec(x_694);
lean_dec(x_692);
lean_dec(x_690);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_952 = lean_box(0);
x_953 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_953, 0, x_952);
return x_953;
}
}
}
else
{
uint8_t x_954; 
lean_dec(x_884);
lean_dec(x_882);
lean_dec_ref(x_772);
lean_dec(x_694);
lean_dec(x_692);
lean_dec(x_690);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_954 = !lean_is_exclusive(x_885);
if (x_954 == 0)
{
return x_885;
}
else
{
lean_object* x_955; lean_object* x_956; 
x_955 = lean_ctor_get(x_885, 0);
lean_inc(x_955);
lean_dec(x_885);
x_956 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_956, 0, x_955);
return x_956;
}
}
}
else
{
uint8_t x_957; 
lean_dec(x_882);
lean_dec_ref(x_772);
lean_dec(x_694);
lean_dec(x_692);
lean_dec(x_690);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_957 = !lean_is_exclusive(x_883);
if (x_957 == 0)
{
return x_883;
}
else
{
lean_object* x_958; lean_object* x_959; 
x_958 = lean_ctor_get(x_883, 0);
lean_inc(x_958);
lean_dec(x_883);
x_959 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_959, 0, x_958);
return x_959;
}
}
}
else
{
uint8_t x_960; 
lean_dec_ref(x_772);
lean_dec(x_694);
lean_dec(x_692);
lean_dec(x_690);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_960 = !lean_is_exclusive(x_881);
if (x_960 == 0)
{
return x_881;
}
else
{
lean_object* x_961; lean_object* x_962; 
x_961 = lean_ctor_get(x_881, 0);
lean_inc(x_961);
lean_dec(x_881);
x_962 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_962, 0, x_961);
return x_962;
}
}
}
}
else
{
uint8_t x_976; 
lean_dec(x_694);
lean_dec(x_692);
lean_dec(x_690);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_976 = !lean_is_exclusive(x_769);
if (x_976 == 0)
{
return x_769;
}
else
{
lean_object* x_977; lean_object* x_978; 
x_977 = lean_ctor_get(x_769, 0);
lean_inc(x_977);
lean_dec(x_769);
x_978 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_978, 0, x_977);
return x_978;
}
}
block_768:
{
lean_object* x_717; lean_object* x_718; 
x_717 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__51));
lean_inc(x_695);
lean_inc_ref(x_707);
lean_inc(x_697);
lean_inc_ref(x_698);
lean_inc_ref(x_1);
lean_inc(x_70);
lean_inc(x_702);
lean_inc(x_77);
x_718 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(x_77, x_702, x_692, x_717, x_70, x_1, x_703, x_696, x_700, x_710, x_712, x_698, x_697, x_707, x_695);
if (lean_obj_tag(x_718) == 0)
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; 
x_719 = lean_ctor_get(x_718, 0);
lean_inc(x_719);
lean_dec_ref(x_718);
x_720 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__54));
lean_inc(x_695);
lean_inc_ref(x_707);
lean_inc(x_697);
lean_inc_ref(x_698);
lean_inc_ref(x_1);
lean_inc(x_70);
lean_inc(x_77);
x_721 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(x_77, x_719, x_694, x_720, x_70, x_1, x_703, x_696, x_700, x_710, x_712, x_698, x_697, x_707, x_695);
if (lean_obj_tag(x_721) == 0)
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; 
x_722 = lean_ctor_get(x_721, 0);
lean_inc(x_722);
lean_dec_ref(x_721);
x_723 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0));
x_724 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1));
x_725 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2));
x_726 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__56));
lean_inc(x_706);
x_727 = l_Lean_mkConst(x_726, x_706);
lean_inc_ref(x_704);
lean_inc_ref(x_1);
x_728 = l_Lean_mkAppB(x_727, x_1, x_704);
x_729 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__57));
x_730 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__59));
lean_inc(x_706);
x_731 = l_Lean_mkConst(x_730, x_706);
lean_inc_ref(x_728);
lean_inc_ref(x_1);
x_732 = l_Lean_mkAppB(x_731, x_1, x_728);
lean_inc(x_695);
lean_inc_ref(x_707);
lean_inc(x_697);
lean_inc_ref(x_698);
lean_inc(x_714);
lean_inc_ref(x_1);
lean_inc(x_70);
x_733 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(x_70, x_1, x_714, x_698, x_697, x_707, x_695);
if (lean_obj_tag(x_733) == 0)
{
lean_object* x_734; lean_object* x_735; lean_object* x_736; 
x_734 = lean_ctor_get(x_733, 0);
lean_inc(x_734);
lean_dec_ref(x_733);
x_735 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__61));
lean_inc(x_695);
lean_inc_ref(x_707);
lean_inc(x_697);
lean_inc_ref(x_698);
lean_inc_ref(x_1);
lean_inc(x_70);
x_736 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(x_735, x_70, x_1, x_698, x_697, x_707, x_695);
if (lean_obj_tag(x_736) == 0)
{
lean_object* x_737; lean_object* x_738; 
x_737 = lean_ctor_get(x_736, 0);
lean_inc(x_737);
lean_dec_ref(x_736);
lean_inc(x_695);
lean_inc_ref(x_707);
lean_inc(x_697);
lean_inc_ref(x_698);
lean_inc(x_712);
lean_inc_ref(x_710);
lean_inc(x_700);
lean_inc_ref(x_696);
lean_inc(x_703);
lean_inc(x_715);
lean_inc_ref(x_1);
lean_inc(x_70);
x_738 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(x_70, x_1, x_715, x_703, x_696, x_700, x_710, x_712, x_698, x_697, x_707, x_695);
if (lean_obj_tag(x_738) == 0)
{
lean_object* x_739; lean_object* x_740; 
x_739 = lean_ctor_get(x_738, 0);
lean_inc(x_739);
lean_dec_ref(x_738);
lean_inc(x_695);
lean_inc_ref(x_707);
lean_inc(x_697);
lean_inc_ref(x_698);
lean_inc(x_702);
lean_inc(x_80);
lean_inc(x_77);
lean_inc(x_734);
lean_inc_ref(x_1);
lean_inc(x_70);
x_740 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(x_70, x_1, x_734, x_77, x_80, x_702, x_703, x_696, x_700, x_710, x_712, x_698, x_697, x_707, x_695);
if (lean_obj_tag(x_740) == 0)
{
if (lean_obj_tag(x_734) == 1)
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; 
x_741 = lean_ctor_get(x_740, 0);
lean_inc(x_741);
lean_dec_ref(x_740);
x_742 = lean_ctor_get(x_734, 0);
lean_inc(x_742);
lean_dec_ref(x_734);
lean_inc(x_695);
lean_inc_ref(x_707);
lean_inc(x_697);
lean_inc_ref(x_698);
lean_inc(x_712);
lean_inc_ref(x_710);
lean_inc(x_700);
lean_inc_ref(x_696);
lean_inc(x_703);
lean_inc(x_715);
lean_inc_ref(x_1);
lean_inc(x_70);
x_743 = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(x_70, x_1, x_742, x_715, x_703, x_696, x_700, x_710, x_712, x_698, x_697, x_707, x_695);
if (lean_obj_tag(x_743) == 0)
{
lean_object* x_744; 
x_744 = lean_ctor_get(x_743, 0);
lean_inc(x_744);
lean_dec_ref(x_743);
x_254 = x_741;
x_255 = x_739;
x_256 = x_725;
x_257 = x_699;
x_258 = x_737;
x_259 = x_723;
x_260 = x_724;
x_261 = x_732;
x_262 = x_701;
x_263 = x_704;
x_264 = x_702;
x_265 = x_729;
x_266 = x_705;
x_267 = x_706;
x_268 = x_709;
x_269 = x_708;
x_270 = x_716;
x_271 = x_711;
x_272 = x_728;
x_273 = x_722;
x_274 = x_714;
x_275 = x_744;
x_276 = x_715;
x_277 = x_703;
x_278 = x_696;
x_279 = x_700;
x_280 = x_710;
x_281 = x_712;
x_282 = x_698;
x_283 = x_697;
x_284 = x_707;
x_285 = x_695;
x_286 = lean_box(0);
goto block_688;
}
else
{
uint8_t x_745; 
lean_dec(x_741);
lean_dec(x_739);
lean_dec(x_737);
lean_dec_ref(x_732);
lean_dec_ref(x_728);
lean_dec(x_722);
lean_dec(x_715);
lean_dec(x_714);
lean_dec(x_712);
lean_dec(x_711);
lean_dec_ref(x_710);
lean_dec_ref(x_709);
lean_dec(x_708);
lean_dec_ref(x_707);
lean_dec(x_706);
lean_dec_ref(x_705);
lean_dec_ref(x_704);
lean_dec(x_703);
lean_dec(x_702);
lean_dec(x_701);
lean_dec(x_700);
lean_dec(x_699);
lean_dec_ref(x_698);
lean_dec(x_697);
lean_dec_ref(x_696);
lean_dec(x_695);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_745 = !lean_is_exclusive(x_743);
if (x_745 == 0)
{
return x_743;
}
else
{
lean_object* x_746; lean_object* x_747; 
x_746 = lean_ctor_get(x_743, 0);
lean_inc(x_746);
lean_dec(x_743);
x_747 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_747, 0, x_746);
return x_747;
}
}
}
else
{
lean_object* x_748; lean_object* x_749; 
lean_dec(x_734);
x_748 = lean_ctor_get(x_740, 0);
lean_inc(x_748);
lean_dec_ref(x_740);
x_749 = lean_box(0);
x_254 = x_748;
x_255 = x_739;
x_256 = x_725;
x_257 = x_699;
x_258 = x_737;
x_259 = x_723;
x_260 = x_724;
x_261 = x_732;
x_262 = x_701;
x_263 = x_704;
x_264 = x_702;
x_265 = x_729;
x_266 = x_705;
x_267 = x_706;
x_268 = x_709;
x_269 = x_708;
x_270 = x_716;
x_271 = x_711;
x_272 = x_728;
x_273 = x_722;
x_274 = x_714;
x_275 = x_749;
x_276 = x_715;
x_277 = x_703;
x_278 = x_696;
x_279 = x_700;
x_280 = x_710;
x_281 = x_712;
x_282 = x_698;
x_283 = x_697;
x_284 = x_707;
x_285 = x_695;
x_286 = lean_box(0);
goto block_688;
}
}
else
{
uint8_t x_750; 
lean_dec(x_739);
lean_dec(x_737);
lean_dec(x_734);
lean_dec_ref(x_732);
lean_dec_ref(x_728);
lean_dec(x_722);
lean_dec(x_715);
lean_dec(x_714);
lean_dec(x_712);
lean_dec(x_711);
lean_dec_ref(x_710);
lean_dec_ref(x_709);
lean_dec(x_708);
lean_dec_ref(x_707);
lean_dec(x_706);
lean_dec_ref(x_705);
lean_dec_ref(x_704);
lean_dec(x_703);
lean_dec(x_702);
lean_dec(x_701);
lean_dec(x_700);
lean_dec(x_699);
lean_dec_ref(x_698);
lean_dec(x_697);
lean_dec_ref(x_696);
lean_dec(x_695);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_750 = !lean_is_exclusive(x_740);
if (x_750 == 0)
{
return x_740;
}
else
{
lean_object* x_751; lean_object* x_752; 
x_751 = lean_ctor_get(x_740, 0);
lean_inc(x_751);
lean_dec(x_740);
x_752 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_752, 0, x_751);
return x_752;
}
}
}
else
{
uint8_t x_753; 
lean_dec(x_737);
lean_dec(x_734);
lean_dec_ref(x_732);
lean_dec_ref(x_728);
lean_dec(x_722);
lean_dec(x_715);
lean_dec(x_714);
lean_dec(x_712);
lean_dec(x_711);
lean_dec_ref(x_710);
lean_dec_ref(x_709);
lean_dec(x_708);
lean_dec_ref(x_707);
lean_dec(x_706);
lean_dec_ref(x_705);
lean_dec_ref(x_704);
lean_dec(x_703);
lean_dec(x_702);
lean_dec(x_701);
lean_dec(x_700);
lean_dec(x_699);
lean_dec_ref(x_698);
lean_dec(x_697);
lean_dec_ref(x_696);
lean_dec(x_695);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_753 = !lean_is_exclusive(x_738);
if (x_753 == 0)
{
return x_738;
}
else
{
lean_object* x_754; lean_object* x_755; 
x_754 = lean_ctor_get(x_738, 0);
lean_inc(x_754);
lean_dec(x_738);
x_755 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_755, 0, x_754);
return x_755;
}
}
}
else
{
uint8_t x_756; 
lean_dec(x_734);
lean_dec_ref(x_732);
lean_dec_ref(x_728);
lean_dec(x_722);
lean_dec(x_715);
lean_dec(x_714);
lean_dec(x_712);
lean_dec(x_711);
lean_dec_ref(x_710);
lean_dec_ref(x_709);
lean_dec(x_708);
lean_dec_ref(x_707);
lean_dec(x_706);
lean_dec_ref(x_705);
lean_dec_ref(x_704);
lean_dec(x_703);
lean_dec(x_702);
lean_dec(x_701);
lean_dec(x_700);
lean_dec(x_699);
lean_dec_ref(x_698);
lean_dec(x_697);
lean_dec_ref(x_696);
lean_dec(x_695);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_756 = !lean_is_exclusive(x_736);
if (x_756 == 0)
{
return x_736;
}
else
{
lean_object* x_757; lean_object* x_758; 
x_757 = lean_ctor_get(x_736, 0);
lean_inc(x_757);
lean_dec(x_736);
x_758 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_758, 0, x_757);
return x_758;
}
}
}
else
{
uint8_t x_759; 
lean_dec_ref(x_732);
lean_dec_ref(x_728);
lean_dec(x_722);
lean_dec(x_715);
lean_dec(x_714);
lean_dec(x_712);
lean_dec(x_711);
lean_dec_ref(x_710);
lean_dec_ref(x_709);
lean_dec(x_708);
lean_dec_ref(x_707);
lean_dec(x_706);
lean_dec_ref(x_705);
lean_dec_ref(x_704);
lean_dec(x_703);
lean_dec(x_702);
lean_dec(x_701);
lean_dec(x_700);
lean_dec(x_699);
lean_dec_ref(x_698);
lean_dec(x_697);
lean_dec_ref(x_696);
lean_dec(x_695);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_759 = !lean_is_exclusive(x_733);
if (x_759 == 0)
{
return x_733;
}
else
{
lean_object* x_760; lean_object* x_761; 
x_760 = lean_ctor_get(x_733, 0);
lean_inc(x_760);
lean_dec(x_733);
x_761 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_761, 0, x_760);
return x_761;
}
}
}
else
{
uint8_t x_762; 
lean_dec(x_715);
lean_dec(x_714);
lean_dec(x_712);
lean_dec(x_711);
lean_dec_ref(x_710);
lean_dec_ref(x_709);
lean_dec(x_708);
lean_dec_ref(x_707);
lean_dec(x_706);
lean_dec_ref(x_705);
lean_dec_ref(x_704);
lean_dec(x_703);
lean_dec(x_702);
lean_dec(x_701);
lean_dec(x_700);
lean_dec(x_699);
lean_dec_ref(x_698);
lean_dec(x_697);
lean_dec_ref(x_696);
lean_dec(x_695);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_762 = !lean_is_exclusive(x_721);
if (x_762 == 0)
{
return x_721;
}
else
{
lean_object* x_763; lean_object* x_764; 
x_763 = lean_ctor_get(x_721, 0);
lean_inc(x_763);
lean_dec(x_721);
x_764 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_764, 0, x_763);
return x_764;
}
}
}
else
{
uint8_t x_765; 
lean_dec(x_715);
lean_dec(x_714);
lean_dec(x_712);
lean_dec(x_711);
lean_dec_ref(x_710);
lean_dec_ref(x_709);
lean_dec(x_708);
lean_dec_ref(x_707);
lean_dec(x_706);
lean_dec_ref(x_705);
lean_dec_ref(x_704);
lean_dec(x_703);
lean_dec(x_702);
lean_dec(x_701);
lean_dec(x_700);
lean_dec(x_699);
lean_dec_ref(x_698);
lean_dec(x_697);
lean_dec_ref(x_696);
lean_dec(x_695);
lean_dec(x_694);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_765 = !lean_is_exclusive(x_718);
if (x_765 == 0)
{
return x_718;
}
else
{
lean_object* x_766; lean_object* x_767; 
x_766 = lean_ctor_get(x_718, 0);
lean_inc(x_766);
lean_dec(x_718);
x_767 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_767, 0, x_766);
return x_767;
}
}
}
}
else
{
uint8_t x_979; 
lean_dec(x_692);
lean_dec(x_690);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_979 = !lean_is_exclusive(x_693);
if (x_979 == 0)
{
return x_693;
}
else
{
lean_object* x_980; lean_object* x_981; 
x_980 = lean_ctor_get(x_693, 0);
lean_inc(x_980);
lean_dec(x_693);
x_981 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_981, 0, x_980);
return x_981;
}
}
}
else
{
uint8_t x_982; 
lean_dec(x_690);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_982 = !lean_is_exclusive(x_691);
if (x_982 == 0)
{
return x_691;
}
else
{
lean_object* x_983; lean_object* x_984; 
x_983 = lean_ctor_get(x_691, 0);
lean_inc(x_983);
lean_dec(x_691);
x_984 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_984, 0, x_983);
return x_984;
}
}
}
else
{
uint8_t x_985; 
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_985 = !lean_is_exclusive(x_689);
if (x_985 == 0)
{
return x_689;
}
else
{
lean_object* x_986; lean_object* x_987; 
x_986 = lean_ctor_get(x_689, 0);
lean_inc(x_986);
lean_dec(x_689);
x_987 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_987, 0, x_986);
return x_987;
}
}
block_145:
{
lean_object* x_119; 
x_119 = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(x_108, x_116);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; size_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec_ref(x_119);
x_121 = lean_ctor_get(x_120, 0);
lean_inc_ref(x_121);
lean_dec(x_120);
x_122 = lean_array_get_size(x_121);
lean_dec_ref(x_121);
x_123 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__4;
x_124 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__5;
x_125 = 5;
lean_inc(x_84);
x_126 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_123);
lean_ctor_set(x_126, 2, x_84);
lean_ctor_set(x_126, 3, x_84);
lean_ctor_set_usize(x_126, 4, x_125);
x_127 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__7;
x_128 = lean_box(0);
x_129 = lean_box(0);
lean_inc_ref_n(x_126, 7);
lean_inc(x_88);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_85);
lean_inc(x_103);
x_130 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_130, 0, x_122);
lean_ctor_set(x_130, 1, x_73);
lean_ctor_set(x_130, 2, x_1);
lean_ctor_set(x_130, 3, x_70);
lean_ctor_set(x_130, 4, x_97);
lean_ctor_set(x_130, 5, x_77);
lean_ctor_set(x_130, 6, x_80);
lean_ctor_set(x_130, 7, x_82);
lean_ctor_set(x_130, 8, x_98);
lean_ctor_set(x_130, 9, x_96);
lean_ctor_set(x_130, 10, x_102);
lean_ctor_set(x_130, 11, x_101);
lean_ctor_set(x_130, 12, x_103);
lean_ctor_set(x_130, 13, x_90);
lean_ctor_set(x_130, 14, x_85);
lean_ctor_set(x_130, 15, x_91);
lean_ctor_set(x_130, 16, x_92);
lean_ctor_set(x_130, 17, x_106);
lean_ctor_set(x_130, 18, x_105);
lean_ctor_set(x_130, 19, x_88);
lean_ctor_set(x_130, 20, x_94);
lean_ctor_set(x_130, 21, x_93);
lean_ctor_set(x_130, 22, x_99);
lean_ctor_set(x_130, 23, x_83);
lean_ctor_set(x_130, 24, x_95);
lean_ctor_set(x_130, 25, x_89);
lean_ctor_set(x_130, 26, x_87);
lean_ctor_set(x_130, 27, x_107);
lean_ctor_set(x_130, 28, x_86);
lean_ctor_set(x_130, 29, x_104);
lean_ctor_set(x_130, 30, x_126);
lean_ctor_set(x_130, 31, x_127);
lean_ctor_set(x_130, 32, x_126);
lean_ctor_set(x_130, 33, x_126);
lean_ctor_set(x_130, 34, x_126);
lean_ctor_set(x_130, 35, x_126);
lean_ctor_set(x_130, 36, x_128);
lean_ctor_set(x_130, 37, x_127);
lean_ctor_set(x_130, 38, x_126);
lean_ctor_set(x_130, 39, x_129);
lean_ctor_set(x_130, 40, x_126);
lean_ctor_set(x_130, 41, x_126);
lean_ctor_set_uint8(x_130, sizeof(void*)*42, x_100);
x_131 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__1), 2, 1);
lean_closure_set(x_131, 0, x_130);
x_132 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_133 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_132, x_131, x_108);
if (lean_obj_tag(x_133) == 0)
{
lean_dec_ref(x_133);
if (lean_obj_tag(x_88) == 1)
{
if (lean_obj_tag(x_103) == 0)
{
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec(x_111);
lean_dec_ref(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_92);
lean_dec(x_91);
lean_dec_ref(x_88);
lean_dec(x_85);
x_13 = x_122;
x_14 = lean_box(0);
goto block_17;
}
else
{
lean_dec_ref(x_103);
if (lean_obj_tag(x_85) == 0)
{
if (x_100 == 0)
{
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_88, 0);
lean_inc(x_134);
lean_dec_ref(x_88);
x_135 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(x_92);
lean_dec(x_92);
if (x_135 == 0)
{
lean_dec(x_134);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec(x_111);
lean_dec_ref(x_110);
lean_dec(x_109);
lean_dec(x_108);
x_13 = x_122;
x_14 = lean_box(0);
goto block_17;
}
else
{
x_46 = x_108;
x_47 = x_114;
x_48 = x_122;
x_49 = x_111;
x_50 = x_110;
x_51 = x_116;
x_52 = x_113;
x_53 = x_100;
x_54 = x_134;
x_55 = x_117;
x_56 = x_109;
x_57 = lean_box(0);
x_58 = x_112;
x_59 = x_115;
goto block_66;
}
}
else
{
lean_object* x_136; 
lean_dec(x_92);
lean_dec_ref(x_91);
x_136 = lean_ctor_get(x_88, 0);
lean_inc(x_136);
lean_dec_ref(x_88);
x_46 = x_108;
x_47 = x_114;
x_48 = x_122;
x_49 = x_111;
x_50 = x_110;
x_51 = x_116;
x_52 = x_113;
x_53 = x_100;
x_54 = x_136;
x_55 = x_117;
x_56 = x_109;
x_57 = lean_box(0);
x_58 = x_112;
x_59 = x_115;
goto block_66;
}
}
else
{
lean_object* x_137; 
lean_dec(x_92);
lean_dec(x_91);
x_137 = lean_ctor_get(x_88, 0);
lean_inc(x_137);
lean_dec_ref(x_88);
x_24 = x_108;
x_25 = x_114;
x_26 = x_122;
x_27 = x_111;
x_28 = x_110;
x_29 = x_116;
x_30 = x_113;
x_31 = x_100;
x_32 = x_137;
x_33 = x_117;
x_34 = x_109;
x_35 = lean_box(0);
x_36 = x_115;
x_37 = x_112;
goto block_45;
}
}
else
{
lean_object* x_138; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec_ref(x_85);
x_138 = lean_ctor_get(x_88, 0);
lean_inc(x_138);
lean_dec_ref(x_88);
x_24 = x_108;
x_25 = x_114;
x_26 = x_122;
x_27 = x_111;
x_28 = x_110;
x_29 = x_116;
x_30 = x_113;
x_31 = x_100;
x_32 = x_138;
x_33 = x_117;
x_34 = x_109;
x_35 = lean_box(0);
x_36 = x_115;
x_37 = x_112;
goto block_45;
}
}
}
else
{
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec(x_111);
lean_dec_ref(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_103);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_88);
lean_dec(x_85);
x_13 = x_122;
x_14 = lean_box(0);
goto block_17;
}
}
else
{
uint8_t x_139; 
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec(x_111);
lean_dec_ref(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_103);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_88);
lean_dec(x_85);
x_139 = !lean_is_exclusive(x_133);
if (x_139 == 0)
{
return x_133;
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_133, 0);
lean_inc(x_140);
lean_dec(x_133);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_140);
return x_141;
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec(x_111);
lean_dec_ref(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec_ref(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec_ref(x_99);
lean_dec(x_98);
lean_dec_ref(x_97);
lean_dec(x_96);
lean_dec_ref(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_73);
lean_dec(x_70);
lean_dec_ref(x_1);
x_142 = !lean_is_exclusive(x_119);
if (x_142 == 0)
{
return x_119;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_119, 0);
lean_inc(x_143);
lean_dec(x_119);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_143);
return x_144;
}
}
}
block_207:
{
lean_object* x_181; 
lean_inc(x_179);
lean_inc_ref(x_178);
lean_inc(x_177);
lean_inc_ref(x_176);
lean_inc(x_175);
lean_inc_ref(x_174);
lean_inc(x_173);
lean_inc_ref(x_172);
lean_inc(x_171);
lean_inc(x_170);
lean_inc_ref(x_1);
lean_inc(x_70);
x_181 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f(x_70, x_1, x_170, x_171, x_172, x_173, x_174, x_175, x_176, x_177, x_178, x_179);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
lean_dec_ref(x_181);
lean_inc(x_179);
lean_inc_ref(x_178);
lean_inc(x_177);
lean_inc_ref(x_176);
lean_inc(x_175);
lean_inc_ref(x_174);
lean_inc(x_173);
lean_inc_ref(x_172);
lean_inc(x_171);
lean_inc(x_170);
lean_inc_ref(x_1);
lean_inc(x_70);
x_183 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f(x_70, x_1, x_170, x_171, x_172, x_173, x_174, x_175, x_176, x_177, x_178, x_179);
if (lean_obj_tag(x_183) == 0)
{
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_184; 
lean_dec(x_161);
lean_dec(x_71);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
lean_dec_ref(x_183);
x_83 = x_147;
x_84 = x_148;
x_85 = x_149;
x_86 = x_150;
x_87 = x_184;
x_88 = x_151;
x_89 = x_182;
x_90 = x_152;
x_91 = x_153;
x_92 = x_154;
x_93 = x_169;
x_94 = x_155;
x_95 = x_156;
x_96 = x_157;
x_97 = x_158;
x_98 = x_159;
x_99 = x_160;
x_100 = x_163;
x_101 = x_162;
x_102 = x_164;
x_103 = x_165;
x_104 = x_167;
x_105 = x_166;
x_106 = x_168;
x_107 = x_146;
x_108 = x_170;
x_109 = x_171;
x_110 = x_172;
x_111 = x_173;
x_112 = x_174;
x_113 = x_175;
x_114 = x_176;
x_115 = x_177;
x_116 = x_178;
x_117 = x_179;
x_118 = lean_box(0);
goto block_145;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_146);
x_185 = lean_ctor_get(x_183, 0);
lean_inc(x_185);
lean_dec_ref(x_183);
x_186 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__9));
lean_inc(x_179);
lean_inc_ref(x_178);
lean_inc(x_177);
lean_inc_ref(x_176);
lean_inc_ref(x_1);
lean_inc(x_70);
x_187 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(x_186, x_70, x_1, x_170, x_171, x_172, x_173, x_174, x_175, x_176, x_177, x_178, x_179);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
lean_dec_ref(x_187);
x_189 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__11));
x_190 = l_Lean_mkConst(x_189, x_161);
lean_inc_ref_n(x_1, 3);
x_191 = l_Lean_mkApp4(x_190, x_1, x_1, x_1, x_188);
lean_inc(x_179);
lean_inc_ref(x_178);
lean_inc(x_177);
lean_inc_ref(x_176);
lean_inc(x_175);
lean_inc_ref(x_174);
lean_inc(x_173);
lean_inc_ref(x_172);
lean_inc(x_171);
lean_inc(x_170);
x_192 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_191, x_170, x_171, x_172, x_173, x_174, x_175, x_176, x_177, x_178, x_179);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
lean_dec_ref(x_192);
if (lean_is_scalar(x_71)) {
 x_194 = lean_alloc_ctor(1, 1, 0);
} else {
 x_194 = x_71;
}
lean_ctor_set(x_194, 0, x_193);
x_83 = x_147;
x_84 = x_148;
x_85 = x_149;
x_86 = x_150;
x_87 = x_185;
x_88 = x_151;
x_89 = x_182;
x_90 = x_152;
x_91 = x_153;
x_92 = x_154;
x_93 = x_169;
x_94 = x_155;
x_95 = x_156;
x_96 = x_157;
x_97 = x_158;
x_98 = x_159;
x_99 = x_160;
x_100 = x_163;
x_101 = x_162;
x_102 = x_164;
x_103 = x_165;
x_104 = x_167;
x_105 = x_166;
x_106 = x_168;
x_107 = x_194;
x_108 = x_170;
x_109 = x_171;
x_110 = x_172;
x_111 = x_173;
x_112 = x_174;
x_113 = x_175;
x_114 = x_176;
x_115 = x_177;
x_116 = x_178;
x_117 = x_179;
x_118 = lean_box(0);
goto block_145;
}
else
{
uint8_t x_195; 
lean_dec(x_185);
lean_dec(x_182);
lean_dec(x_179);
lean_dec_ref(x_178);
lean_dec(x_177);
lean_dec_ref(x_176);
lean_dec(x_175);
lean_dec_ref(x_174);
lean_dec(x_173);
lean_dec_ref(x_172);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec_ref(x_168);
lean_dec_ref(x_167);
lean_dec_ref(x_166);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_162);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec_ref(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec_ref(x_152);
lean_dec(x_151);
lean_dec_ref(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec_ref(x_147);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_195 = !lean_is_exclusive(x_192);
if (x_195 == 0)
{
return x_192;
}
else
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_192, 0);
lean_inc(x_196);
lean_dec(x_192);
x_197 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_197, 0, x_196);
return x_197;
}
}
}
else
{
uint8_t x_198; 
lean_dec(x_185);
lean_dec(x_182);
lean_dec(x_179);
lean_dec_ref(x_178);
lean_dec(x_177);
lean_dec_ref(x_176);
lean_dec(x_175);
lean_dec_ref(x_174);
lean_dec(x_173);
lean_dec_ref(x_172);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec_ref(x_168);
lean_dec_ref(x_167);
lean_dec_ref(x_166);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_162);
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec_ref(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec_ref(x_152);
lean_dec(x_151);
lean_dec_ref(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec_ref(x_147);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_198 = !lean_is_exclusive(x_187);
if (x_198 == 0)
{
return x_187;
}
else
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_187, 0);
lean_inc(x_199);
lean_dec(x_187);
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_199);
return x_200;
}
}
}
}
else
{
uint8_t x_201; 
lean_dec(x_182);
lean_dec(x_179);
lean_dec_ref(x_178);
lean_dec(x_177);
lean_dec_ref(x_176);
lean_dec(x_175);
lean_dec_ref(x_174);
lean_dec(x_173);
lean_dec_ref(x_172);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec_ref(x_168);
lean_dec_ref(x_167);
lean_dec_ref(x_166);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_162);
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec_ref(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec_ref(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec_ref(x_147);
lean_dec(x_146);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_201 = !lean_is_exclusive(x_183);
if (x_201 == 0)
{
return x_183;
}
else
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_183, 0);
lean_inc(x_202);
lean_dec(x_183);
x_203 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_203, 0, x_202);
return x_203;
}
}
}
else
{
uint8_t x_204; 
lean_dec(x_179);
lean_dec_ref(x_178);
lean_dec(x_177);
lean_dec_ref(x_176);
lean_dec(x_175);
lean_dec_ref(x_174);
lean_dec(x_173);
lean_dec_ref(x_172);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec_ref(x_168);
lean_dec_ref(x_167);
lean_dec_ref(x_166);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_162);
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec_ref(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec_ref(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec_ref(x_147);
lean_dec(x_146);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_204 = !lean_is_exclusive(x_181);
if (x_204 == 0)
{
return x_181;
}
else
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_181, 0);
lean_inc(x_205);
lean_dec(x_181);
x_206 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_206, 0, x_205);
return x_206;
}
}
}
block_253:
{
if (lean_obj_tag(x_80) == 1)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_243 = lean_ctor_get(x_80, 0);
x_244 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__13));
x_245 = l_Lean_mkConst(x_244, x_221);
lean_inc(x_243);
lean_inc_ref(x_1);
x_246 = l_Lean_mkAppB(x_245, x_1, x_243);
lean_inc(x_241);
lean_inc_ref(x_240);
lean_inc(x_239);
lean_inc_ref(x_238);
lean_inc(x_237);
lean_inc_ref(x_236);
lean_inc(x_235);
lean_inc_ref(x_234);
lean_inc(x_233);
lean_inc(x_232);
x_247 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_246, x_232, x_233, x_234, x_235, x_236, x_237, x_238, x_239, x_240, x_241);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
lean_dec_ref(x_247);
if (lean_is_scalar(x_74)) {
 x_249 = lean_alloc_ctor(1, 1, 0);
} else {
 x_249 = x_74;
 lean_ctor_set_tag(x_249, 1);
}
lean_ctor_set(x_249, 0, x_248);
x_146 = x_208;
x_147 = x_209;
x_148 = x_210;
x_149 = x_211;
x_150 = x_212;
x_151 = x_213;
x_152 = x_214;
x_153 = x_215;
x_154 = x_216;
x_155 = x_231;
x_156 = x_217;
x_157 = x_218;
x_158 = x_219;
x_159 = x_220;
x_160 = x_222;
x_161 = x_223;
x_162 = x_225;
x_163 = x_224;
x_164 = x_226;
x_165 = x_227;
x_166 = x_229;
x_167 = x_228;
x_168 = x_230;
x_169 = x_249;
x_170 = x_232;
x_171 = x_233;
x_172 = x_234;
x_173 = x_235;
x_174 = x_236;
x_175 = x_237;
x_176 = x_238;
x_177 = x_239;
x_178 = x_240;
x_179 = x_241;
x_180 = lean_box(0);
goto block_207;
}
else
{
uint8_t x_250; 
lean_dec(x_241);
lean_dec_ref(x_240);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec(x_235);
lean_dec_ref(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec_ref(x_230);
lean_dec_ref(x_229);
lean_dec_ref(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec(x_218);
lean_dec_ref(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec_ref(x_212);
lean_dec(x_211);
lean_dec(x_210);
lean_dec_ref(x_209);
lean_dec(x_208);
lean_dec(x_82);
lean_dec_ref(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_250 = !lean_is_exclusive(x_247);
if (x_250 == 0)
{
return x_247;
}
else
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_247, 0);
lean_inc(x_251);
lean_dec(x_247);
x_252 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_252, 0, x_251);
return x_252;
}
}
}
else
{
lean_dec(x_221);
lean_dec(x_74);
lean_inc(x_208);
x_146 = x_208;
x_147 = x_209;
x_148 = x_210;
x_149 = x_211;
x_150 = x_212;
x_151 = x_213;
x_152 = x_214;
x_153 = x_215;
x_154 = x_216;
x_155 = x_231;
x_156 = x_217;
x_157 = x_218;
x_158 = x_219;
x_159 = x_220;
x_160 = x_222;
x_161 = x_223;
x_162 = x_225;
x_163 = x_224;
x_164 = x_226;
x_165 = x_227;
x_166 = x_229;
x_167 = x_228;
x_168 = x_230;
x_169 = x_208;
x_170 = x_232;
x_171 = x_233;
x_172 = x_234;
x_173 = x_235;
x_174 = x_236;
x_175 = x_237;
x_176 = x_238;
x_177 = x_239;
x_178 = x_240;
x_179 = x_241;
x_180 = lean_box(0);
goto block_207;
}
}
block_688:
{
lean_object* x_287; 
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
x_287 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(x_70, x_1, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
lean_dec_ref(x_287);
x_289 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__15));
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
x_290 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(x_289, x_70, x_1, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
lean_dec_ref(x_290);
x_292 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__17));
lean_inc(x_267);
x_293 = l_Lean_mkConst(x_292, x_267);
lean_inc(x_291);
lean_inc_ref(x_1);
x_294 = l_Lean_mkAppB(x_293, x_1, x_291);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc(x_281);
lean_inc_ref(x_280);
lean_inc(x_279);
lean_inc_ref(x_278);
lean_inc(x_277);
lean_inc(x_276);
x_295 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(x_294, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
lean_dec_ref(x_295);
x_297 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__19));
lean_inc(x_267);
x_298 = l_Lean_mkConst(x_297, x_267);
x_299 = lean_unsigned_to_nat(0u);
x_300 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__20;
lean_inc_ref(x_1);
x_301 = l_Lean_mkAppB(x_298, x_1, x_300);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
x_302 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_301, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_302) == 0)
{
uint8_t x_303; 
x_303 = !lean_is_exclusive(x_302);
if (x_303 == 0)
{
lean_object* x_304; 
x_304 = lean_ctor_get(x_302, 0);
if (lean_obj_tag(x_304) == 1)
{
uint8_t x_305; 
lean_free_object(x_302);
x_305 = !lean_is_exclusive(x_304);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_306 = lean_ctor_get(x_304, 0);
x_307 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__22));
lean_inc(x_267);
x_308 = l_Lean_mkConst(x_307, x_267);
lean_inc_ref(x_1);
x_309 = l_Lean_mkApp3(x_308, x_1, x_300, x_306);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc(x_281);
lean_inc_ref(x_280);
lean_inc(x_279);
lean_inc_ref(x_278);
lean_inc(x_277);
lean_inc(x_276);
x_310 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_309, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; lean_object* x_312; 
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
lean_dec_ref(x_310);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc(x_311);
lean_inc(x_296);
x_312 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(x_296, x_311, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; lean_object* x_314; 
lean_dec_ref(x_312);
x_313 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__24));
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
x_314 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(x_313, x_70, x_1, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
lean_dec_ref(x_314);
x_316 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__26));
lean_inc(x_269);
x_317 = l_Lean_mkConst(x_316, x_269);
lean_inc(x_315);
lean_inc_ref_n(x_1, 3);
x_318 = l_Lean_mkApp4(x_317, x_1, x_1, x_1, x_315);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc(x_281);
lean_inc_ref(x_280);
lean_inc(x_279);
lean_inc_ref(x_278);
lean_inc(x_277);
lean_inc(x_276);
x_319 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_318, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
lean_dec_ref(x_319);
x_321 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__28));
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
x_322 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(x_321, x_70, x_1, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
lean_dec_ref(x_322);
x_324 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__30));
lean_inc(x_267);
x_325 = l_Lean_mkConst(x_324, x_267);
lean_inc(x_323);
lean_inc_ref(x_1);
x_326 = l_Lean_mkAppB(x_325, x_1, x_323);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc(x_281);
lean_inc_ref(x_280);
lean_inc(x_279);
lean_inc_ref(x_278);
lean_inc(x_277);
lean_inc(x_276);
x_327 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_326, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; lean_object* x_329; 
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
lean_dec_ref(x_327);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
x_329 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(x_70, x_1, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
lean_dec_ref(x_329);
x_331 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__1));
x_332 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2;
x_333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_271);
x_334 = l_Lean_mkConst(x_331, x_333);
x_335 = l_Lean_Int_mkType;
lean_inc(x_330);
lean_inc_ref_n(x_1, 2);
lean_inc_ref(x_334);
x_336 = l_Lean_mkApp4(x_334, x_335, x_1, x_1, x_330);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc(x_281);
lean_inc_ref(x_280);
lean_inc(x_279);
lean_inc_ref(x_278);
lean_inc(x_277);
lean_inc(x_276);
x_337 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_336, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; 
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
lean_dec_ref(x_337);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
x_339 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(x_70, x_1, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
lean_dec_ref(x_339);
x_341 = l_Lean_Nat_mkType;
lean_inc(x_340);
lean_inc_ref_n(x_1, 2);
x_342 = l_Lean_mkApp4(x_334, x_341, x_1, x_1, x_340);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc(x_281);
lean_inc_ref(x_280);
lean_inc(x_279);
lean_inc_ref(x_278);
lean_inc(x_277);
lean_inc(x_276);
x_343 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_342, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
lean_dec_ref(x_343);
x_345 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__31));
x_346 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__32));
lean_inc_ref(x_260);
lean_inc_ref(x_259);
x_347 = l_Lean_Name_mkStr4(x_259, x_260, x_345, x_346);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
lean_inc_ref(x_261);
x_348 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(x_291, x_261, x_347, x_70, x_1, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec_ref(x_348);
x_349 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__33));
lean_inc_ref(x_260);
lean_inc_ref(x_259);
x_350 = l_Lean_Name_mkStr4(x_259, x_260, x_345, x_349);
x_351 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__35));
x_352 = lean_box(0);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
x_353 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(x_268, x_261, x_350, x_351, x_70, x_1, x_352, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_dec_ref(x_353);
x_354 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__36));
lean_inc_ref(x_265);
lean_inc_ref(x_260);
lean_inc_ref(x_259);
x_355 = l_Lean_Name_mkStr4(x_259, x_260, x_265, x_354);
x_356 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__38));
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
lean_inc_ref(x_272);
x_357 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(x_315, x_272, x_355, x_356, x_70, x_1, x_352, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec_ref(x_357);
x_358 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__39));
lean_inc_ref(x_260);
lean_inc_ref(x_259);
x_359 = l_Lean_Name_mkStr4(x_259, x_260, x_265, x_358);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
x_360 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(x_323, x_272, x_359, x_70, x_1, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_dec_ref(x_360);
x_361 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__40));
lean_inc_ref(x_256);
lean_inc_ref(x_260);
lean_inc_ref(x_259);
x_362 = l_Lean_Name_mkStr4(x_259, x_260, x_256, x_361);
x_363 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__42));
x_364 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__43;
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
lean_inc_ref(x_263);
x_365 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(x_330, x_263, x_362, x_363, x_70, x_1, x_364, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec_ref(x_365);
x_366 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__44));
x_367 = l_Lean_Name_mkStr4(x_259, x_260, x_256, x_366);
x_368 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__45;
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
lean_inc_ref(x_263);
x_369 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(x_340, x_263, x_367, x_363, x_70, x_1, x_368, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_369) == 0)
{
lean_dec_ref(x_369);
if (lean_obj_tag(x_77) == 1)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_370 = lean_ctor_get(x_77, 0);
x_371 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__47));
lean_inc(x_267);
x_372 = l_Lean_mkConst(x_371, x_267);
lean_inc(x_370);
lean_inc_ref(x_1);
x_373 = l_Lean_mkAppB(x_372, x_1, x_370);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc(x_281);
lean_inc_ref(x_280);
lean_inc(x_279);
lean_inc_ref(x_278);
lean_inc(x_277);
lean_inc(x_276);
x_374 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_373, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; 
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
lean_dec_ref(x_374);
lean_ctor_set(x_304, 0, x_375);
x_208 = x_352;
x_209 = x_338;
x_210 = x_299;
x_211 = x_254;
x_212 = x_320;
x_213 = x_255;
x_214 = x_257;
x_215 = x_258;
x_216 = x_275;
x_217 = x_344;
x_218 = x_262;
x_219 = x_263;
x_220 = x_264;
x_221 = x_267;
x_222 = x_266;
x_223 = x_269;
x_224 = x_270;
x_225 = x_288;
x_226 = x_273;
x_227 = x_274;
x_228 = x_328;
x_229 = x_311;
x_230 = x_296;
x_231 = x_304;
x_232 = x_276;
x_233 = x_277;
x_234 = x_278;
x_235 = x_279;
x_236 = x_280;
x_237 = x_281;
x_238 = x_282;
x_239 = x_283;
x_240 = x_284;
x_241 = x_285;
x_242 = lean_box(0);
goto block_253;
}
else
{
uint8_t x_376; 
lean_dec(x_344);
lean_dec(x_338);
lean_dec(x_328);
lean_dec(x_320);
lean_dec(x_311);
lean_free_object(x_304);
lean_dec(x_296);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_269);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec_ref(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_376 = !lean_is_exclusive(x_374);
if (x_376 == 0)
{
return x_374;
}
else
{
lean_object* x_377; lean_object* x_378; 
x_377 = lean_ctor_get(x_374, 0);
lean_inc(x_377);
lean_dec(x_374);
x_378 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_378, 0, x_377);
return x_378;
}
}
}
else
{
lean_free_object(x_304);
x_208 = x_352;
x_209 = x_338;
x_210 = x_299;
x_211 = x_254;
x_212 = x_320;
x_213 = x_255;
x_214 = x_257;
x_215 = x_258;
x_216 = x_275;
x_217 = x_344;
x_218 = x_262;
x_219 = x_263;
x_220 = x_264;
x_221 = x_267;
x_222 = x_266;
x_223 = x_269;
x_224 = x_270;
x_225 = x_288;
x_226 = x_273;
x_227 = x_274;
x_228 = x_328;
x_229 = x_311;
x_230 = x_296;
x_231 = x_352;
x_232 = x_276;
x_233 = x_277;
x_234 = x_278;
x_235 = x_279;
x_236 = x_280;
x_237 = x_281;
x_238 = x_282;
x_239 = x_283;
x_240 = x_284;
x_241 = x_285;
x_242 = lean_box(0);
goto block_253;
}
}
else
{
uint8_t x_379; 
lean_dec(x_344);
lean_dec(x_338);
lean_dec(x_328);
lean_dec(x_320);
lean_dec(x_311);
lean_free_object(x_304);
lean_dec(x_296);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_269);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_379 = !lean_is_exclusive(x_369);
if (x_379 == 0)
{
return x_369;
}
else
{
lean_object* x_380; lean_object* x_381; 
x_380 = lean_ctor_get(x_369, 0);
lean_inc(x_380);
lean_dec(x_369);
x_381 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_381, 0, x_380);
return x_381;
}
}
}
else
{
uint8_t x_382; 
lean_dec(x_344);
lean_dec(x_340);
lean_dec(x_338);
lean_dec(x_328);
lean_dec(x_320);
lean_dec(x_311);
lean_free_object(x_304);
lean_dec(x_296);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_269);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_382 = !lean_is_exclusive(x_365);
if (x_382 == 0)
{
return x_365;
}
else
{
lean_object* x_383; lean_object* x_384; 
x_383 = lean_ctor_get(x_365, 0);
lean_inc(x_383);
lean_dec(x_365);
x_384 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_384, 0, x_383);
return x_384;
}
}
}
else
{
uint8_t x_385; 
lean_dec(x_344);
lean_dec(x_340);
lean_dec(x_338);
lean_dec(x_330);
lean_dec(x_328);
lean_dec(x_320);
lean_dec(x_311);
lean_free_object(x_304);
lean_dec(x_296);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_269);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_385 = !lean_is_exclusive(x_360);
if (x_385 == 0)
{
return x_360;
}
else
{
lean_object* x_386; lean_object* x_387; 
x_386 = lean_ctor_get(x_360, 0);
lean_inc(x_386);
lean_dec(x_360);
x_387 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_387, 0, x_386);
return x_387;
}
}
}
else
{
uint8_t x_388; 
lean_dec(x_344);
lean_dec(x_340);
lean_dec(x_338);
lean_dec(x_330);
lean_dec(x_328);
lean_dec(x_323);
lean_dec(x_320);
lean_dec(x_311);
lean_free_object(x_304);
lean_dec(x_296);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_269);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_388 = !lean_is_exclusive(x_357);
if (x_388 == 0)
{
return x_357;
}
else
{
lean_object* x_389; lean_object* x_390; 
x_389 = lean_ctor_get(x_357, 0);
lean_inc(x_389);
lean_dec(x_357);
x_390 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_390, 0, x_389);
return x_390;
}
}
}
else
{
uint8_t x_391; 
lean_dec(x_344);
lean_dec(x_340);
lean_dec(x_338);
lean_dec(x_330);
lean_dec(x_328);
lean_dec(x_323);
lean_dec(x_320);
lean_dec(x_315);
lean_dec(x_311);
lean_free_object(x_304);
lean_dec(x_296);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_269);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_391 = !lean_is_exclusive(x_353);
if (x_391 == 0)
{
return x_353;
}
else
{
lean_object* x_392; lean_object* x_393; 
x_392 = lean_ctor_get(x_353, 0);
lean_inc(x_392);
lean_dec(x_353);
x_393 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_393, 0, x_392);
return x_393;
}
}
}
else
{
uint8_t x_394; 
lean_dec(x_344);
lean_dec(x_340);
lean_dec(x_338);
lean_dec(x_330);
lean_dec(x_328);
lean_dec(x_323);
lean_dec(x_320);
lean_dec(x_315);
lean_dec(x_311);
lean_free_object(x_304);
lean_dec(x_296);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_394 = !lean_is_exclusive(x_348);
if (x_394 == 0)
{
return x_348;
}
else
{
lean_object* x_395; lean_object* x_396; 
x_395 = lean_ctor_get(x_348, 0);
lean_inc(x_395);
lean_dec(x_348);
x_396 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_396, 0, x_395);
return x_396;
}
}
}
else
{
uint8_t x_397; 
lean_dec(x_340);
lean_dec(x_338);
lean_dec(x_330);
lean_dec(x_328);
lean_dec(x_323);
lean_dec(x_320);
lean_dec(x_315);
lean_dec(x_311);
lean_free_object(x_304);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_397 = !lean_is_exclusive(x_343);
if (x_397 == 0)
{
return x_343;
}
else
{
lean_object* x_398; lean_object* x_399; 
x_398 = lean_ctor_get(x_343, 0);
lean_inc(x_398);
lean_dec(x_343);
x_399 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_399, 0, x_398);
return x_399;
}
}
}
else
{
uint8_t x_400; 
lean_dec(x_338);
lean_dec_ref(x_334);
lean_dec(x_330);
lean_dec(x_328);
lean_dec(x_323);
lean_dec(x_320);
lean_dec(x_315);
lean_dec(x_311);
lean_free_object(x_304);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_400 = !lean_is_exclusive(x_339);
if (x_400 == 0)
{
return x_339;
}
else
{
lean_object* x_401; lean_object* x_402; 
x_401 = lean_ctor_get(x_339, 0);
lean_inc(x_401);
lean_dec(x_339);
x_402 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_402, 0, x_401);
return x_402;
}
}
}
else
{
uint8_t x_403; 
lean_dec_ref(x_334);
lean_dec(x_330);
lean_dec(x_328);
lean_dec(x_323);
lean_dec(x_320);
lean_dec(x_315);
lean_dec(x_311);
lean_free_object(x_304);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_403 = !lean_is_exclusive(x_337);
if (x_403 == 0)
{
return x_337;
}
else
{
lean_object* x_404; lean_object* x_405; 
x_404 = lean_ctor_get(x_337, 0);
lean_inc(x_404);
lean_dec(x_337);
x_405 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_405, 0, x_404);
return x_405;
}
}
}
else
{
uint8_t x_406; 
lean_dec(x_328);
lean_dec(x_323);
lean_dec(x_320);
lean_dec(x_315);
lean_dec(x_311);
lean_free_object(x_304);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_406 = !lean_is_exclusive(x_329);
if (x_406 == 0)
{
return x_329;
}
else
{
lean_object* x_407; lean_object* x_408; 
x_407 = lean_ctor_get(x_329, 0);
lean_inc(x_407);
lean_dec(x_329);
x_408 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_408, 0, x_407);
return x_408;
}
}
}
else
{
uint8_t x_409; 
lean_dec(x_323);
lean_dec(x_320);
lean_dec(x_315);
lean_dec(x_311);
lean_free_object(x_304);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_409 = !lean_is_exclusive(x_327);
if (x_409 == 0)
{
return x_327;
}
else
{
lean_object* x_410; lean_object* x_411; 
x_410 = lean_ctor_get(x_327, 0);
lean_inc(x_410);
lean_dec(x_327);
x_411 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_411, 0, x_410);
return x_411;
}
}
}
else
{
uint8_t x_412; 
lean_dec(x_320);
lean_dec(x_315);
lean_dec(x_311);
lean_free_object(x_304);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_412 = !lean_is_exclusive(x_322);
if (x_412 == 0)
{
return x_322;
}
else
{
lean_object* x_413; lean_object* x_414; 
x_413 = lean_ctor_get(x_322, 0);
lean_inc(x_413);
lean_dec(x_322);
x_414 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_414, 0, x_413);
return x_414;
}
}
}
else
{
uint8_t x_415; 
lean_dec(x_315);
lean_dec(x_311);
lean_free_object(x_304);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_415 = !lean_is_exclusive(x_319);
if (x_415 == 0)
{
return x_319;
}
else
{
lean_object* x_416; lean_object* x_417; 
x_416 = lean_ctor_get(x_319, 0);
lean_inc(x_416);
lean_dec(x_319);
x_417 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_417, 0, x_416);
return x_417;
}
}
}
else
{
uint8_t x_418; 
lean_dec(x_311);
lean_free_object(x_304);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_418 = !lean_is_exclusive(x_314);
if (x_418 == 0)
{
return x_314;
}
else
{
lean_object* x_419; lean_object* x_420; 
x_419 = lean_ctor_get(x_314, 0);
lean_inc(x_419);
lean_dec(x_314);
x_420 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_420, 0, x_419);
return x_420;
}
}
}
else
{
uint8_t x_421; 
lean_dec(x_311);
lean_free_object(x_304);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_421 = !lean_is_exclusive(x_312);
if (x_421 == 0)
{
return x_312;
}
else
{
lean_object* x_422; lean_object* x_423; 
x_422 = lean_ctor_get(x_312, 0);
lean_inc(x_422);
lean_dec(x_312);
x_423 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_423, 0, x_422);
return x_423;
}
}
}
else
{
uint8_t x_424; 
lean_free_object(x_304);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_424 = !lean_is_exclusive(x_310);
if (x_424 == 0)
{
return x_310;
}
else
{
lean_object* x_425; lean_object* x_426; 
x_425 = lean_ctor_get(x_310, 0);
lean_inc(x_425);
lean_dec(x_310);
x_426 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_426, 0, x_425);
return x_426;
}
}
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_427 = lean_ctor_get(x_304, 0);
lean_inc(x_427);
lean_dec(x_304);
x_428 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__22));
lean_inc(x_267);
x_429 = l_Lean_mkConst(x_428, x_267);
lean_inc_ref(x_1);
x_430 = l_Lean_mkApp3(x_429, x_1, x_300, x_427);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc(x_281);
lean_inc_ref(x_280);
lean_inc(x_279);
lean_inc_ref(x_278);
lean_inc(x_277);
lean_inc(x_276);
x_431 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_430, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
lean_dec_ref(x_431);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc(x_432);
lean_inc(x_296);
x_433 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(x_296, x_432, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_433) == 0)
{
lean_object* x_434; lean_object* x_435; 
lean_dec_ref(x_433);
x_434 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__24));
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
x_435 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(x_434, x_70, x_1, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
lean_dec_ref(x_435);
x_437 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__26));
lean_inc(x_269);
x_438 = l_Lean_mkConst(x_437, x_269);
lean_inc(x_436);
lean_inc_ref_n(x_1, 3);
x_439 = l_Lean_mkApp4(x_438, x_1, x_1, x_1, x_436);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc(x_281);
lean_inc_ref(x_280);
lean_inc(x_279);
lean_inc_ref(x_278);
lean_inc(x_277);
lean_inc(x_276);
x_440 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_439, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
lean_dec_ref(x_440);
x_442 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__28));
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
x_443 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(x_442, x_70, x_1, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_443) == 0)
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
lean_dec_ref(x_443);
x_445 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__30));
lean_inc(x_267);
x_446 = l_Lean_mkConst(x_445, x_267);
lean_inc(x_444);
lean_inc_ref(x_1);
x_447 = l_Lean_mkAppB(x_446, x_1, x_444);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc(x_281);
lean_inc_ref(x_280);
lean_inc(x_279);
lean_inc_ref(x_278);
lean_inc(x_277);
lean_inc(x_276);
x_448 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_447, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; 
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
lean_dec_ref(x_448);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
x_450 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(x_70, x_1, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
lean_dec_ref(x_450);
x_452 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__1));
x_453 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2;
x_454 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_454, 0, x_453);
lean_ctor_set(x_454, 1, x_271);
x_455 = l_Lean_mkConst(x_452, x_454);
x_456 = l_Lean_Int_mkType;
lean_inc(x_451);
lean_inc_ref_n(x_1, 2);
lean_inc_ref(x_455);
x_457 = l_Lean_mkApp4(x_455, x_456, x_1, x_1, x_451);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc(x_281);
lean_inc_ref(x_280);
lean_inc(x_279);
lean_inc_ref(x_278);
lean_inc(x_277);
lean_inc(x_276);
x_458 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_457, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; lean_object* x_460; 
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
lean_dec_ref(x_458);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
x_460 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(x_70, x_1, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
lean_dec_ref(x_460);
x_462 = l_Lean_Nat_mkType;
lean_inc(x_461);
lean_inc_ref_n(x_1, 2);
x_463 = l_Lean_mkApp4(x_455, x_462, x_1, x_1, x_461);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc(x_281);
lean_inc_ref(x_280);
lean_inc(x_279);
lean_inc_ref(x_278);
lean_inc(x_277);
lean_inc(x_276);
x_464 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_463, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_465 = lean_ctor_get(x_464, 0);
lean_inc(x_465);
lean_dec_ref(x_464);
x_466 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__31));
x_467 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__32));
lean_inc_ref(x_260);
lean_inc_ref(x_259);
x_468 = l_Lean_Name_mkStr4(x_259, x_260, x_466, x_467);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
lean_inc_ref(x_261);
x_469 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(x_291, x_261, x_468, x_70, x_1, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
lean_dec_ref(x_469);
x_470 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__33));
lean_inc_ref(x_260);
lean_inc_ref(x_259);
x_471 = l_Lean_Name_mkStr4(x_259, x_260, x_466, x_470);
x_472 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__35));
x_473 = lean_box(0);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
x_474 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(x_268, x_261, x_471, x_472, x_70, x_1, x_473, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_474) == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
lean_dec_ref(x_474);
x_475 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__36));
lean_inc_ref(x_265);
lean_inc_ref(x_260);
lean_inc_ref(x_259);
x_476 = l_Lean_Name_mkStr4(x_259, x_260, x_265, x_475);
x_477 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__38));
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
lean_inc_ref(x_272);
x_478 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(x_436, x_272, x_476, x_477, x_70, x_1, x_473, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_478) == 0)
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; 
lean_dec_ref(x_478);
x_479 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__39));
lean_inc_ref(x_260);
lean_inc_ref(x_259);
x_480 = l_Lean_Name_mkStr4(x_259, x_260, x_265, x_479);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
x_481 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(x_444, x_272, x_480, x_70, x_1, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_481) == 0)
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
lean_dec_ref(x_481);
x_482 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__40));
lean_inc_ref(x_256);
lean_inc_ref(x_260);
lean_inc_ref(x_259);
x_483 = l_Lean_Name_mkStr4(x_259, x_260, x_256, x_482);
x_484 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__42));
x_485 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__43;
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
lean_inc_ref(x_263);
x_486 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(x_451, x_263, x_483, x_484, x_70, x_1, x_485, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
lean_dec_ref(x_486);
x_487 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__44));
x_488 = l_Lean_Name_mkStr4(x_259, x_260, x_256, x_487);
x_489 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__45;
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
lean_inc_ref(x_263);
x_490 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(x_461, x_263, x_488, x_484, x_70, x_1, x_489, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_490) == 0)
{
lean_dec_ref(x_490);
if (lean_obj_tag(x_77) == 1)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_491 = lean_ctor_get(x_77, 0);
x_492 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__47));
lean_inc(x_267);
x_493 = l_Lean_mkConst(x_492, x_267);
lean_inc(x_491);
lean_inc_ref(x_1);
x_494 = l_Lean_mkAppB(x_493, x_1, x_491);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc(x_281);
lean_inc_ref(x_280);
lean_inc(x_279);
lean_inc_ref(x_278);
lean_inc(x_277);
lean_inc(x_276);
x_495 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_494, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_495) == 0)
{
lean_object* x_496; lean_object* x_497; 
x_496 = lean_ctor_get(x_495, 0);
lean_inc(x_496);
lean_dec_ref(x_495);
x_497 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_497, 0, x_496);
x_208 = x_473;
x_209 = x_459;
x_210 = x_299;
x_211 = x_254;
x_212 = x_441;
x_213 = x_255;
x_214 = x_257;
x_215 = x_258;
x_216 = x_275;
x_217 = x_465;
x_218 = x_262;
x_219 = x_263;
x_220 = x_264;
x_221 = x_267;
x_222 = x_266;
x_223 = x_269;
x_224 = x_270;
x_225 = x_288;
x_226 = x_273;
x_227 = x_274;
x_228 = x_449;
x_229 = x_432;
x_230 = x_296;
x_231 = x_497;
x_232 = x_276;
x_233 = x_277;
x_234 = x_278;
x_235 = x_279;
x_236 = x_280;
x_237 = x_281;
x_238 = x_282;
x_239 = x_283;
x_240 = x_284;
x_241 = x_285;
x_242 = lean_box(0);
goto block_253;
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_dec(x_465);
lean_dec(x_459);
lean_dec(x_449);
lean_dec(x_441);
lean_dec(x_432);
lean_dec(x_296);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_269);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec_ref(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_498 = lean_ctor_get(x_495, 0);
lean_inc(x_498);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 x_499 = x_495;
} else {
 lean_dec_ref(x_495);
 x_499 = lean_box(0);
}
if (lean_is_scalar(x_499)) {
 x_500 = lean_alloc_ctor(1, 1, 0);
} else {
 x_500 = x_499;
}
lean_ctor_set(x_500, 0, x_498);
return x_500;
}
}
else
{
x_208 = x_473;
x_209 = x_459;
x_210 = x_299;
x_211 = x_254;
x_212 = x_441;
x_213 = x_255;
x_214 = x_257;
x_215 = x_258;
x_216 = x_275;
x_217 = x_465;
x_218 = x_262;
x_219 = x_263;
x_220 = x_264;
x_221 = x_267;
x_222 = x_266;
x_223 = x_269;
x_224 = x_270;
x_225 = x_288;
x_226 = x_273;
x_227 = x_274;
x_228 = x_449;
x_229 = x_432;
x_230 = x_296;
x_231 = x_473;
x_232 = x_276;
x_233 = x_277;
x_234 = x_278;
x_235 = x_279;
x_236 = x_280;
x_237 = x_281;
x_238 = x_282;
x_239 = x_283;
x_240 = x_284;
x_241 = x_285;
x_242 = lean_box(0);
goto block_253;
}
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; 
lean_dec(x_465);
lean_dec(x_459);
lean_dec(x_449);
lean_dec(x_441);
lean_dec(x_432);
lean_dec(x_296);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_269);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_501 = lean_ctor_get(x_490, 0);
lean_inc(x_501);
if (lean_is_exclusive(x_490)) {
 lean_ctor_release(x_490, 0);
 x_502 = x_490;
} else {
 lean_dec_ref(x_490);
 x_502 = lean_box(0);
}
if (lean_is_scalar(x_502)) {
 x_503 = lean_alloc_ctor(1, 1, 0);
} else {
 x_503 = x_502;
}
lean_ctor_set(x_503, 0, x_501);
return x_503;
}
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; 
lean_dec(x_465);
lean_dec(x_461);
lean_dec(x_459);
lean_dec(x_449);
lean_dec(x_441);
lean_dec(x_432);
lean_dec(x_296);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_269);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_504 = lean_ctor_get(x_486, 0);
lean_inc(x_504);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 x_505 = x_486;
} else {
 lean_dec_ref(x_486);
 x_505 = lean_box(0);
}
if (lean_is_scalar(x_505)) {
 x_506 = lean_alloc_ctor(1, 1, 0);
} else {
 x_506 = x_505;
}
lean_ctor_set(x_506, 0, x_504);
return x_506;
}
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; 
lean_dec(x_465);
lean_dec(x_461);
lean_dec(x_459);
lean_dec(x_451);
lean_dec(x_449);
lean_dec(x_441);
lean_dec(x_432);
lean_dec(x_296);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_269);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_507 = lean_ctor_get(x_481, 0);
lean_inc(x_507);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 x_508 = x_481;
} else {
 lean_dec_ref(x_481);
 x_508 = lean_box(0);
}
if (lean_is_scalar(x_508)) {
 x_509 = lean_alloc_ctor(1, 1, 0);
} else {
 x_509 = x_508;
}
lean_ctor_set(x_509, 0, x_507);
return x_509;
}
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; 
lean_dec(x_465);
lean_dec(x_461);
lean_dec(x_459);
lean_dec(x_451);
lean_dec(x_449);
lean_dec(x_444);
lean_dec(x_441);
lean_dec(x_432);
lean_dec(x_296);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_269);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_510 = lean_ctor_get(x_478, 0);
lean_inc(x_510);
if (lean_is_exclusive(x_478)) {
 lean_ctor_release(x_478, 0);
 x_511 = x_478;
} else {
 lean_dec_ref(x_478);
 x_511 = lean_box(0);
}
if (lean_is_scalar(x_511)) {
 x_512 = lean_alloc_ctor(1, 1, 0);
} else {
 x_512 = x_511;
}
lean_ctor_set(x_512, 0, x_510);
return x_512;
}
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; 
lean_dec(x_465);
lean_dec(x_461);
lean_dec(x_459);
lean_dec(x_451);
lean_dec(x_449);
lean_dec(x_444);
lean_dec(x_441);
lean_dec(x_436);
lean_dec(x_432);
lean_dec(x_296);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_269);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_513 = lean_ctor_get(x_474, 0);
lean_inc(x_513);
if (lean_is_exclusive(x_474)) {
 lean_ctor_release(x_474, 0);
 x_514 = x_474;
} else {
 lean_dec_ref(x_474);
 x_514 = lean_box(0);
}
if (lean_is_scalar(x_514)) {
 x_515 = lean_alloc_ctor(1, 1, 0);
} else {
 x_515 = x_514;
}
lean_ctor_set(x_515, 0, x_513);
return x_515;
}
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; 
lean_dec(x_465);
lean_dec(x_461);
lean_dec(x_459);
lean_dec(x_451);
lean_dec(x_449);
lean_dec(x_444);
lean_dec(x_441);
lean_dec(x_436);
lean_dec(x_432);
lean_dec(x_296);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_516 = lean_ctor_get(x_469, 0);
lean_inc(x_516);
if (lean_is_exclusive(x_469)) {
 lean_ctor_release(x_469, 0);
 x_517 = x_469;
} else {
 lean_dec_ref(x_469);
 x_517 = lean_box(0);
}
if (lean_is_scalar(x_517)) {
 x_518 = lean_alloc_ctor(1, 1, 0);
} else {
 x_518 = x_517;
}
lean_ctor_set(x_518, 0, x_516);
return x_518;
}
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; 
lean_dec(x_461);
lean_dec(x_459);
lean_dec(x_451);
lean_dec(x_449);
lean_dec(x_444);
lean_dec(x_441);
lean_dec(x_436);
lean_dec(x_432);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_519 = lean_ctor_get(x_464, 0);
lean_inc(x_519);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 x_520 = x_464;
} else {
 lean_dec_ref(x_464);
 x_520 = lean_box(0);
}
if (lean_is_scalar(x_520)) {
 x_521 = lean_alloc_ctor(1, 1, 0);
} else {
 x_521 = x_520;
}
lean_ctor_set(x_521, 0, x_519);
return x_521;
}
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; 
lean_dec(x_459);
lean_dec_ref(x_455);
lean_dec(x_451);
lean_dec(x_449);
lean_dec(x_444);
lean_dec(x_441);
lean_dec(x_436);
lean_dec(x_432);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_522 = lean_ctor_get(x_460, 0);
lean_inc(x_522);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 x_523 = x_460;
} else {
 lean_dec_ref(x_460);
 x_523 = lean_box(0);
}
if (lean_is_scalar(x_523)) {
 x_524 = lean_alloc_ctor(1, 1, 0);
} else {
 x_524 = x_523;
}
lean_ctor_set(x_524, 0, x_522);
return x_524;
}
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; 
lean_dec_ref(x_455);
lean_dec(x_451);
lean_dec(x_449);
lean_dec(x_444);
lean_dec(x_441);
lean_dec(x_436);
lean_dec(x_432);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_525 = lean_ctor_get(x_458, 0);
lean_inc(x_525);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 x_526 = x_458;
} else {
 lean_dec_ref(x_458);
 x_526 = lean_box(0);
}
if (lean_is_scalar(x_526)) {
 x_527 = lean_alloc_ctor(1, 1, 0);
} else {
 x_527 = x_526;
}
lean_ctor_set(x_527, 0, x_525);
return x_527;
}
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_dec(x_449);
lean_dec(x_444);
lean_dec(x_441);
lean_dec(x_436);
lean_dec(x_432);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_528 = lean_ctor_get(x_450, 0);
lean_inc(x_528);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 x_529 = x_450;
} else {
 lean_dec_ref(x_450);
 x_529 = lean_box(0);
}
if (lean_is_scalar(x_529)) {
 x_530 = lean_alloc_ctor(1, 1, 0);
} else {
 x_530 = x_529;
}
lean_ctor_set(x_530, 0, x_528);
return x_530;
}
}
else
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; 
lean_dec(x_444);
lean_dec(x_441);
lean_dec(x_436);
lean_dec(x_432);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_531 = lean_ctor_get(x_448, 0);
lean_inc(x_531);
if (lean_is_exclusive(x_448)) {
 lean_ctor_release(x_448, 0);
 x_532 = x_448;
} else {
 lean_dec_ref(x_448);
 x_532 = lean_box(0);
}
if (lean_is_scalar(x_532)) {
 x_533 = lean_alloc_ctor(1, 1, 0);
} else {
 x_533 = x_532;
}
lean_ctor_set(x_533, 0, x_531);
return x_533;
}
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; 
lean_dec(x_441);
lean_dec(x_436);
lean_dec(x_432);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_534 = lean_ctor_get(x_443, 0);
lean_inc(x_534);
if (lean_is_exclusive(x_443)) {
 lean_ctor_release(x_443, 0);
 x_535 = x_443;
} else {
 lean_dec_ref(x_443);
 x_535 = lean_box(0);
}
if (lean_is_scalar(x_535)) {
 x_536 = lean_alloc_ctor(1, 1, 0);
} else {
 x_536 = x_535;
}
lean_ctor_set(x_536, 0, x_534);
return x_536;
}
}
else
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; 
lean_dec(x_436);
lean_dec(x_432);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_537 = lean_ctor_get(x_440, 0);
lean_inc(x_537);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 x_538 = x_440;
} else {
 lean_dec_ref(x_440);
 x_538 = lean_box(0);
}
if (lean_is_scalar(x_538)) {
 x_539 = lean_alloc_ctor(1, 1, 0);
} else {
 x_539 = x_538;
}
lean_ctor_set(x_539, 0, x_537);
return x_539;
}
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; 
lean_dec(x_432);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_540 = lean_ctor_get(x_435, 0);
lean_inc(x_540);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 x_541 = x_435;
} else {
 lean_dec_ref(x_435);
 x_541 = lean_box(0);
}
if (lean_is_scalar(x_541)) {
 x_542 = lean_alloc_ctor(1, 1, 0);
} else {
 x_542 = x_541;
}
lean_ctor_set(x_542, 0, x_540);
return x_542;
}
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; 
lean_dec(x_432);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_543 = lean_ctor_get(x_433, 0);
lean_inc(x_543);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 x_544 = x_433;
} else {
 lean_dec_ref(x_433);
 x_544 = lean_box(0);
}
if (lean_is_scalar(x_544)) {
 x_545 = lean_alloc_ctor(1, 1, 0);
} else {
 x_545 = x_544;
}
lean_ctor_set(x_545, 0, x_543);
return x_545;
}
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; 
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_546 = lean_ctor_get(x_431, 0);
lean_inc(x_546);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 x_547 = x_431;
} else {
 lean_dec_ref(x_431);
 x_547 = lean_box(0);
}
if (lean_is_scalar(x_547)) {
 x_548 = lean_alloc_ctor(1, 1, 0);
} else {
 x_548 = x_547;
}
lean_ctor_set(x_548, 0, x_546);
return x_548;
}
}
}
else
{
lean_object* x_549; 
lean_dec(x_304);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_549 = lean_box(0);
lean_ctor_set(x_302, 0, x_549);
return x_302;
}
}
else
{
lean_object* x_550; 
x_550 = lean_ctor_get(x_302, 0);
lean_inc(x_550);
lean_dec(x_302);
if (lean_obj_tag(x_550) == 1)
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; 
x_551 = lean_ctor_get(x_550, 0);
lean_inc(x_551);
if (lean_is_exclusive(x_550)) {
 lean_ctor_release(x_550, 0);
 x_552 = x_550;
} else {
 lean_dec_ref(x_550);
 x_552 = lean_box(0);
}
x_553 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__22));
lean_inc(x_267);
x_554 = l_Lean_mkConst(x_553, x_267);
lean_inc_ref(x_1);
x_555 = l_Lean_mkApp3(x_554, x_1, x_300, x_551);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc(x_281);
lean_inc_ref(x_280);
lean_inc(x_279);
lean_inc_ref(x_278);
lean_inc(x_277);
lean_inc(x_276);
x_556 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_555, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_556) == 0)
{
lean_object* x_557; lean_object* x_558; 
x_557 = lean_ctor_get(x_556, 0);
lean_inc(x_557);
lean_dec_ref(x_556);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc(x_557);
lean_inc(x_296);
x_558 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(x_296, x_557, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_558) == 0)
{
lean_object* x_559; lean_object* x_560; 
lean_dec_ref(x_558);
x_559 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__24));
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
x_560 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(x_559, x_70, x_1, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_560) == 0)
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
x_561 = lean_ctor_get(x_560, 0);
lean_inc(x_561);
lean_dec_ref(x_560);
x_562 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__26));
lean_inc(x_269);
x_563 = l_Lean_mkConst(x_562, x_269);
lean_inc(x_561);
lean_inc_ref_n(x_1, 3);
x_564 = l_Lean_mkApp4(x_563, x_1, x_1, x_1, x_561);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc(x_281);
lean_inc_ref(x_280);
lean_inc(x_279);
lean_inc_ref(x_278);
lean_inc(x_277);
lean_inc(x_276);
x_565 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_564, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_565) == 0)
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; 
x_566 = lean_ctor_get(x_565, 0);
lean_inc(x_566);
lean_dec_ref(x_565);
x_567 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__28));
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
x_568 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(x_567, x_70, x_1, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_568) == 0)
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; 
x_569 = lean_ctor_get(x_568, 0);
lean_inc(x_569);
lean_dec_ref(x_568);
x_570 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__30));
lean_inc(x_267);
x_571 = l_Lean_mkConst(x_570, x_267);
lean_inc(x_569);
lean_inc_ref(x_1);
x_572 = l_Lean_mkAppB(x_571, x_1, x_569);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc(x_281);
lean_inc_ref(x_280);
lean_inc(x_279);
lean_inc_ref(x_278);
lean_inc(x_277);
lean_inc(x_276);
x_573 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_572, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_573) == 0)
{
lean_object* x_574; lean_object* x_575; 
x_574 = lean_ctor_get(x_573, 0);
lean_inc(x_574);
lean_dec_ref(x_573);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
x_575 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(x_70, x_1, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_575) == 0)
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_576 = lean_ctor_get(x_575, 0);
lean_inc(x_576);
lean_dec_ref(x_575);
x_577 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__1));
x_578 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2;
x_579 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_579, 0, x_578);
lean_ctor_set(x_579, 1, x_271);
x_580 = l_Lean_mkConst(x_577, x_579);
x_581 = l_Lean_Int_mkType;
lean_inc(x_576);
lean_inc_ref_n(x_1, 2);
lean_inc_ref(x_580);
x_582 = l_Lean_mkApp4(x_580, x_581, x_1, x_1, x_576);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc(x_281);
lean_inc_ref(x_280);
lean_inc(x_279);
lean_inc_ref(x_278);
lean_inc(x_277);
lean_inc(x_276);
x_583 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_582, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_583) == 0)
{
lean_object* x_584; lean_object* x_585; 
x_584 = lean_ctor_get(x_583, 0);
lean_inc(x_584);
lean_dec_ref(x_583);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
x_585 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(x_70, x_1, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_585) == 0)
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_586 = lean_ctor_get(x_585, 0);
lean_inc(x_586);
lean_dec_ref(x_585);
x_587 = l_Lean_Nat_mkType;
lean_inc(x_586);
lean_inc_ref_n(x_1, 2);
x_588 = l_Lean_mkApp4(x_580, x_587, x_1, x_1, x_586);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc(x_281);
lean_inc_ref(x_280);
lean_inc(x_279);
lean_inc_ref(x_278);
lean_inc(x_277);
lean_inc(x_276);
x_589 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_588, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_589) == 0)
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
x_590 = lean_ctor_get(x_589, 0);
lean_inc(x_590);
lean_dec_ref(x_589);
x_591 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__31));
x_592 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__32));
lean_inc_ref(x_260);
lean_inc_ref(x_259);
x_593 = l_Lean_Name_mkStr4(x_259, x_260, x_591, x_592);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
lean_inc_ref(x_261);
x_594 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(x_291, x_261, x_593, x_70, x_1, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_594) == 0)
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
lean_dec_ref(x_594);
x_595 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__33));
lean_inc_ref(x_260);
lean_inc_ref(x_259);
x_596 = l_Lean_Name_mkStr4(x_259, x_260, x_591, x_595);
x_597 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__35));
x_598 = lean_box(0);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
x_599 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(x_268, x_261, x_596, x_597, x_70, x_1, x_598, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_599) == 0)
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
lean_dec_ref(x_599);
x_600 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__36));
lean_inc_ref(x_265);
lean_inc_ref(x_260);
lean_inc_ref(x_259);
x_601 = l_Lean_Name_mkStr4(x_259, x_260, x_265, x_600);
x_602 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__38));
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
lean_inc_ref(x_272);
x_603 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(x_561, x_272, x_601, x_602, x_70, x_1, x_598, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_603) == 0)
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; 
lean_dec_ref(x_603);
x_604 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__39));
lean_inc_ref(x_260);
lean_inc_ref(x_259);
x_605 = l_Lean_Name_mkStr4(x_259, x_260, x_265, x_604);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
x_606 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(x_569, x_272, x_605, x_70, x_1, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_606) == 0)
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
lean_dec_ref(x_606);
x_607 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__40));
lean_inc_ref(x_256);
lean_inc_ref(x_260);
lean_inc_ref(x_259);
x_608 = l_Lean_Name_mkStr4(x_259, x_260, x_256, x_607);
x_609 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__42));
x_610 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__43;
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
lean_inc_ref(x_263);
x_611 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(x_576, x_263, x_608, x_609, x_70, x_1, x_610, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_611) == 0)
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; 
lean_dec_ref(x_611);
x_612 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__44));
x_613 = l_Lean_Name_mkStr4(x_259, x_260, x_256, x_612);
x_614 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__45;
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc_ref(x_1);
lean_inc(x_70);
lean_inc_ref(x_263);
x_615 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(x_586, x_263, x_613, x_609, x_70, x_1, x_614, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_615) == 0)
{
lean_dec_ref(x_615);
if (lean_obj_tag(x_77) == 1)
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_616 = lean_ctor_get(x_77, 0);
x_617 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__47));
lean_inc(x_267);
x_618 = l_Lean_mkConst(x_617, x_267);
lean_inc(x_616);
lean_inc_ref(x_1);
x_619 = l_Lean_mkAppB(x_618, x_1, x_616);
lean_inc(x_285);
lean_inc_ref(x_284);
lean_inc(x_283);
lean_inc_ref(x_282);
lean_inc(x_281);
lean_inc_ref(x_280);
lean_inc(x_279);
lean_inc_ref(x_278);
lean_inc(x_277);
lean_inc(x_276);
x_620 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_619, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_285);
if (lean_obj_tag(x_620) == 0)
{
lean_object* x_621; lean_object* x_622; 
x_621 = lean_ctor_get(x_620, 0);
lean_inc(x_621);
lean_dec_ref(x_620);
if (lean_is_scalar(x_552)) {
 x_622 = lean_alloc_ctor(1, 1, 0);
} else {
 x_622 = x_552;
}
lean_ctor_set(x_622, 0, x_621);
x_208 = x_598;
x_209 = x_584;
x_210 = x_299;
x_211 = x_254;
x_212 = x_566;
x_213 = x_255;
x_214 = x_257;
x_215 = x_258;
x_216 = x_275;
x_217 = x_590;
x_218 = x_262;
x_219 = x_263;
x_220 = x_264;
x_221 = x_267;
x_222 = x_266;
x_223 = x_269;
x_224 = x_270;
x_225 = x_288;
x_226 = x_273;
x_227 = x_274;
x_228 = x_574;
x_229 = x_557;
x_230 = x_296;
x_231 = x_622;
x_232 = x_276;
x_233 = x_277;
x_234 = x_278;
x_235 = x_279;
x_236 = x_280;
x_237 = x_281;
x_238 = x_282;
x_239 = x_283;
x_240 = x_284;
x_241 = x_285;
x_242 = lean_box(0);
goto block_253;
}
else
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; 
lean_dec(x_590);
lean_dec(x_584);
lean_dec(x_574);
lean_dec(x_566);
lean_dec(x_557);
lean_dec(x_552);
lean_dec(x_296);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_269);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec_ref(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_623 = lean_ctor_get(x_620, 0);
lean_inc(x_623);
if (lean_is_exclusive(x_620)) {
 lean_ctor_release(x_620, 0);
 x_624 = x_620;
} else {
 lean_dec_ref(x_620);
 x_624 = lean_box(0);
}
if (lean_is_scalar(x_624)) {
 x_625 = lean_alloc_ctor(1, 1, 0);
} else {
 x_625 = x_624;
}
lean_ctor_set(x_625, 0, x_623);
return x_625;
}
}
else
{
lean_dec(x_552);
x_208 = x_598;
x_209 = x_584;
x_210 = x_299;
x_211 = x_254;
x_212 = x_566;
x_213 = x_255;
x_214 = x_257;
x_215 = x_258;
x_216 = x_275;
x_217 = x_590;
x_218 = x_262;
x_219 = x_263;
x_220 = x_264;
x_221 = x_267;
x_222 = x_266;
x_223 = x_269;
x_224 = x_270;
x_225 = x_288;
x_226 = x_273;
x_227 = x_274;
x_228 = x_574;
x_229 = x_557;
x_230 = x_296;
x_231 = x_598;
x_232 = x_276;
x_233 = x_277;
x_234 = x_278;
x_235 = x_279;
x_236 = x_280;
x_237 = x_281;
x_238 = x_282;
x_239 = x_283;
x_240 = x_284;
x_241 = x_285;
x_242 = lean_box(0);
goto block_253;
}
}
else
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; 
lean_dec(x_590);
lean_dec(x_584);
lean_dec(x_574);
lean_dec(x_566);
lean_dec(x_557);
lean_dec(x_552);
lean_dec(x_296);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_269);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_626 = lean_ctor_get(x_615, 0);
lean_inc(x_626);
if (lean_is_exclusive(x_615)) {
 lean_ctor_release(x_615, 0);
 x_627 = x_615;
} else {
 lean_dec_ref(x_615);
 x_627 = lean_box(0);
}
if (lean_is_scalar(x_627)) {
 x_628 = lean_alloc_ctor(1, 1, 0);
} else {
 x_628 = x_627;
}
lean_ctor_set(x_628, 0, x_626);
return x_628;
}
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; 
lean_dec(x_590);
lean_dec(x_586);
lean_dec(x_584);
lean_dec(x_574);
lean_dec(x_566);
lean_dec(x_557);
lean_dec(x_552);
lean_dec(x_296);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_269);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_629 = lean_ctor_get(x_611, 0);
lean_inc(x_629);
if (lean_is_exclusive(x_611)) {
 lean_ctor_release(x_611, 0);
 x_630 = x_611;
} else {
 lean_dec_ref(x_611);
 x_630 = lean_box(0);
}
if (lean_is_scalar(x_630)) {
 x_631 = lean_alloc_ctor(1, 1, 0);
} else {
 x_631 = x_630;
}
lean_ctor_set(x_631, 0, x_629);
return x_631;
}
}
else
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; 
lean_dec(x_590);
lean_dec(x_586);
lean_dec(x_584);
lean_dec(x_576);
lean_dec(x_574);
lean_dec(x_566);
lean_dec(x_557);
lean_dec(x_552);
lean_dec(x_296);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_269);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_632 = lean_ctor_get(x_606, 0);
lean_inc(x_632);
if (lean_is_exclusive(x_606)) {
 lean_ctor_release(x_606, 0);
 x_633 = x_606;
} else {
 lean_dec_ref(x_606);
 x_633 = lean_box(0);
}
if (lean_is_scalar(x_633)) {
 x_634 = lean_alloc_ctor(1, 1, 0);
} else {
 x_634 = x_633;
}
lean_ctor_set(x_634, 0, x_632);
return x_634;
}
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; 
lean_dec(x_590);
lean_dec(x_586);
lean_dec(x_584);
lean_dec(x_576);
lean_dec(x_574);
lean_dec(x_569);
lean_dec(x_566);
lean_dec(x_557);
lean_dec(x_552);
lean_dec(x_296);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_269);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_635 = lean_ctor_get(x_603, 0);
lean_inc(x_635);
if (lean_is_exclusive(x_603)) {
 lean_ctor_release(x_603, 0);
 x_636 = x_603;
} else {
 lean_dec_ref(x_603);
 x_636 = lean_box(0);
}
if (lean_is_scalar(x_636)) {
 x_637 = lean_alloc_ctor(1, 1, 0);
} else {
 x_637 = x_636;
}
lean_ctor_set(x_637, 0, x_635);
return x_637;
}
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; 
lean_dec(x_590);
lean_dec(x_586);
lean_dec(x_584);
lean_dec(x_576);
lean_dec(x_574);
lean_dec(x_569);
lean_dec(x_566);
lean_dec(x_561);
lean_dec(x_557);
lean_dec(x_552);
lean_dec(x_296);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_269);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_638 = lean_ctor_get(x_599, 0);
lean_inc(x_638);
if (lean_is_exclusive(x_599)) {
 lean_ctor_release(x_599, 0);
 x_639 = x_599;
} else {
 lean_dec_ref(x_599);
 x_639 = lean_box(0);
}
if (lean_is_scalar(x_639)) {
 x_640 = lean_alloc_ctor(1, 1, 0);
} else {
 x_640 = x_639;
}
lean_ctor_set(x_640, 0, x_638);
return x_640;
}
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; 
lean_dec(x_590);
lean_dec(x_586);
lean_dec(x_584);
lean_dec(x_576);
lean_dec(x_574);
lean_dec(x_569);
lean_dec(x_566);
lean_dec(x_561);
lean_dec(x_557);
lean_dec(x_552);
lean_dec(x_296);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_641 = lean_ctor_get(x_594, 0);
lean_inc(x_641);
if (lean_is_exclusive(x_594)) {
 lean_ctor_release(x_594, 0);
 x_642 = x_594;
} else {
 lean_dec_ref(x_594);
 x_642 = lean_box(0);
}
if (lean_is_scalar(x_642)) {
 x_643 = lean_alloc_ctor(1, 1, 0);
} else {
 x_643 = x_642;
}
lean_ctor_set(x_643, 0, x_641);
return x_643;
}
}
else
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; 
lean_dec(x_586);
lean_dec(x_584);
lean_dec(x_576);
lean_dec(x_574);
lean_dec(x_569);
lean_dec(x_566);
lean_dec(x_561);
lean_dec(x_557);
lean_dec(x_552);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_644 = lean_ctor_get(x_589, 0);
lean_inc(x_644);
if (lean_is_exclusive(x_589)) {
 lean_ctor_release(x_589, 0);
 x_645 = x_589;
} else {
 lean_dec_ref(x_589);
 x_645 = lean_box(0);
}
if (lean_is_scalar(x_645)) {
 x_646 = lean_alloc_ctor(1, 1, 0);
} else {
 x_646 = x_645;
}
lean_ctor_set(x_646, 0, x_644);
return x_646;
}
}
else
{
lean_object* x_647; lean_object* x_648; lean_object* x_649; 
lean_dec(x_584);
lean_dec_ref(x_580);
lean_dec(x_576);
lean_dec(x_574);
lean_dec(x_569);
lean_dec(x_566);
lean_dec(x_561);
lean_dec(x_557);
lean_dec(x_552);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_647 = lean_ctor_get(x_585, 0);
lean_inc(x_647);
if (lean_is_exclusive(x_585)) {
 lean_ctor_release(x_585, 0);
 x_648 = x_585;
} else {
 lean_dec_ref(x_585);
 x_648 = lean_box(0);
}
if (lean_is_scalar(x_648)) {
 x_649 = lean_alloc_ctor(1, 1, 0);
} else {
 x_649 = x_648;
}
lean_ctor_set(x_649, 0, x_647);
return x_649;
}
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; 
lean_dec_ref(x_580);
lean_dec(x_576);
lean_dec(x_574);
lean_dec(x_569);
lean_dec(x_566);
lean_dec(x_561);
lean_dec(x_557);
lean_dec(x_552);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_650 = lean_ctor_get(x_583, 0);
lean_inc(x_650);
if (lean_is_exclusive(x_583)) {
 lean_ctor_release(x_583, 0);
 x_651 = x_583;
} else {
 lean_dec_ref(x_583);
 x_651 = lean_box(0);
}
if (lean_is_scalar(x_651)) {
 x_652 = lean_alloc_ctor(1, 1, 0);
} else {
 x_652 = x_651;
}
lean_ctor_set(x_652, 0, x_650);
return x_652;
}
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; 
lean_dec(x_574);
lean_dec(x_569);
lean_dec(x_566);
lean_dec(x_561);
lean_dec(x_557);
lean_dec(x_552);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_653 = lean_ctor_get(x_575, 0);
lean_inc(x_653);
if (lean_is_exclusive(x_575)) {
 lean_ctor_release(x_575, 0);
 x_654 = x_575;
} else {
 lean_dec_ref(x_575);
 x_654 = lean_box(0);
}
if (lean_is_scalar(x_654)) {
 x_655 = lean_alloc_ctor(1, 1, 0);
} else {
 x_655 = x_654;
}
lean_ctor_set(x_655, 0, x_653);
return x_655;
}
}
else
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; 
lean_dec(x_569);
lean_dec(x_566);
lean_dec(x_561);
lean_dec(x_557);
lean_dec(x_552);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_656 = lean_ctor_get(x_573, 0);
lean_inc(x_656);
if (lean_is_exclusive(x_573)) {
 lean_ctor_release(x_573, 0);
 x_657 = x_573;
} else {
 lean_dec_ref(x_573);
 x_657 = lean_box(0);
}
if (lean_is_scalar(x_657)) {
 x_658 = lean_alloc_ctor(1, 1, 0);
} else {
 x_658 = x_657;
}
lean_ctor_set(x_658, 0, x_656);
return x_658;
}
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; 
lean_dec(x_566);
lean_dec(x_561);
lean_dec(x_557);
lean_dec(x_552);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_659 = lean_ctor_get(x_568, 0);
lean_inc(x_659);
if (lean_is_exclusive(x_568)) {
 lean_ctor_release(x_568, 0);
 x_660 = x_568;
} else {
 lean_dec_ref(x_568);
 x_660 = lean_box(0);
}
if (lean_is_scalar(x_660)) {
 x_661 = lean_alloc_ctor(1, 1, 0);
} else {
 x_661 = x_660;
}
lean_ctor_set(x_661, 0, x_659);
return x_661;
}
}
else
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; 
lean_dec(x_561);
lean_dec(x_557);
lean_dec(x_552);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_662 = lean_ctor_get(x_565, 0);
lean_inc(x_662);
if (lean_is_exclusive(x_565)) {
 lean_ctor_release(x_565, 0);
 x_663 = x_565;
} else {
 lean_dec_ref(x_565);
 x_663 = lean_box(0);
}
if (lean_is_scalar(x_663)) {
 x_664 = lean_alloc_ctor(1, 1, 0);
} else {
 x_664 = x_663;
}
lean_ctor_set(x_664, 0, x_662);
return x_664;
}
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; 
lean_dec(x_557);
lean_dec(x_552);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_665 = lean_ctor_get(x_560, 0);
lean_inc(x_665);
if (lean_is_exclusive(x_560)) {
 lean_ctor_release(x_560, 0);
 x_666 = x_560;
} else {
 lean_dec_ref(x_560);
 x_666 = lean_box(0);
}
if (lean_is_scalar(x_666)) {
 x_667 = lean_alloc_ctor(1, 1, 0);
} else {
 x_667 = x_666;
}
lean_ctor_set(x_667, 0, x_665);
return x_667;
}
}
else
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; 
lean_dec(x_557);
lean_dec(x_552);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_668 = lean_ctor_get(x_558, 0);
lean_inc(x_668);
if (lean_is_exclusive(x_558)) {
 lean_ctor_release(x_558, 0);
 x_669 = x_558;
} else {
 lean_dec_ref(x_558);
 x_669 = lean_box(0);
}
if (lean_is_scalar(x_669)) {
 x_670 = lean_alloc_ctor(1, 1, 0);
} else {
 x_670 = x_669;
}
lean_ctor_set(x_670, 0, x_668);
return x_670;
}
}
else
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; 
lean_dec(x_552);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_671 = lean_ctor_get(x_556, 0);
lean_inc(x_671);
if (lean_is_exclusive(x_556)) {
 lean_ctor_release(x_556, 0);
 x_672 = x_556;
} else {
 lean_dec_ref(x_556);
 x_672 = lean_box(0);
}
if (lean_is_scalar(x_672)) {
 x_673 = lean_alloc_ctor(1, 1, 0);
} else {
 x_673 = x_672;
}
lean_ctor_set(x_673, 0, x_671);
return x_673;
}
}
else
{
lean_object* x_674; lean_object* x_675; 
lean_dec(x_550);
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_674 = lean_box(0);
x_675 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_675, 0, x_674);
return x_675;
}
}
}
else
{
uint8_t x_676; 
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_676 = !lean_is_exclusive(x_302);
if (x_676 == 0)
{
return x_302;
}
else
{
lean_object* x_677; lean_object* x_678; 
x_677 = lean_ctor_get(x_302, 0);
lean_inc(x_677);
lean_dec(x_302);
x_678 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_678, 0, x_677);
return x_678;
}
}
}
else
{
uint8_t x_679; 
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_679 = !lean_is_exclusive(x_295);
if (x_679 == 0)
{
return x_295;
}
else
{
lean_object* x_680; lean_object* x_681; 
x_680 = lean_ctor_get(x_295, 0);
lean_inc(x_680);
lean_dec(x_295);
x_681 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_681, 0, x_680);
return x_681;
}
}
}
else
{
uint8_t x_682; 
lean_dec(x_288);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_682 = !lean_is_exclusive(x_290);
if (x_682 == 0)
{
return x_290;
}
else
{
lean_object* x_683; lean_object* x_684; 
x_683 = lean_ctor_get(x_290, 0);
lean_inc(x_683);
lean_dec(x_290);
x_684 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_684, 0, x_683);
return x_684;
}
}
}
else
{
uint8_t x_685; 
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_283);
lean_dec_ref(x_282);
lean_dec(x_281);
lean_dec_ref(x_280);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec(x_264);
lean_dec_ref(x_263);
lean_dec(x_262);
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_685 = !lean_is_exclusive(x_287);
if (x_685 == 0)
{
return x_287;
}
else
{
lean_object* x_686; lean_object* x_687; 
x_686 = lean_ctor_get(x_287, 0);
lean_inc(x_686);
lean_dec(x_287);
x_687 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_687, 0, x_686);
return x_687;
}
}
}
}
else
{
uint8_t x_988; 
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_988 = !lean_is_exclusive(x_81);
if (x_988 == 0)
{
return x_81;
}
else
{
lean_object* x_989; lean_object* x_990; 
x_989 = lean_ctor_get(x_81, 0);
lean_inc(x_989);
lean_dec(x_81);
x_990 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_990, 0, x_989);
return x_990;
}
}
}
else
{
uint8_t x_991; 
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_991 = !lean_is_exclusive(x_79);
if (x_991 == 0)
{
return x_79;
}
else
{
lean_object* x_992; lean_object* x_993; 
x_992 = lean_ctor_get(x_79, 0);
lean_inc(x_992);
lean_dec(x_79);
x_993 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_993, 0, x_992);
return x_993;
}
}
}
else
{
uint8_t x_994; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_994 = !lean_is_exclusive(x_76);
if (x_994 == 0)
{
return x_76;
}
else
{
lean_object* x_995; lean_object* x_996; 
x_995 = lean_ctor_get(x_76, 0);
lean_inc(x_995);
lean_dec(x_76);
x_996 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_996, 0, x_995);
return x_996;
}
}
}
else
{
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_72;
}
}
else
{
lean_object* x_997; 
lean_dec(x_69);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_997 = lean_box(0);
lean_ctor_set(x_67, 0, x_997);
return x_67;
}
}
else
{
lean_object* x_998; 
x_998 = lean_ctor_get(x_67, 0);
lean_inc(x_998);
lean_dec(x_67);
if (lean_obj_tag(x_998) == 1)
{
lean_object* x_999; lean_object* x_1000; lean_object* x_1001; 
x_999 = lean_ctor_get(x_998, 0);
lean_inc(x_999);
if (lean_is_exclusive(x_998)) {
 lean_ctor_release(x_998, 0);
 x_1000 = x_998;
} else {
 lean_dec_ref(x_998);
 x_1000 = lean_box(0);
}
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_1001 = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_1001) == 0)
{
lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; 
x_1002 = lean_ctor_get(x_1001, 0);
lean_inc(x_1002);
if (lean_is_exclusive(x_1001)) {
 lean_ctor_release(x_1001, 0);
 x_1003 = x_1001;
} else {
 lean_dec_ref(x_1001);
 x_1003 = lean_box(0);
}
x_1004 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1));
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
lean_inc(x_999);
x_1005 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(x_1004, x_999, x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_1005) == 0)
{
lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; 
x_1006 = lean_ctor_get(x_1005, 0);
lean_inc(x_1006);
lean_dec_ref(x_1005);
x_1007 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__3));
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
lean_inc(x_999);
x_1008 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(x_1007, x_999, x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_1008) == 0)
{
lean_object* x_1009; lean_object* x_1010; 
x_1009 = lean_ctor_get(x_1008, 0);
lean_inc(x_1009);
lean_dec_ref(x_1008);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_1006);
lean_inc(x_1009);
lean_inc_ref(x_1);
lean_inc(x_999);
x_1010 = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(x_999, x_1, x_1009, x_1006, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_1010) == 0)
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; uint8_t x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; uint8_t x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; uint8_t x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; uint8_t x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1372; 
x_1011 = lean_ctor_get(x_1010, 0);
lean_inc(x_1011);
lean_dec_ref(x_1010);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_1006);
lean_inc_ref(x_1);
lean_inc(x_999);
x_1372 = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(x_999, x_1, x_1006, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_1372) == 0)
{
lean_object* x_1373; lean_object* x_1374; 
x_1373 = lean_ctor_get(x_1372, 0);
lean_inc(x_1373);
lean_dec_ref(x_1372);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_1006);
lean_inc_ref(x_1);
lean_inc(x_999);
x_1374 = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(x_999, x_1, x_1006, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_1374) == 0)
{
lean_object* x_1375; lean_object* x_1376; 
x_1375 = lean_ctor_get(x_1374, 0);
lean_inc(x_1375);
lean_dec_ref(x_1374);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_1006);
lean_inc_ref(x_1);
lean_inc(x_999);
x_1376 = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(x_999, x_1, x_1006, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_1376) == 0)
{
lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; uint8_t x_1399; lean_object* x_1452; 
x_1377 = lean_ctor_get(x_1376, 0);
lean_inc(x_1377);
lean_dec_ref(x_1376);
x_1452 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_1452) == 0)
{
lean_object* x_1453; uint8_t x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; uint8_t x_1477; lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; lean_object* x_1506; uint8_t x_1507; lean_object* x_1508; lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; uint8_t x_1536; lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; uint8_t x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; uint8_t x_1561; 
x_1453 = lean_ctor_get(x_1452, 0);
lean_inc(x_1453);
lean_dec_ref(x_1452);
x_1454 = lean_ctor_get_uint8(x_1453, sizeof(void*)*11 + 20);
lean_dec(x_1453);
lean_inc_ref(x_1);
x_1455 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(x_1455, 0, x_1);
if (x_1454 == 0)
{
x_1561 = x_1454;
goto block_1611;
}
else
{
if (lean_obj_tag(x_1002) == 0)
{
uint8_t x_1612; 
x_1612 = 0;
x_1561 = x_1612;
goto block_1611;
}
else
{
if (lean_obj_tag(x_1373) == 0)
{
lean_object* x_1613; lean_object* x_1614; 
lean_dec(x_1377);
lean_dec(x_1375);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec_ref(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1613 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_1614 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_1613, x_1455, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_1614) == 0)
{
lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; 
if (lean_is_exclusive(x_1614)) {
 lean_ctor_release(x_1614, 0);
 x_1615 = x_1614;
} else {
 lean_dec_ref(x_1614);
 x_1615 = lean_box(0);
}
x_1616 = lean_box(0);
if (lean_is_scalar(x_1615)) {
 x_1617 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1617 = x_1615;
}
lean_ctor_set(x_1617, 0, x_1616);
return x_1617;
}
else
{
lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; 
x_1618 = lean_ctor_get(x_1614, 0);
lean_inc(x_1618);
if (lean_is_exclusive(x_1614)) {
 lean_ctor_release(x_1614, 0);
 x_1619 = x_1614;
} else {
 lean_dec_ref(x_1614);
 x_1619 = lean_box(0);
}
if (lean_is_scalar(x_1619)) {
 x_1620 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1620 = x_1619;
}
lean_ctor_set(x_1620, 0, x_1618);
return x_1620;
}
}
else
{
uint8_t x_1621; 
x_1621 = 0;
x_1561 = x_1621;
goto block_1611;
}
}
}
block_1486:
{
if (lean_obj_tag(x_1463) == 0)
{
lean_object* x_1478; lean_object* x_1479; 
lean_dec(x_1475);
lean_dec(x_1473);
lean_dec(x_1472);
lean_dec_ref(x_1471);
lean_dec(x_1470);
lean_dec_ref(x_1469);
lean_dec_ref(x_1468);
lean_dec_ref(x_1467);
lean_dec(x_1466);
lean_dec_ref(x_1465);
lean_dec(x_1464);
lean_dec(x_1462);
lean_dec(x_1461);
lean_dec(x_1460);
lean_dec_ref(x_1459);
lean_dec(x_1458);
lean_dec_ref(x_1457);
lean_dec(x_1456);
lean_dec(x_1377);
lean_dec(x_1375);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1478 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_1479 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_1478, x_1455, x_1476);
lean_dec(x_1476);
if (lean_obj_tag(x_1479) == 0)
{
lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; 
if (lean_is_exclusive(x_1479)) {
 lean_ctor_release(x_1479, 0);
 x_1480 = x_1479;
} else {
 lean_dec_ref(x_1479);
 x_1480 = lean_box(0);
}
x_1481 = lean_box(0);
if (lean_is_scalar(x_1480)) {
 x_1482 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1482 = x_1480;
}
lean_ctor_set(x_1482, 0, x_1481);
return x_1482;
}
else
{
lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; 
x_1483 = lean_ctor_get(x_1479, 0);
lean_inc(x_1483);
if (lean_is_exclusive(x_1479)) {
 lean_ctor_release(x_1479, 0);
 x_1484 = x_1479;
} else {
 lean_dec_ref(x_1479);
 x_1484 = lean_box(0);
}
if (lean_is_scalar(x_1484)) {
 x_1485 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1485 = x_1484;
}
lean_ctor_set(x_1485, 0, x_1483);
return x_1485;
}
}
else
{
lean_dec_ref(x_1455);
x_1378 = x_1456;
x_1379 = x_1457;
x_1380 = x_1458;
x_1381 = x_1459;
x_1382 = x_1460;
x_1383 = x_1461;
x_1384 = x_1462;
x_1385 = x_1463;
x_1386 = x_1464;
x_1387 = x_1465;
x_1388 = x_1467;
x_1389 = x_1466;
x_1390 = x_1468;
x_1391 = x_1470;
x_1392 = x_1469;
x_1393 = x_1471;
x_1394 = x_1472;
x_1395 = x_1473;
x_1396 = lean_box(0);
x_1397 = x_1475;
x_1398 = x_1476;
x_1399 = x_1477;
goto block_1451;
}
}
block_1515:
{
lean_object* x_1509; 
x_1509 = l_Lean_Meta_Grind_getConfig___redArg(x_1488);
if (lean_obj_tag(x_1509) == 0)
{
lean_object* x_1510; uint8_t x_1511; 
x_1510 = lean_ctor_get(x_1509, 0);
lean_inc(x_1510);
lean_dec_ref(x_1509);
x_1511 = lean_ctor_get_uint8(x_1510, sizeof(void*)*11 + 20);
lean_dec(x_1510);
if (x_1511 == 0)
{
lean_dec_ref(x_1455);
x_1378 = x_1487;
x_1379 = x_1488;
x_1380 = x_1489;
x_1381 = x_1490;
x_1382 = x_1491;
x_1383 = x_1493;
x_1384 = x_1494;
x_1385 = x_1508;
x_1386 = x_1495;
x_1387 = x_1496;
x_1388 = x_1497;
x_1389 = x_1498;
x_1390 = x_1499;
x_1391 = x_1501;
x_1392 = x_1500;
x_1393 = x_1502;
x_1394 = x_1503;
x_1395 = x_1504;
x_1396 = lean_box(0);
x_1397 = x_1505;
x_1398 = x_1506;
x_1399 = x_1511;
goto block_1451;
}
else
{
if (lean_obj_tag(x_1002) == 0)
{
if (x_1507 == 0)
{
lean_dec_ref(x_1455);
x_1378 = x_1487;
x_1379 = x_1488;
x_1380 = x_1489;
x_1381 = x_1490;
x_1382 = x_1491;
x_1383 = x_1493;
x_1384 = x_1494;
x_1385 = x_1508;
x_1386 = x_1495;
x_1387 = x_1496;
x_1388 = x_1497;
x_1389 = x_1498;
x_1390 = x_1499;
x_1391 = x_1501;
x_1392 = x_1500;
x_1393 = x_1502;
x_1394 = x_1503;
x_1395 = x_1504;
x_1396 = lean_box(0);
x_1397 = x_1505;
x_1398 = x_1506;
x_1399 = x_1507;
goto block_1451;
}
else
{
x_1456 = x_1487;
x_1457 = x_1488;
x_1458 = x_1489;
x_1459 = x_1490;
x_1460 = x_1491;
x_1461 = x_1493;
x_1462 = x_1494;
x_1463 = x_1508;
x_1464 = x_1495;
x_1465 = x_1496;
x_1466 = x_1498;
x_1467 = x_1497;
x_1468 = x_1499;
x_1469 = x_1500;
x_1470 = x_1501;
x_1471 = x_1502;
x_1472 = x_1503;
x_1473 = x_1504;
x_1474 = lean_box(0);
x_1475 = x_1505;
x_1476 = x_1506;
x_1477 = x_1507;
goto block_1486;
}
}
else
{
x_1456 = x_1487;
x_1457 = x_1488;
x_1458 = x_1489;
x_1459 = x_1490;
x_1460 = x_1491;
x_1461 = x_1493;
x_1462 = x_1494;
x_1463 = x_1508;
x_1464 = x_1495;
x_1465 = x_1496;
x_1466 = x_1498;
x_1467 = x_1497;
x_1468 = x_1499;
x_1469 = x_1500;
x_1470 = x_1501;
x_1471 = x_1502;
x_1472 = x_1503;
x_1473 = x_1504;
x_1474 = lean_box(0);
x_1475 = x_1505;
x_1476 = x_1506;
x_1477 = x_1507;
goto block_1486;
}
}
}
else
{
lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; 
lean_dec(x_1508);
lean_dec(x_1506);
lean_dec(x_1505);
lean_dec(x_1504);
lean_dec(x_1503);
lean_dec_ref(x_1502);
lean_dec(x_1501);
lean_dec_ref(x_1500);
lean_dec_ref(x_1499);
lean_dec(x_1498);
lean_dec_ref(x_1497);
lean_dec_ref(x_1496);
lean_dec(x_1495);
lean_dec(x_1494);
lean_dec(x_1493);
lean_dec(x_1491);
lean_dec_ref(x_1490);
lean_dec(x_1489);
lean_dec_ref(x_1488);
lean_dec(x_1487);
lean_dec_ref(x_1455);
lean_dec(x_1377);
lean_dec(x_1375);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1512 = lean_ctor_get(x_1509, 0);
lean_inc(x_1512);
if (lean_is_exclusive(x_1509)) {
 lean_ctor_release(x_1509, 0);
 x_1513 = x_1509;
} else {
 lean_dec_ref(x_1509);
 x_1513 = lean_box(0);
}
if (lean_is_scalar(x_1513)) {
 x_1514 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1514 = x_1513;
}
lean_ctor_set(x_1514, 0, x_1512);
return x_1514;
}
}
block_1538:
{
lean_object* x_1537; 
x_1537 = lean_box(0);
x_1487 = x_1516;
x_1488 = x_1517;
x_1489 = x_1518;
x_1490 = x_1519;
x_1491 = x_1520;
x_1492 = lean_box(0);
x_1493 = x_1522;
x_1494 = x_1523;
x_1495 = x_1524;
x_1496 = x_1525;
x_1497 = x_1526;
x_1498 = x_1527;
x_1499 = x_1528;
x_1500 = x_1530;
x_1501 = x_1529;
x_1502 = x_1531;
x_1503 = x_1532;
x_1504 = x_1533;
x_1505 = x_1534;
x_1506 = x_1535;
x_1507 = x_1536;
x_1508 = x_1537;
goto block_1515;
}
block_1560:
{
lean_object* x_1559; 
x_1559 = lean_box(0);
x_1516 = x_1557;
x_1517 = x_1550;
x_1518 = x_1555;
x_1519 = x_1554;
x_1520 = x_1544;
x_1521 = lean_box(0);
x_1522 = x_1551;
x_1523 = x_1559;
x_1524 = x_1549;
x_1525 = x_1547;
x_1526 = x_1539;
x_1527 = x_1540;
x_1528 = x_1556;
x_1529 = x_1542;
x_1530 = x_1541;
x_1531 = x_1552;
x_1532 = x_1543;
x_1533 = x_1553;
x_1534 = x_1545;
x_1535 = x_1548;
x_1536 = x_1546;
goto block_1538;
}
block_1611:
{
lean_object* x_1562; 
lean_inc(x_1002);
x_1562 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(x_1002, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_1562) == 0)
{
lean_object* x_1563; lean_object* x_1564; 
x_1563 = lean_ctor_get(x_1562, 0);
lean_inc(x_1563);
lean_dec_ref(x_1562);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_1563);
lean_inc_ref(x_1);
lean_inc(x_999);
x_1564 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(x_999, x_1, x_1563, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_1564) == 0)
{
lean_object* x_1565; lean_object* x_1566; 
x_1565 = lean_ctor_get(x_1564, 0);
lean_inc(x_1565);
lean_dec_ref(x_1564);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_1565);
lean_inc_ref(x_1);
lean_inc(x_999);
x_1566 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(x_999, x_1, x_1565, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_1566) == 0)
{
lean_object* x_1567; lean_object* x_1568; 
x_1567 = lean_ctor_get(x_1566, 0);
lean_inc(x_1567);
if (lean_is_exclusive(x_1566)) {
 lean_ctor_release(x_1566, 0);
 x_1568 = x_1566;
} else {
 lean_dec_ref(x_1566);
 x_1568 = lean_box(0);
}
if (lean_obj_tag(x_1567) == 1)
{
lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; 
lean_dec(x_1568);
x_1569 = lean_ctor_get(x_1567, 0);
lean_inc(x_1569);
lean_dec_ref(x_1567);
x_1570 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__63));
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
lean_inc(x_999);
x_1571 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(x_1570, x_999, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_1571) == 0)
{
lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; 
x_1572 = lean_ctor_get(x_1571, 0);
lean_inc(x_1572);
lean_dec_ref(x_1571);
x_1573 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__65));
x_1574 = lean_box(0);
lean_inc(x_999);
x_1575 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1575, 0, x_999);
lean_ctor_set(x_1575, 1, x_1574);
lean_inc_ref(x_1575);
lean_inc(x_999);
x_1576 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1576, 0, x_999);
lean_ctor_set(x_1576, 1, x_1575);
lean_inc_ref(x_1576);
lean_inc(x_999);
x_1577 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1577, 0, x_999);
lean_ctor_set(x_1577, 1, x_1576);
lean_inc_ref(x_1577);
x_1578 = l_Lean_mkConst(x_1573, x_1577);
lean_inc(x_1572);
lean_inc_ref_n(x_1, 3);
x_1579 = l_Lean_mkApp4(x_1578, x_1, x_1, x_1, x_1572);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_1580 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_1579, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_1580) == 0)
{
if (lean_obj_tag(x_1006) == 1)
{
if (lean_obj_tag(x_1373) == 1)
{
lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; 
x_1581 = lean_ctor_get(x_1580, 0);
lean_inc(x_1581);
lean_dec_ref(x_1580);
x_1582 = lean_ctor_get(x_1006, 0);
x_1583 = lean_ctor_get(x_1373, 0);
x_1584 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__67));
lean_inc_ref(x_1575);
x_1585 = l_Lean_mkConst(x_1584, x_1575);
lean_inc(x_1583);
lean_inc(x_1582);
lean_inc(x_1572);
lean_inc_ref(x_1);
x_1586 = l_Lean_mkApp4(x_1585, x_1, x_1572, x_1582, x_1583);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_1587 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_1586, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_1587) == 0)
{
lean_object* x_1588; 
x_1588 = lean_ctor_get(x_1587, 0);
lean_inc(x_1588);
lean_dec_ref(x_1587);
if (lean_obj_tag(x_1588) == 0)
{
lean_dec_ref(x_1373);
x_1516 = x_11;
x_1517 = x_4;
x_1518 = x_9;
x_1519 = x_8;
x_1520 = x_1563;
x_1521 = lean_box(0);
x_1522 = x_5;
x_1523 = x_1588;
x_1524 = x_3;
x_1525 = x_1569;
x_1526 = x_1581;
x_1527 = x_1575;
x_1528 = x_10;
x_1529 = x_1577;
x_1530 = x_1572;
x_1531 = x_6;
x_1532 = x_1576;
x_1533 = x_7;
x_1534 = x_1565;
x_1535 = x_2;
x_1536 = x_1561;
goto block_1538;
}
else
{
if (x_1561 == 0)
{
x_1487 = x_11;
x_1488 = x_4;
x_1489 = x_9;
x_1490 = x_8;
x_1491 = x_1563;
x_1492 = lean_box(0);
x_1493 = x_5;
x_1494 = x_1588;
x_1495 = x_3;
x_1496 = x_1569;
x_1497 = x_1581;
x_1498 = x_1575;
x_1499 = x_10;
x_1500 = x_1572;
x_1501 = x_1577;
x_1502 = x_6;
x_1503 = x_1576;
x_1504 = x_7;
x_1505 = x_1565;
x_1506 = x_2;
x_1507 = x_1561;
x_1508 = x_1373;
goto block_1515;
}
else
{
lean_dec_ref(x_1373);
x_1516 = x_11;
x_1517 = x_4;
x_1518 = x_9;
x_1519 = x_8;
x_1520 = x_1563;
x_1521 = lean_box(0);
x_1522 = x_5;
x_1523 = x_1588;
x_1524 = x_3;
x_1525 = x_1569;
x_1526 = x_1581;
x_1527 = x_1575;
x_1528 = x_10;
x_1529 = x_1577;
x_1530 = x_1572;
x_1531 = x_6;
x_1532 = x_1576;
x_1533 = x_7;
x_1534 = x_1565;
x_1535 = x_2;
x_1536 = x_1561;
goto block_1538;
}
}
}
else
{
lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; 
lean_dec(x_1581);
lean_dec_ref(x_1577);
lean_dec_ref(x_1576);
lean_dec_ref(x_1575);
lean_dec(x_1572);
lean_dec(x_1569);
lean_dec(x_1565);
lean_dec(x_1563);
lean_dec_ref(x_1455);
lean_dec(x_1377);
lean_dec(x_1375);
lean_dec_ref(x_1373);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec_ref(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1589 = lean_ctor_get(x_1587, 0);
lean_inc(x_1589);
if (lean_is_exclusive(x_1587)) {
 lean_ctor_release(x_1587, 0);
 x_1590 = x_1587;
} else {
 lean_dec_ref(x_1587);
 x_1590 = lean_box(0);
}
if (lean_is_scalar(x_1590)) {
 x_1591 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1591 = x_1590;
}
lean_ctor_set(x_1591, 0, x_1589);
return x_1591;
}
}
else
{
lean_object* x_1592; 
lean_dec(x_1373);
x_1592 = lean_ctor_get(x_1580, 0);
lean_inc(x_1592);
lean_dec_ref(x_1580);
x_1539 = x_1592;
x_1540 = x_1575;
x_1541 = x_1572;
x_1542 = x_1577;
x_1543 = x_1576;
x_1544 = x_1563;
x_1545 = x_1565;
x_1546 = x_1561;
x_1547 = x_1569;
x_1548 = x_2;
x_1549 = x_3;
x_1550 = x_4;
x_1551 = x_5;
x_1552 = x_6;
x_1553 = x_7;
x_1554 = x_8;
x_1555 = x_9;
x_1556 = x_10;
x_1557 = x_11;
x_1558 = lean_box(0);
goto block_1560;
}
}
else
{
lean_object* x_1593; 
lean_dec(x_1373);
x_1593 = lean_ctor_get(x_1580, 0);
lean_inc(x_1593);
lean_dec_ref(x_1580);
x_1539 = x_1593;
x_1540 = x_1575;
x_1541 = x_1572;
x_1542 = x_1577;
x_1543 = x_1576;
x_1544 = x_1563;
x_1545 = x_1565;
x_1546 = x_1561;
x_1547 = x_1569;
x_1548 = x_2;
x_1549 = x_3;
x_1550 = x_4;
x_1551 = x_5;
x_1552 = x_6;
x_1553 = x_7;
x_1554 = x_8;
x_1555 = x_9;
x_1556 = x_10;
x_1557 = x_11;
x_1558 = lean_box(0);
goto block_1560;
}
}
else
{
lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; 
lean_dec_ref(x_1577);
lean_dec_ref(x_1576);
lean_dec_ref(x_1575);
lean_dec(x_1572);
lean_dec(x_1569);
lean_dec(x_1565);
lean_dec(x_1563);
lean_dec_ref(x_1455);
lean_dec(x_1377);
lean_dec(x_1375);
lean_dec(x_1373);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1594 = lean_ctor_get(x_1580, 0);
lean_inc(x_1594);
if (lean_is_exclusive(x_1580)) {
 lean_ctor_release(x_1580, 0);
 x_1595 = x_1580;
} else {
 lean_dec_ref(x_1580);
 x_1595 = lean_box(0);
}
if (lean_is_scalar(x_1595)) {
 x_1596 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1596 = x_1595;
}
lean_ctor_set(x_1596, 0, x_1594);
return x_1596;
}
}
else
{
lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; 
lean_dec(x_1569);
lean_dec(x_1565);
lean_dec(x_1563);
lean_dec_ref(x_1455);
lean_dec(x_1377);
lean_dec(x_1375);
lean_dec(x_1373);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1597 = lean_ctor_get(x_1571, 0);
lean_inc(x_1597);
if (lean_is_exclusive(x_1571)) {
 lean_ctor_release(x_1571, 0);
 x_1598 = x_1571;
} else {
 lean_dec_ref(x_1571);
 x_1598 = lean_box(0);
}
if (lean_is_scalar(x_1598)) {
 x_1599 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1599 = x_1598;
}
lean_ctor_set(x_1599, 0, x_1597);
return x_1599;
}
}
else
{
lean_object* x_1600; lean_object* x_1601; 
lean_dec(x_1567);
lean_dec(x_1565);
lean_dec(x_1563);
lean_dec_ref(x_1455);
lean_dec(x_1377);
lean_dec(x_1375);
lean_dec(x_1373);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1600 = lean_box(0);
if (lean_is_scalar(x_1568)) {
 x_1601 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1601 = x_1568;
}
lean_ctor_set(x_1601, 0, x_1600);
return x_1601;
}
}
else
{
lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; 
lean_dec(x_1565);
lean_dec(x_1563);
lean_dec_ref(x_1455);
lean_dec(x_1377);
lean_dec(x_1375);
lean_dec(x_1373);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1602 = lean_ctor_get(x_1566, 0);
lean_inc(x_1602);
if (lean_is_exclusive(x_1566)) {
 lean_ctor_release(x_1566, 0);
 x_1603 = x_1566;
} else {
 lean_dec_ref(x_1566);
 x_1603 = lean_box(0);
}
if (lean_is_scalar(x_1603)) {
 x_1604 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1604 = x_1603;
}
lean_ctor_set(x_1604, 0, x_1602);
return x_1604;
}
}
else
{
lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; 
lean_dec(x_1563);
lean_dec_ref(x_1455);
lean_dec(x_1377);
lean_dec(x_1375);
lean_dec(x_1373);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1605 = lean_ctor_get(x_1564, 0);
lean_inc(x_1605);
if (lean_is_exclusive(x_1564)) {
 lean_ctor_release(x_1564, 0);
 x_1606 = x_1564;
} else {
 lean_dec_ref(x_1564);
 x_1606 = lean_box(0);
}
if (lean_is_scalar(x_1606)) {
 x_1607 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1607 = x_1606;
}
lean_ctor_set(x_1607, 0, x_1605);
return x_1607;
}
}
else
{
lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; 
lean_dec_ref(x_1455);
lean_dec(x_1377);
lean_dec(x_1375);
lean_dec(x_1373);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1608 = lean_ctor_get(x_1562, 0);
lean_inc(x_1608);
if (lean_is_exclusive(x_1562)) {
 lean_ctor_release(x_1562, 0);
 x_1609 = x_1562;
} else {
 lean_dec_ref(x_1562);
 x_1609 = lean_box(0);
}
if (lean_is_scalar(x_1609)) {
 x_1610 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1610 = x_1609;
}
lean_ctor_set(x_1610, 0, x_1608);
return x_1610;
}
}
}
else
{
lean_object* x_1622; lean_object* x_1623; lean_object* x_1624; 
lean_dec(x_1377);
lean_dec(x_1375);
lean_dec(x_1373);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1622 = lean_ctor_get(x_1452, 0);
lean_inc(x_1622);
if (lean_is_exclusive(x_1452)) {
 lean_ctor_release(x_1452, 0);
 x_1623 = x_1452;
} else {
 lean_dec_ref(x_1452);
 x_1623 = lean_box(0);
}
if (lean_is_scalar(x_1623)) {
 x_1624 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1624 = x_1623;
}
lean_ctor_set(x_1624, 0, x_1622);
return x_1624;
}
block_1451:
{
lean_object* x_1400; lean_object* x_1401; 
x_1400 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__51));
lean_inc(x_1378);
lean_inc_ref(x_1390);
lean_inc(x_1380);
lean_inc_ref(x_1381);
lean_inc_ref(x_1);
lean_inc(x_999);
lean_inc(x_1385);
lean_inc(x_1006);
x_1401 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(x_1006, x_1385, x_1375, x_1400, x_999, x_1, x_1386, x_1379, x_1383, x_1393, x_1395, x_1381, x_1380, x_1390, x_1378);
if (lean_obj_tag(x_1401) == 0)
{
lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; 
x_1402 = lean_ctor_get(x_1401, 0);
lean_inc(x_1402);
lean_dec_ref(x_1401);
x_1403 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__54));
lean_inc(x_1378);
lean_inc_ref(x_1390);
lean_inc(x_1380);
lean_inc_ref(x_1381);
lean_inc_ref(x_1);
lean_inc(x_999);
lean_inc(x_1006);
x_1404 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(x_1006, x_1402, x_1377, x_1403, x_999, x_1, x_1386, x_1379, x_1383, x_1393, x_1395, x_1381, x_1380, x_1390, x_1378);
if (lean_obj_tag(x_1404) == 0)
{
lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; 
x_1405 = lean_ctor_get(x_1404, 0);
lean_inc(x_1405);
lean_dec_ref(x_1404);
x_1406 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0));
x_1407 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1));
x_1408 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2));
x_1409 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__56));
lean_inc(x_1389);
x_1410 = l_Lean_mkConst(x_1409, x_1389);
lean_inc_ref(x_1387);
lean_inc_ref(x_1);
x_1411 = l_Lean_mkAppB(x_1410, x_1, x_1387);
x_1412 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__57));
x_1413 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__59));
lean_inc(x_1389);
x_1414 = l_Lean_mkConst(x_1413, x_1389);
lean_inc_ref(x_1411);
lean_inc_ref(x_1);
x_1415 = l_Lean_mkAppB(x_1414, x_1, x_1411);
lean_inc(x_1378);
lean_inc_ref(x_1390);
lean_inc(x_1380);
lean_inc_ref(x_1381);
lean_inc(x_1397);
lean_inc_ref(x_1);
lean_inc(x_999);
x_1416 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(x_999, x_1, x_1397, x_1381, x_1380, x_1390, x_1378);
if (lean_obj_tag(x_1416) == 0)
{
lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; 
x_1417 = lean_ctor_get(x_1416, 0);
lean_inc(x_1417);
lean_dec_ref(x_1416);
x_1418 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__61));
lean_inc(x_1378);
lean_inc_ref(x_1390);
lean_inc(x_1380);
lean_inc_ref(x_1381);
lean_inc_ref(x_1);
lean_inc(x_999);
x_1419 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(x_1418, x_999, x_1, x_1381, x_1380, x_1390, x_1378);
if (lean_obj_tag(x_1419) == 0)
{
lean_object* x_1420; lean_object* x_1421; 
x_1420 = lean_ctor_get(x_1419, 0);
lean_inc(x_1420);
lean_dec_ref(x_1419);
lean_inc(x_1378);
lean_inc_ref(x_1390);
lean_inc(x_1380);
lean_inc_ref(x_1381);
lean_inc(x_1395);
lean_inc_ref(x_1393);
lean_inc(x_1383);
lean_inc_ref(x_1379);
lean_inc(x_1386);
lean_inc(x_1398);
lean_inc_ref(x_1);
lean_inc(x_999);
x_1421 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(x_999, x_1, x_1398, x_1386, x_1379, x_1383, x_1393, x_1395, x_1381, x_1380, x_1390, x_1378);
if (lean_obj_tag(x_1421) == 0)
{
lean_object* x_1422; lean_object* x_1423; 
x_1422 = lean_ctor_get(x_1421, 0);
lean_inc(x_1422);
lean_dec_ref(x_1421);
lean_inc(x_1378);
lean_inc_ref(x_1390);
lean_inc(x_1380);
lean_inc_ref(x_1381);
lean_inc(x_1385);
lean_inc(x_1009);
lean_inc(x_1006);
lean_inc(x_1417);
lean_inc_ref(x_1);
lean_inc(x_999);
x_1423 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(x_999, x_1, x_1417, x_1006, x_1009, x_1385, x_1386, x_1379, x_1383, x_1393, x_1395, x_1381, x_1380, x_1390, x_1378);
if (lean_obj_tag(x_1423) == 0)
{
if (lean_obj_tag(x_1417) == 1)
{
lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; 
x_1424 = lean_ctor_get(x_1423, 0);
lean_inc(x_1424);
lean_dec_ref(x_1423);
x_1425 = lean_ctor_get(x_1417, 0);
lean_inc(x_1425);
lean_dec_ref(x_1417);
lean_inc(x_1378);
lean_inc_ref(x_1390);
lean_inc(x_1380);
lean_inc_ref(x_1381);
lean_inc(x_1395);
lean_inc_ref(x_1393);
lean_inc(x_1383);
lean_inc_ref(x_1379);
lean_inc(x_1386);
lean_inc(x_1398);
lean_inc_ref(x_1);
lean_inc(x_999);
x_1426 = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(x_999, x_1, x_1425, x_1398, x_1386, x_1379, x_1383, x_1393, x_1395, x_1381, x_1380, x_1390, x_1378);
if (lean_obj_tag(x_1426) == 0)
{
lean_object* x_1427; 
x_1427 = lean_ctor_get(x_1426, 0);
lean_inc(x_1427);
lean_dec_ref(x_1426);
x_1183 = x_1424;
x_1184 = x_1422;
x_1185 = x_1408;
x_1186 = x_1382;
x_1187 = x_1420;
x_1188 = x_1406;
x_1189 = x_1407;
x_1190 = x_1415;
x_1191 = x_1384;
x_1192 = x_1387;
x_1193 = x_1385;
x_1194 = x_1412;
x_1195 = x_1388;
x_1196 = x_1389;
x_1197 = x_1392;
x_1198 = x_1391;
x_1199 = x_1399;
x_1200 = x_1394;
x_1201 = x_1411;
x_1202 = x_1405;
x_1203 = x_1397;
x_1204 = x_1427;
x_1205 = x_1398;
x_1206 = x_1386;
x_1207 = x_1379;
x_1208 = x_1383;
x_1209 = x_1393;
x_1210 = x_1395;
x_1211 = x_1381;
x_1212 = x_1380;
x_1213 = x_1390;
x_1214 = x_1378;
x_1215 = lean_box(0);
goto block_1371;
}
else
{
lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; 
lean_dec(x_1424);
lean_dec(x_1422);
lean_dec(x_1420);
lean_dec_ref(x_1415);
lean_dec_ref(x_1411);
lean_dec(x_1405);
lean_dec(x_1398);
lean_dec(x_1397);
lean_dec(x_1395);
lean_dec(x_1394);
lean_dec_ref(x_1393);
lean_dec_ref(x_1392);
lean_dec(x_1391);
lean_dec_ref(x_1390);
lean_dec(x_1389);
lean_dec_ref(x_1388);
lean_dec_ref(x_1387);
lean_dec(x_1386);
lean_dec(x_1385);
lean_dec(x_1384);
lean_dec(x_1383);
lean_dec(x_1382);
lean_dec_ref(x_1381);
lean_dec(x_1380);
lean_dec_ref(x_1379);
lean_dec(x_1378);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1428 = lean_ctor_get(x_1426, 0);
lean_inc(x_1428);
if (lean_is_exclusive(x_1426)) {
 lean_ctor_release(x_1426, 0);
 x_1429 = x_1426;
} else {
 lean_dec_ref(x_1426);
 x_1429 = lean_box(0);
}
if (lean_is_scalar(x_1429)) {
 x_1430 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1430 = x_1429;
}
lean_ctor_set(x_1430, 0, x_1428);
return x_1430;
}
}
else
{
lean_object* x_1431; lean_object* x_1432; 
lean_dec(x_1417);
x_1431 = lean_ctor_get(x_1423, 0);
lean_inc(x_1431);
lean_dec_ref(x_1423);
x_1432 = lean_box(0);
x_1183 = x_1431;
x_1184 = x_1422;
x_1185 = x_1408;
x_1186 = x_1382;
x_1187 = x_1420;
x_1188 = x_1406;
x_1189 = x_1407;
x_1190 = x_1415;
x_1191 = x_1384;
x_1192 = x_1387;
x_1193 = x_1385;
x_1194 = x_1412;
x_1195 = x_1388;
x_1196 = x_1389;
x_1197 = x_1392;
x_1198 = x_1391;
x_1199 = x_1399;
x_1200 = x_1394;
x_1201 = x_1411;
x_1202 = x_1405;
x_1203 = x_1397;
x_1204 = x_1432;
x_1205 = x_1398;
x_1206 = x_1386;
x_1207 = x_1379;
x_1208 = x_1383;
x_1209 = x_1393;
x_1210 = x_1395;
x_1211 = x_1381;
x_1212 = x_1380;
x_1213 = x_1390;
x_1214 = x_1378;
x_1215 = lean_box(0);
goto block_1371;
}
}
else
{
lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; 
lean_dec(x_1422);
lean_dec(x_1420);
lean_dec(x_1417);
lean_dec_ref(x_1415);
lean_dec_ref(x_1411);
lean_dec(x_1405);
lean_dec(x_1398);
lean_dec(x_1397);
lean_dec(x_1395);
lean_dec(x_1394);
lean_dec_ref(x_1393);
lean_dec_ref(x_1392);
lean_dec(x_1391);
lean_dec_ref(x_1390);
lean_dec(x_1389);
lean_dec_ref(x_1388);
lean_dec_ref(x_1387);
lean_dec(x_1386);
lean_dec(x_1385);
lean_dec(x_1384);
lean_dec(x_1383);
lean_dec(x_1382);
lean_dec_ref(x_1381);
lean_dec(x_1380);
lean_dec_ref(x_1379);
lean_dec(x_1378);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1433 = lean_ctor_get(x_1423, 0);
lean_inc(x_1433);
if (lean_is_exclusive(x_1423)) {
 lean_ctor_release(x_1423, 0);
 x_1434 = x_1423;
} else {
 lean_dec_ref(x_1423);
 x_1434 = lean_box(0);
}
if (lean_is_scalar(x_1434)) {
 x_1435 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1435 = x_1434;
}
lean_ctor_set(x_1435, 0, x_1433);
return x_1435;
}
}
else
{
lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; 
lean_dec(x_1420);
lean_dec(x_1417);
lean_dec_ref(x_1415);
lean_dec_ref(x_1411);
lean_dec(x_1405);
lean_dec(x_1398);
lean_dec(x_1397);
lean_dec(x_1395);
lean_dec(x_1394);
lean_dec_ref(x_1393);
lean_dec_ref(x_1392);
lean_dec(x_1391);
lean_dec_ref(x_1390);
lean_dec(x_1389);
lean_dec_ref(x_1388);
lean_dec_ref(x_1387);
lean_dec(x_1386);
lean_dec(x_1385);
lean_dec(x_1384);
lean_dec(x_1383);
lean_dec(x_1382);
lean_dec_ref(x_1381);
lean_dec(x_1380);
lean_dec_ref(x_1379);
lean_dec(x_1378);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1436 = lean_ctor_get(x_1421, 0);
lean_inc(x_1436);
if (lean_is_exclusive(x_1421)) {
 lean_ctor_release(x_1421, 0);
 x_1437 = x_1421;
} else {
 lean_dec_ref(x_1421);
 x_1437 = lean_box(0);
}
if (lean_is_scalar(x_1437)) {
 x_1438 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1438 = x_1437;
}
lean_ctor_set(x_1438, 0, x_1436);
return x_1438;
}
}
else
{
lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; 
lean_dec(x_1417);
lean_dec_ref(x_1415);
lean_dec_ref(x_1411);
lean_dec(x_1405);
lean_dec(x_1398);
lean_dec(x_1397);
lean_dec(x_1395);
lean_dec(x_1394);
lean_dec_ref(x_1393);
lean_dec_ref(x_1392);
lean_dec(x_1391);
lean_dec_ref(x_1390);
lean_dec(x_1389);
lean_dec_ref(x_1388);
lean_dec_ref(x_1387);
lean_dec(x_1386);
lean_dec(x_1385);
lean_dec(x_1384);
lean_dec(x_1383);
lean_dec(x_1382);
lean_dec_ref(x_1381);
lean_dec(x_1380);
lean_dec_ref(x_1379);
lean_dec(x_1378);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1439 = lean_ctor_get(x_1419, 0);
lean_inc(x_1439);
if (lean_is_exclusive(x_1419)) {
 lean_ctor_release(x_1419, 0);
 x_1440 = x_1419;
} else {
 lean_dec_ref(x_1419);
 x_1440 = lean_box(0);
}
if (lean_is_scalar(x_1440)) {
 x_1441 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1441 = x_1440;
}
lean_ctor_set(x_1441, 0, x_1439);
return x_1441;
}
}
else
{
lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; 
lean_dec_ref(x_1415);
lean_dec_ref(x_1411);
lean_dec(x_1405);
lean_dec(x_1398);
lean_dec(x_1397);
lean_dec(x_1395);
lean_dec(x_1394);
lean_dec_ref(x_1393);
lean_dec_ref(x_1392);
lean_dec(x_1391);
lean_dec_ref(x_1390);
lean_dec(x_1389);
lean_dec_ref(x_1388);
lean_dec_ref(x_1387);
lean_dec(x_1386);
lean_dec(x_1385);
lean_dec(x_1384);
lean_dec(x_1383);
lean_dec(x_1382);
lean_dec_ref(x_1381);
lean_dec(x_1380);
lean_dec_ref(x_1379);
lean_dec(x_1378);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1442 = lean_ctor_get(x_1416, 0);
lean_inc(x_1442);
if (lean_is_exclusive(x_1416)) {
 lean_ctor_release(x_1416, 0);
 x_1443 = x_1416;
} else {
 lean_dec_ref(x_1416);
 x_1443 = lean_box(0);
}
if (lean_is_scalar(x_1443)) {
 x_1444 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1444 = x_1443;
}
lean_ctor_set(x_1444, 0, x_1442);
return x_1444;
}
}
else
{
lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; 
lean_dec(x_1398);
lean_dec(x_1397);
lean_dec(x_1395);
lean_dec(x_1394);
lean_dec_ref(x_1393);
lean_dec_ref(x_1392);
lean_dec(x_1391);
lean_dec_ref(x_1390);
lean_dec(x_1389);
lean_dec_ref(x_1388);
lean_dec_ref(x_1387);
lean_dec(x_1386);
lean_dec(x_1385);
lean_dec(x_1384);
lean_dec(x_1383);
lean_dec(x_1382);
lean_dec_ref(x_1381);
lean_dec(x_1380);
lean_dec_ref(x_1379);
lean_dec(x_1378);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1445 = lean_ctor_get(x_1404, 0);
lean_inc(x_1445);
if (lean_is_exclusive(x_1404)) {
 lean_ctor_release(x_1404, 0);
 x_1446 = x_1404;
} else {
 lean_dec_ref(x_1404);
 x_1446 = lean_box(0);
}
if (lean_is_scalar(x_1446)) {
 x_1447 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1447 = x_1446;
}
lean_ctor_set(x_1447, 0, x_1445);
return x_1447;
}
}
else
{
lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; 
lean_dec(x_1398);
lean_dec(x_1397);
lean_dec(x_1395);
lean_dec(x_1394);
lean_dec_ref(x_1393);
lean_dec_ref(x_1392);
lean_dec(x_1391);
lean_dec_ref(x_1390);
lean_dec(x_1389);
lean_dec_ref(x_1388);
lean_dec_ref(x_1387);
lean_dec(x_1386);
lean_dec(x_1385);
lean_dec(x_1384);
lean_dec(x_1383);
lean_dec(x_1382);
lean_dec_ref(x_1381);
lean_dec(x_1380);
lean_dec_ref(x_1379);
lean_dec(x_1378);
lean_dec(x_1377);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1448 = lean_ctor_get(x_1401, 0);
lean_inc(x_1448);
if (lean_is_exclusive(x_1401)) {
 lean_ctor_release(x_1401, 0);
 x_1449 = x_1401;
} else {
 lean_dec_ref(x_1401);
 x_1449 = lean_box(0);
}
if (lean_is_scalar(x_1449)) {
 x_1450 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1450 = x_1449;
}
lean_ctor_set(x_1450, 0, x_1448);
return x_1450;
}
}
}
else
{
lean_object* x_1625; lean_object* x_1626; lean_object* x_1627; 
lean_dec(x_1375);
lean_dec(x_1373);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1625 = lean_ctor_get(x_1376, 0);
lean_inc(x_1625);
if (lean_is_exclusive(x_1376)) {
 lean_ctor_release(x_1376, 0);
 x_1626 = x_1376;
} else {
 lean_dec_ref(x_1376);
 x_1626 = lean_box(0);
}
if (lean_is_scalar(x_1626)) {
 x_1627 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1627 = x_1626;
}
lean_ctor_set(x_1627, 0, x_1625);
return x_1627;
}
}
else
{
lean_object* x_1628; lean_object* x_1629; lean_object* x_1630; 
lean_dec(x_1373);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1628 = lean_ctor_get(x_1374, 0);
lean_inc(x_1628);
if (lean_is_exclusive(x_1374)) {
 lean_ctor_release(x_1374, 0);
 x_1629 = x_1374;
} else {
 lean_dec_ref(x_1374);
 x_1629 = lean_box(0);
}
if (lean_is_scalar(x_1629)) {
 x_1630 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1630 = x_1629;
}
lean_ctor_set(x_1630, 0, x_1628);
return x_1630;
}
}
else
{
lean_object* x_1631; lean_object* x_1632; lean_object* x_1633; 
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1631 = lean_ctor_get(x_1372, 0);
lean_inc(x_1631);
if (lean_is_exclusive(x_1372)) {
 lean_ctor_release(x_1372, 0);
 x_1632 = x_1372;
} else {
 lean_dec_ref(x_1372);
 x_1632 = lean_box(0);
}
if (lean_is_scalar(x_1632)) {
 x_1633 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1633 = x_1632;
}
lean_ctor_set(x_1633, 0, x_1631);
return x_1633;
}
block_1074:
{
lean_object* x_1048; 
x_1048 = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(x_1037, x_1045);
if (lean_obj_tag(x_1048) == 0)
{
lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; size_t x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; 
x_1049 = lean_ctor_get(x_1048, 0);
lean_inc(x_1049);
lean_dec_ref(x_1048);
x_1050 = lean_ctor_get(x_1049, 0);
lean_inc_ref(x_1050);
lean_dec(x_1049);
x_1051 = lean_array_get_size(x_1050);
lean_dec_ref(x_1050);
x_1052 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__4;
x_1053 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__5;
x_1054 = 5;
lean_inc(x_1013);
x_1055 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_1055, 0, x_1053);
lean_ctor_set(x_1055, 1, x_1052);
lean_ctor_set(x_1055, 2, x_1013);
lean_ctor_set(x_1055, 3, x_1013);
lean_ctor_set_usize(x_1055, 4, x_1054);
x_1056 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__7;
x_1057 = lean_box(0);
x_1058 = lean_box(0);
lean_inc_ref_n(x_1055, 7);
lean_inc(x_1017);
lean_inc(x_1021);
lean_inc(x_1020);
lean_inc(x_1014);
lean_inc(x_1032);
x_1059 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_1059, 0, x_1051);
lean_ctor_set(x_1059, 1, x_1002);
lean_ctor_set(x_1059, 2, x_1);
lean_ctor_set(x_1059, 3, x_999);
lean_ctor_set(x_1059, 4, x_1026);
lean_ctor_set(x_1059, 5, x_1006);
lean_ctor_set(x_1059, 6, x_1009);
lean_ctor_set(x_1059, 7, x_1011);
lean_ctor_set(x_1059, 8, x_1027);
lean_ctor_set(x_1059, 9, x_1025);
lean_ctor_set(x_1059, 10, x_1031);
lean_ctor_set(x_1059, 11, x_1030);
lean_ctor_set(x_1059, 12, x_1032);
lean_ctor_set(x_1059, 13, x_1019);
lean_ctor_set(x_1059, 14, x_1014);
lean_ctor_set(x_1059, 15, x_1020);
lean_ctor_set(x_1059, 16, x_1021);
lean_ctor_set(x_1059, 17, x_1035);
lean_ctor_set(x_1059, 18, x_1034);
lean_ctor_set(x_1059, 19, x_1017);
lean_ctor_set(x_1059, 20, x_1023);
lean_ctor_set(x_1059, 21, x_1022);
lean_ctor_set(x_1059, 22, x_1028);
lean_ctor_set(x_1059, 23, x_1012);
lean_ctor_set(x_1059, 24, x_1024);
lean_ctor_set(x_1059, 25, x_1018);
lean_ctor_set(x_1059, 26, x_1016);
lean_ctor_set(x_1059, 27, x_1036);
lean_ctor_set(x_1059, 28, x_1015);
lean_ctor_set(x_1059, 29, x_1033);
lean_ctor_set(x_1059, 30, x_1055);
lean_ctor_set(x_1059, 31, x_1056);
lean_ctor_set(x_1059, 32, x_1055);
lean_ctor_set(x_1059, 33, x_1055);
lean_ctor_set(x_1059, 34, x_1055);
lean_ctor_set(x_1059, 35, x_1055);
lean_ctor_set(x_1059, 36, x_1057);
lean_ctor_set(x_1059, 37, x_1056);
lean_ctor_set(x_1059, 38, x_1055);
lean_ctor_set(x_1059, 39, x_1058);
lean_ctor_set(x_1059, 40, x_1055);
lean_ctor_set(x_1059, 41, x_1055);
lean_ctor_set_uint8(x_1059, sizeof(void*)*42, x_1029);
x_1060 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__1), 2, 1);
lean_closure_set(x_1060, 0, x_1059);
x_1061 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_1062 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_1061, x_1060, x_1037);
if (lean_obj_tag(x_1062) == 0)
{
lean_dec_ref(x_1062);
if (lean_obj_tag(x_1017) == 1)
{
if (lean_obj_tag(x_1032) == 0)
{
lean_dec(x_1046);
lean_dec_ref(x_1045);
lean_dec(x_1044);
lean_dec_ref(x_1043);
lean_dec(x_1042);
lean_dec_ref(x_1041);
lean_dec(x_1040);
lean_dec_ref(x_1039);
lean_dec(x_1038);
lean_dec(x_1037);
lean_dec(x_1021);
lean_dec(x_1020);
lean_dec_ref(x_1017);
lean_dec(x_1014);
x_13 = x_1051;
x_14 = lean_box(0);
goto block_17;
}
else
{
lean_dec_ref(x_1032);
if (lean_obj_tag(x_1014) == 0)
{
if (x_1029 == 0)
{
if (lean_obj_tag(x_1020) == 0)
{
lean_object* x_1063; uint8_t x_1064; 
x_1063 = lean_ctor_get(x_1017, 0);
lean_inc(x_1063);
lean_dec_ref(x_1017);
x_1064 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(x_1021);
lean_dec(x_1021);
if (x_1064 == 0)
{
lean_dec(x_1063);
lean_dec(x_1046);
lean_dec_ref(x_1045);
lean_dec(x_1044);
lean_dec_ref(x_1043);
lean_dec(x_1042);
lean_dec_ref(x_1041);
lean_dec(x_1040);
lean_dec_ref(x_1039);
lean_dec(x_1038);
lean_dec(x_1037);
x_13 = x_1051;
x_14 = lean_box(0);
goto block_17;
}
else
{
x_46 = x_1037;
x_47 = x_1043;
x_48 = x_1051;
x_49 = x_1040;
x_50 = x_1039;
x_51 = x_1045;
x_52 = x_1042;
x_53 = x_1029;
x_54 = x_1063;
x_55 = x_1046;
x_56 = x_1038;
x_57 = lean_box(0);
x_58 = x_1041;
x_59 = x_1044;
goto block_66;
}
}
else
{
lean_object* x_1065; 
lean_dec(x_1021);
lean_dec_ref(x_1020);
x_1065 = lean_ctor_get(x_1017, 0);
lean_inc(x_1065);
lean_dec_ref(x_1017);
x_46 = x_1037;
x_47 = x_1043;
x_48 = x_1051;
x_49 = x_1040;
x_50 = x_1039;
x_51 = x_1045;
x_52 = x_1042;
x_53 = x_1029;
x_54 = x_1065;
x_55 = x_1046;
x_56 = x_1038;
x_57 = lean_box(0);
x_58 = x_1041;
x_59 = x_1044;
goto block_66;
}
}
else
{
lean_object* x_1066; 
lean_dec(x_1021);
lean_dec(x_1020);
x_1066 = lean_ctor_get(x_1017, 0);
lean_inc(x_1066);
lean_dec_ref(x_1017);
x_24 = x_1037;
x_25 = x_1043;
x_26 = x_1051;
x_27 = x_1040;
x_28 = x_1039;
x_29 = x_1045;
x_30 = x_1042;
x_31 = x_1029;
x_32 = x_1066;
x_33 = x_1046;
x_34 = x_1038;
x_35 = lean_box(0);
x_36 = x_1044;
x_37 = x_1041;
goto block_45;
}
}
else
{
lean_object* x_1067; 
lean_dec(x_1021);
lean_dec(x_1020);
lean_dec_ref(x_1014);
x_1067 = lean_ctor_get(x_1017, 0);
lean_inc(x_1067);
lean_dec_ref(x_1017);
x_24 = x_1037;
x_25 = x_1043;
x_26 = x_1051;
x_27 = x_1040;
x_28 = x_1039;
x_29 = x_1045;
x_30 = x_1042;
x_31 = x_1029;
x_32 = x_1067;
x_33 = x_1046;
x_34 = x_1038;
x_35 = lean_box(0);
x_36 = x_1044;
x_37 = x_1041;
goto block_45;
}
}
}
else
{
lean_dec(x_1046);
lean_dec_ref(x_1045);
lean_dec(x_1044);
lean_dec_ref(x_1043);
lean_dec(x_1042);
lean_dec_ref(x_1041);
lean_dec(x_1040);
lean_dec_ref(x_1039);
lean_dec(x_1038);
lean_dec(x_1037);
lean_dec(x_1032);
lean_dec(x_1021);
lean_dec(x_1020);
lean_dec(x_1017);
lean_dec(x_1014);
x_13 = x_1051;
x_14 = lean_box(0);
goto block_17;
}
}
else
{
lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; 
lean_dec(x_1046);
lean_dec_ref(x_1045);
lean_dec(x_1044);
lean_dec_ref(x_1043);
lean_dec(x_1042);
lean_dec_ref(x_1041);
lean_dec(x_1040);
lean_dec_ref(x_1039);
lean_dec(x_1038);
lean_dec(x_1037);
lean_dec(x_1032);
lean_dec(x_1021);
lean_dec(x_1020);
lean_dec(x_1017);
lean_dec(x_1014);
x_1068 = lean_ctor_get(x_1062, 0);
lean_inc(x_1068);
if (lean_is_exclusive(x_1062)) {
 lean_ctor_release(x_1062, 0);
 x_1069 = x_1062;
} else {
 lean_dec_ref(x_1062);
 x_1069 = lean_box(0);
}
if (lean_is_scalar(x_1069)) {
 x_1070 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1070 = x_1069;
}
lean_ctor_set(x_1070, 0, x_1068);
return x_1070;
}
}
else
{
lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; 
lean_dec(x_1046);
lean_dec_ref(x_1045);
lean_dec(x_1044);
lean_dec_ref(x_1043);
lean_dec(x_1042);
lean_dec_ref(x_1041);
lean_dec(x_1040);
lean_dec_ref(x_1039);
lean_dec(x_1038);
lean_dec(x_1037);
lean_dec(x_1036);
lean_dec_ref(x_1035);
lean_dec_ref(x_1034);
lean_dec_ref(x_1033);
lean_dec(x_1032);
lean_dec(x_1031);
lean_dec(x_1030);
lean_dec_ref(x_1028);
lean_dec(x_1027);
lean_dec_ref(x_1026);
lean_dec(x_1025);
lean_dec_ref(x_1024);
lean_dec(x_1023);
lean_dec(x_1022);
lean_dec(x_1021);
lean_dec(x_1020);
lean_dec(x_1019);
lean_dec(x_1018);
lean_dec(x_1017);
lean_dec(x_1016);
lean_dec_ref(x_1015);
lean_dec(x_1014);
lean_dec(x_1013);
lean_dec_ref(x_1012);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1002);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1071 = lean_ctor_get(x_1048, 0);
lean_inc(x_1071);
if (lean_is_exclusive(x_1048)) {
 lean_ctor_release(x_1048, 0);
 x_1072 = x_1048;
} else {
 lean_dec_ref(x_1048);
 x_1072 = lean_box(0);
}
if (lean_is_scalar(x_1072)) {
 x_1073 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1073 = x_1072;
}
lean_ctor_set(x_1073, 0, x_1071);
return x_1073;
}
}
block_1136:
{
lean_object* x_1110; 
lean_inc(x_1108);
lean_inc_ref(x_1107);
lean_inc(x_1106);
lean_inc_ref(x_1105);
lean_inc(x_1104);
lean_inc_ref(x_1103);
lean_inc(x_1102);
lean_inc_ref(x_1101);
lean_inc(x_1100);
lean_inc(x_1099);
lean_inc_ref(x_1);
lean_inc(x_999);
x_1110 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f(x_999, x_1, x_1099, x_1100, x_1101, x_1102, x_1103, x_1104, x_1105, x_1106, x_1107, x_1108);
if (lean_obj_tag(x_1110) == 0)
{
lean_object* x_1111; lean_object* x_1112; 
x_1111 = lean_ctor_get(x_1110, 0);
lean_inc(x_1111);
lean_dec_ref(x_1110);
lean_inc(x_1108);
lean_inc_ref(x_1107);
lean_inc(x_1106);
lean_inc_ref(x_1105);
lean_inc(x_1104);
lean_inc_ref(x_1103);
lean_inc(x_1102);
lean_inc_ref(x_1101);
lean_inc(x_1100);
lean_inc(x_1099);
lean_inc_ref(x_1);
lean_inc(x_999);
x_1112 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f(x_999, x_1, x_1099, x_1100, x_1101, x_1102, x_1103, x_1104, x_1105, x_1106, x_1107, x_1108);
if (lean_obj_tag(x_1112) == 0)
{
if (lean_obj_tag(x_1081) == 0)
{
lean_object* x_1113; 
lean_dec(x_1090);
lean_dec(x_1000);
x_1113 = lean_ctor_get(x_1112, 0);
lean_inc(x_1113);
lean_dec_ref(x_1112);
x_1012 = x_1076;
x_1013 = x_1077;
x_1014 = x_1078;
x_1015 = x_1079;
x_1016 = x_1113;
x_1017 = x_1080;
x_1018 = x_1111;
x_1019 = x_1081;
x_1020 = x_1082;
x_1021 = x_1083;
x_1022 = x_1098;
x_1023 = x_1084;
x_1024 = x_1085;
x_1025 = x_1086;
x_1026 = x_1087;
x_1027 = x_1088;
x_1028 = x_1089;
x_1029 = x_1092;
x_1030 = x_1091;
x_1031 = x_1093;
x_1032 = x_1094;
x_1033 = x_1096;
x_1034 = x_1095;
x_1035 = x_1097;
x_1036 = x_1075;
x_1037 = x_1099;
x_1038 = x_1100;
x_1039 = x_1101;
x_1040 = x_1102;
x_1041 = x_1103;
x_1042 = x_1104;
x_1043 = x_1105;
x_1044 = x_1106;
x_1045 = x_1107;
x_1046 = x_1108;
x_1047 = lean_box(0);
goto block_1074;
}
else
{
lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; 
lean_dec(x_1075);
x_1114 = lean_ctor_get(x_1112, 0);
lean_inc(x_1114);
lean_dec_ref(x_1112);
x_1115 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__9));
lean_inc(x_1108);
lean_inc_ref(x_1107);
lean_inc(x_1106);
lean_inc_ref(x_1105);
lean_inc_ref(x_1);
lean_inc(x_999);
x_1116 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(x_1115, x_999, x_1, x_1099, x_1100, x_1101, x_1102, x_1103, x_1104, x_1105, x_1106, x_1107, x_1108);
if (lean_obj_tag(x_1116) == 0)
{
lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; 
x_1117 = lean_ctor_get(x_1116, 0);
lean_inc(x_1117);
lean_dec_ref(x_1116);
x_1118 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__11));
x_1119 = l_Lean_mkConst(x_1118, x_1090);
lean_inc_ref_n(x_1, 3);
x_1120 = l_Lean_mkApp4(x_1119, x_1, x_1, x_1, x_1117);
lean_inc(x_1108);
lean_inc_ref(x_1107);
lean_inc(x_1106);
lean_inc_ref(x_1105);
lean_inc(x_1104);
lean_inc_ref(x_1103);
lean_inc(x_1102);
lean_inc_ref(x_1101);
lean_inc(x_1100);
lean_inc(x_1099);
x_1121 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_1120, x_1099, x_1100, x_1101, x_1102, x_1103, x_1104, x_1105, x_1106, x_1107, x_1108);
if (lean_obj_tag(x_1121) == 0)
{
lean_object* x_1122; lean_object* x_1123; 
x_1122 = lean_ctor_get(x_1121, 0);
lean_inc(x_1122);
lean_dec_ref(x_1121);
if (lean_is_scalar(x_1000)) {
 x_1123 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1123 = x_1000;
}
lean_ctor_set(x_1123, 0, x_1122);
x_1012 = x_1076;
x_1013 = x_1077;
x_1014 = x_1078;
x_1015 = x_1079;
x_1016 = x_1114;
x_1017 = x_1080;
x_1018 = x_1111;
x_1019 = x_1081;
x_1020 = x_1082;
x_1021 = x_1083;
x_1022 = x_1098;
x_1023 = x_1084;
x_1024 = x_1085;
x_1025 = x_1086;
x_1026 = x_1087;
x_1027 = x_1088;
x_1028 = x_1089;
x_1029 = x_1092;
x_1030 = x_1091;
x_1031 = x_1093;
x_1032 = x_1094;
x_1033 = x_1096;
x_1034 = x_1095;
x_1035 = x_1097;
x_1036 = x_1123;
x_1037 = x_1099;
x_1038 = x_1100;
x_1039 = x_1101;
x_1040 = x_1102;
x_1041 = x_1103;
x_1042 = x_1104;
x_1043 = x_1105;
x_1044 = x_1106;
x_1045 = x_1107;
x_1046 = x_1108;
x_1047 = lean_box(0);
goto block_1074;
}
else
{
lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; 
lean_dec(x_1114);
lean_dec(x_1111);
lean_dec(x_1108);
lean_dec_ref(x_1107);
lean_dec(x_1106);
lean_dec_ref(x_1105);
lean_dec(x_1104);
lean_dec_ref(x_1103);
lean_dec(x_1102);
lean_dec_ref(x_1101);
lean_dec(x_1100);
lean_dec(x_1099);
lean_dec(x_1098);
lean_dec_ref(x_1097);
lean_dec_ref(x_1096);
lean_dec_ref(x_1095);
lean_dec(x_1094);
lean_dec(x_1093);
lean_dec(x_1091);
lean_dec_ref(x_1089);
lean_dec(x_1088);
lean_dec_ref(x_1087);
lean_dec(x_1086);
lean_dec_ref(x_1085);
lean_dec(x_1084);
lean_dec(x_1083);
lean_dec(x_1082);
lean_dec_ref(x_1081);
lean_dec(x_1080);
lean_dec_ref(x_1079);
lean_dec(x_1078);
lean_dec(x_1077);
lean_dec_ref(x_1076);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1124 = lean_ctor_get(x_1121, 0);
lean_inc(x_1124);
if (lean_is_exclusive(x_1121)) {
 lean_ctor_release(x_1121, 0);
 x_1125 = x_1121;
} else {
 lean_dec_ref(x_1121);
 x_1125 = lean_box(0);
}
if (lean_is_scalar(x_1125)) {
 x_1126 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1126 = x_1125;
}
lean_ctor_set(x_1126, 0, x_1124);
return x_1126;
}
}
else
{
lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; 
lean_dec(x_1114);
lean_dec(x_1111);
lean_dec(x_1108);
lean_dec_ref(x_1107);
lean_dec(x_1106);
lean_dec_ref(x_1105);
lean_dec(x_1104);
lean_dec_ref(x_1103);
lean_dec(x_1102);
lean_dec_ref(x_1101);
lean_dec(x_1100);
lean_dec(x_1099);
lean_dec(x_1098);
lean_dec_ref(x_1097);
lean_dec_ref(x_1096);
lean_dec_ref(x_1095);
lean_dec(x_1094);
lean_dec(x_1093);
lean_dec(x_1091);
lean_dec(x_1090);
lean_dec_ref(x_1089);
lean_dec(x_1088);
lean_dec_ref(x_1087);
lean_dec(x_1086);
lean_dec_ref(x_1085);
lean_dec(x_1084);
lean_dec(x_1083);
lean_dec(x_1082);
lean_dec_ref(x_1081);
lean_dec(x_1080);
lean_dec_ref(x_1079);
lean_dec(x_1078);
lean_dec(x_1077);
lean_dec_ref(x_1076);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1127 = lean_ctor_get(x_1116, 0);
lean_inc(x_1127);
if (lean_is_exclusive(x_1116)) {
 lean_ctor_release(x_1116, 0);
 x_1128 = x_1116;
} else {
 lean_dec_ref(x_1116);
 x_1128 = lean_box(0);
}
if (lean_is_scalar(x_1128)) {
 x_1129 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1129 = x_1128;
}
lean_ctor_set(x_1129, 0, x_1127);
return x_1129;
}
}
}
else
{
lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; 
lean_dec(x_1111);
lean_dec(x_1108);
lean_dec_ref(x_1107);
lean_dec(x_1106);
lean_dec_ref(x_1105);
lean_dec(x_1104);
lean_dec_ref(x_1103);
lean_dec(x_1102);
lean_dec_ref(x_1101);
lean_dec(x_1100);
lean_dec(x_1099);
lean_dec(x_1098);
lean_dec_ref(x_1097);
lean_dec_ref(x_1096);
lean_dec_ref(x_1095);
lean_dec(x_1094);
lean_dec(x_1093);
lean_dec(x_1091);
lean_dec(x_1090);
lean_dec_ref(x_1089);
lean_dec(x_1088);
lean_dec_ref(x_1087);
lean_dec(x_1086);
lean_dec_ref(x_1085);
lean_dec(x_1084);
lean_dec(x_1083);
lean_dec(x_1082);
lean_dec(x_1081);
lean_dec(x_1080);
lean_dec_ref(x_1079);
lean_dec(x_1078);
lean_dec(x_1077);
lean_dec_ref(x_1076);
lean_dec(x_1075);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1130 = lean_ctor_get(x_1112, 0);
lean_inc(x_1130);
if (lean_is_exclusive(x_1112)) {
 lean_ctor_release(x_1112, 0);
 x_1131 = x_1112;
} else {
 lean_dec_ref(x_1112);
 x_1131 = lean_box(0);
}
if (lean_is_scalar(x_1131)) {
 x_1132 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1132 = x_1131;
}
lean_ctor_set(x_1132, 0, x_1130);
return x_1132;
}
}
else
{
lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; 
lean_dec(x_1108);
lean_dec_ref(x_1107);
lean_dec(x_1106);
lean_dec_ref(x_1105);
lean_dec(x_1104);
lean_dec_ref(x_1103);
lean_dec(x_1102);
lean_dec_ref(x_1101);
lean_dec(x_1100);
lean_dec(x_1099);
lean_dec(x_1098);
lean_dec_ref(x_1097);
lean_dec_ref(x_1096);
lean_dec_ref(x_1095);
lean_dec(x_1094);
lean_dec(x_1093);
lean_dec(x_1091);
lean_dec(x_1090);
lean_dec_ref(x_1089);
lean_dec(x_1088);
lean_dec_ref(x_1087);
lean_dec(x_1086);
lean_dec_ref(x_1085);
lean_dec(x_1084);
lean_dec(x_1083);
lean_dec(x_1082);
lean_dec(x_1081);
lean_dec(x_1080);
lean_dec_ref(x_1079);
lean_dec(x_1078);
lean_dec(x_1077);
lean_dec_ref(x_1076);
lean_dec(x_1075);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1133 = lean_ctor_get(x_1110, 0);
lean_inc(x_1133);
if (lean_is_exclusive(x_1110)) {
 lean_ctor_release(x_1110, 0);
 x_1134 = x_1110;
} else {
 lean_dec_ref(x_1110);
 x_1134 = lean_box(0);
}
if (lean_is_scalar(x_1134)) {
 x_1135 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1135 = x_1134;
}
lean_ctor_set(x_1135, 0, x_1133);
return x_1135;
}
}
block_1182:
{
if (lean_obj_tag(x_1009) == 1)
{
lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; 
x_1172 = lean_ctor_get(x_1009, 0);
x_1173 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__13));
x_1174 = l_Lean_mkConst(x_1173, x_1150);
lean_inc(x_1172);
lean_inc_ref(x_1);
x_1175 = l_Lean_mkAppB(x_1174, x_1, x_1172);
lean_inc(x_1170);
lean_inc_ref(x_1169);
lean_inc(x_1168);
lean_inc_ref(x_1167);
lean_inc(x_1166);
lean_inc_ref(x_1165);
lean_inc(x_1164);
lean_inc_ref(x_1163);
lean_inc(x_1162);
lean_inc(x_1161);
x_1176 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_1175, x_1161, x_1162, x_1163, x_1164, x_1165, x_1166, x_1167, x_1168, x_1169, x_1170);
if (lean_obj_tag(x_1176) == 0)
{
lean_object* x_1177; lean_object* x_1178; 
x_1177 = lean_ctor_get(x_1176, 0);
lean_inc(x_1177);
lean_dec_ref(x_1176);
if (lean_is_scalar(x_1003)) {
 x_1178 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1178 = x_1003;
 lean_ctor_set_tag(x_1178, 1);
}
lean_ctor_set(x_1178, 0, x_1177);
x_1075 = x_1137;
x_1076 = x_1138;
x_1077 = x_1139;
x_1078 = x_1140;
x_1079 = x_1141;
x_1080 = x_1142;
x_1081 = x_1143;
x_1082 = x_1144;
x_1083 = x_1145;
x_1084 = x_1160;
x_1085 = x_1146;
x_1086 = x_1147;
x_1087 = x_1148;
x_1088 = x_1149;
x_1089 = x_1151;
x_1090 = x_1152;
x_1091 = x_1154;
x_1092 = x_1153;
x_1093 = x_1155;
x_1094 = x_1156;
x_1095 = x_1158;
x_1096 = x_1157;
x_1097 = x_1159;
x_1098 = x_1178;
x_1099 = x_1161;
x_1100 = x_1162;
x_1101 = x_1163;
x_1102 = x_1164;
x_1103 = x_1165;
x_1104 = x_1166;
x_1105 = x_1167;
x_1106 = x_1168;
x_1107 = x_1169;
x_1108 = x_1170;
x_1109 = lean_box(0);
goto block_1136;
}
else
{
lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; 
lean_dec(x_1170);
lean_dec_ref(x_1169);
lean_dec(x_1168);
lean_dec_ref(x_1167);
lean_dec(x_1166);
lean_dec_ref(x_1165);
lean_dec(x_1164);
lean_dec_ref(x_1163);
lean_dec(x_1162);
lean_dec(x_1161);
lean_dec(x_1160);
lean_dec_ref(x_1159);
lean_dec_ref(x_1158);
lean_dec_ref(x_1157);
lean_dec(x_1156);
lean_dec(x_1155);
lean_dec(x_1154);
lean_dec(x_1152);
lean_dec_ref(x_1151);
lean_dec(x_1149);
lean_dec_ref(x_1148);
lean_dec(x_1147);
lean_dec_ref(x_1146);
lean_dec(x_1145);
lean_dec(x_1144);
lean_dec(x_1143);
lean_dec(x_1142);
lean_dec_ref(x_1141);
lean_dec(x_1140);
lean_dec(x_1139);
lean_dec_ref(x_1138);
lean_dec(x_1137);
lean_dec(x_1011);
lean_dec_ref(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1179 = lean_ctor_get(x_1176, 0);
lean_inc(x_1179);
if (lean_is_exclusive(x_1176)) {
 lean_ctor_release(x_1176, 0);
 x_1180 = x_1176;
} else {
 lean_dec_ref(x_1176);
 x_1180 = lean_box(0);
}
if (lean_is_scalar(x_1180)) {
 x_1181 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1181 = x_1180;
}
lean_ctor_set(x_1181, 0, x_1179);
return x_1181;
}
}
else
{
lean_dec(x_1150);
lean_dec(x_1003);
lean_inc(x_1137);
x_1075 = x_1137;
x_1076 = x_1138;
x_1077 = x_1139;
x_1078 = x_1140;
x_1079 = x_1141;
x_1080 = x_1142;
x_1081 = x_1143;
x_1082 = x_1144;
x_1083 = x_1145;
x_1084 = x_1160;
x_1085 = x_1146;
x_1086 = x_1147;
x_1087 = x_1148;
x_1088 = x_1149;
x_1089 = x_1151;
x_1090 = x_1152;
x_1091 = x_1154;
x_1092 = x_1153;
x_1093 = x_1155;
x_1094 = x_1156;
x_1095 = x_1158;
x_1096 = x_1157;
x_1097 = x_1159;
x_1098 = x_1137;
x_1099 = x_1161;
x_1100 = x_1162;
x_1101 = x_1163;
x_1102 = x_1164;
x_1103 = x_1165;
x_1104 = x_1166;
x_1105 = x_1167;
x_1106 = x_1168;
x_1107 = x_1169;
x_1108 = x_1170;
x_1109 = lean_box(0);
goto block_1136;
}
}
block_1371:
{
lean_object* x_1216; 
lean_inc(x_1214);
lean_inc_ref(x_1213);
lean_inc(x_1212);
lean_inc_ref(x_1211);
lean_inc_ref(x_1);
lean_inc(x_999);
x_1216 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(x_999, x_1, x_1211, x_1212, x_1213, x_1214);
if (lean_obj_tag(x_1216) == 0)
{
lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; 
x_1217 = lean_ctor_get(x_1216, 0);
lean_inc(x_1217);
lean_dec_ref(x_1216);
x_1218 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__15));
lean_inc(x_1214);
lean_inc_ref(x_1213);
lean_inc(x_1212);
lean_inc_ref(x_1211);
lean_inc_ref(x_1);
lean_inc(x_999);
x_1219 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(x_1218, x_999, x_1, x_1205, x_1206, x_1207, x_1208, x_1209, x_1210, x_1211, x_1212, x_1213, x_1214);
if (lean_obj_tag(x_1219) == 0)
{
lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; 
x_1220 = lean_ctor_get(x_1219, 0);
lean_inc(x_1220);
lean_dec_ref(x_1219);
x_1221 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__17));
lean_inc(x_1196);
x_1222 = l_Lean_mkConst(x_1221, x_1196);
lean_inc(x_1220);
lean_inc_ref(x_1);
x_1223 = l_Lean_mkAppB(x_1222, x_1, x_1220);
lean_inc(x_1214);
lean_inc_ref(x_1213);
lean_inc(x_1212);
lean_inc_ref(x_1211);
lean_inc(x_1210);
lean_inc_ref(x_1209);
lean_inc(x_1208);
lean_inc_ref(x_1207);
lean_inc(x_1206);
lean_inc(x_1205);
x_1224 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(x_1223, x_1205, x_1206, x_1207, x_1208, x_1209, x_1210, x_1211, x_1212, x_1213, x_1214);
if (lean_obj_tag(x_1224) == 0)
{
lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; 
x_1225 = lean_ctor_get(x_1224, 0);
lean_inc(x_1225);
lean_dec_ref(x_1224);
x_1226 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__19));
lean_inc(x_1196);
x_1227 = l_Lean_mkConst(x_1226, x_1196);
x_1228 = lean_unsigned_to_nat(0u);
x_1229 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__20;
lean_inc_ref(x_1);
x_1230 = l_Lean_mkAppB(x_1227, x_1, x_1229);
lean_inc(x_1214);
lean_inc_ref(x_1213);
lean_inc(x_1212);
lean_inc_ref(x_1211);
x_1231 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_1230, x_1211, x_1212, x_1213, x_1214);
if (lean_obj_tag(x_1231) == 0)
{
lean_object* x_1232; lean_object* x_1233; 
x_1232 = lean_ctor_get(x_1231, 0);
lean_inc(x_1232);
if (lean_is_exclusive(x_1231)) {
 lean_ctor_release(x_1231, 0);
 x_1233 = x_1231;
} else {
 lean_dec_ref(x_1231);
 x_1233 = lean_box(0);
}
if (lean_obj_tag(x_1232) == 1)
{
lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; 
lean_dec(x_1233);
x_1234 = lean_ctor_get(x_1232, 0);
lean_inc(x_1234);
if (lean_is_exclusive(x_1232)) {
 lean_ctor_release(x_1232, 0);
 x_1235 = x_1232;
} else {
 lean_dec_ref(x_1232);
 x_1235 = lean_box(0);
}
x_1236 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__22));
lean_inc(x_1196);
x_1237 = l_Lean_mkConst(x_1236, x_1196);
lean_inc_ref(x_1);
x_1238 = l_Lean_mkApp3(x_1237, x_1, x_1229, x_1234);
lean_inc(x_1214);
lean_inc_ref(x_1213);
lean_inc(x_1212);
lean_inc_ref(x_1211);
lean_inc(x_1210);
lean_inc_ref(x_1209);
lean_inc(x_1208);
lean_inc_ref(x_1207);
lean_inc(x_1206);
lean_inc(x_1205);
x_1239 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_1238, x_1205, x_1206, x_1207, x_1208, x_1209, x_1210, x_1211, x_1212, x_1213, x_1214);
if (lean_obj_tag(x_1239) == 0)
{
lean_object* x_1240; lean_object* x_1241; 
x_1240 = lean_ctor_get(x_1239, 0);
lean_inc(x_1240);
lean_dec_ref(x_1239);
lean_inc(x_1214);
lean_inc_ref(x_1213);
lean_inc(x_1212);
lean_inc_ref(x_1211);
lean_inc(x_1240);
lean_inc(x_1225);
x_1241 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(x_1225, x_1240, x_1211, x_1212, x_1213, x_1214);
if (lean_obj_tag(x_1241) == 0)
{
lean_object* x_1242; lean_object* x_1243; 
lean_dec_ref(x_1241);
x_1242 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__24));
lean_inc(x_1214);
lean_inc_ref(x_1213);
lean_inc(x_1212);
lean_inc_ref(x_1211);
lean_inc_ref(x_1);
lean_inc(x_999);
x_1243 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(x_1242, x_999, x_1, x_1205, x_1206, x_1207, x_1208, x_1209, x_1210, x_1211, x_1212, x_1213, x_1214);
if (lean_obj_tag(x_1243) == 0)
{
lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; 
x_1244 = lean_ctor_get(x_1243, 0);
lean_inc(x_1244);
lean_dec_ref(x_1243);
x_1245 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__26));
lean_inc(x_1198);
x_1246 = l_Lean_mkConst(x_1245, x_1198);
lean_inc(x_1244);
lean_inc_ref_n(x_1, 3);
x_1247 = l_Lean_mkApp4(x_1246, x_1, x_1, x_1, x_1244);
lean_inc(x_1214);
lean_inc_ref(x_1213);
lean_inc(x_1212);
lean_inc_ref(x_1211);
lean_inc(x_1210);
lean_inc_ref(x_1209);
lean_inc(x_1208);
lean_inc_ref(x_1207);
lean_inc(x_1206);
lean_inc(x_1205);
x_1248 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_1247, x_1205, x_1206, x_1207, x_1208, x_1209, x_1210, x_1211, x_1212, x_1213, x_1214);
if (lean_obj_tag(x_1248) == 0)
{
lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; 
x_1249 = lean_ctor_get(x_1248, 0);
lean_inc(x_1249);
lean_dec_ref(x_1248);
x_1250 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__28));
lean_inc(x_1214);
lean_inc_ref(x_1213);
lean_inc(x_1212);
lean_inc_ref(x_1211);
lean_inc_ref(x_1);
lean_inc(x_999);
x_1251 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(x_1250, x_999, x_1, x_1205, x_1206, x_1207, x_1208, x_1209, x_1210, x_1211, x_1212, x_1213, x_1214);
if (lean_obj_tag(x_1251) == 0)
{
lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; 
x_1252 = lean_ctor_get(x_1251, 0);
lean_inc(x_1252);
lean_dec_ref(x_1251);
x_1253 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__30));
lean_inc(x_1196);
x_1254 = l_Lean_mkConst(x_1253, x_1196);
lean_inc(x_1252);
lean_inc_ref(x_1);
x_1255 = l_Lean_mkAppB(x_1254, x_1, x_1252);
lean_inc(x_1214);
lean_inc_ref(x_1213);
lean_inc(x_1212);
lean_inc_ref(x_1211);
lean_inc(x_1210);
lean_inc_ref(x_1209);
lean_inc(x_1208);
lean_inc_ref(x_1207);
lean_inc(x_1206);
lean_inc(x_1205);
x_1256 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_1255, x_1205, x_1206, x_1207, x_1208, x_1209, x_1210, x_1211, x_1212, x_1213, x_1214);
if (lean_obj_tag(x_1256) == 0)
{
lean_object* x_1257; lean_object* x_1258; 
x_1257 = lean_ctor_get(x_1256, 0);
lean_inc(x_1257);
lean_dec_ref(x_1256);
lean_inc(x_1214);
lean_inc_ref(x_1213);
lean_inc(x_1212);
lean_inc_ref(x_1211);
lean_inc_ref(x_1);
lean_inc(x_999);
x_1258 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(x_999, x_1, x_1205, x_1206, x_1207, x_1208, x_1209, x_1210, x_1211, x_1212, x_1213, x_1214);
if (lean_obj_tag(x_1258) == 0)
{
lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; 
x_1259 = lean_ctor_get(x_1258, 0);
lean_inc(x_1259);
lean_dec_ref(x_1258);
x_1260 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__1));
x_1261 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2;
x_1262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1262, 0, x_1261);
lean_ctor_set(x_1262, 1, x_1200);
x_1263 = l_Lean_mkConst(x_1260, x_1262);
x_1264 = l_Lean_Int_mkType;
lean_inc(x_1259);
lean_inc_ref_n(x_1, 2);
lean_inc_ref(x_1263);
x_1265 = l_Lean_mkApp4(x_1263, x_1264, x_1, x_1, x_1259);
lean_inc(x_1214);
lean_inc_ref(x_1213);
lean_inc(x_1212);
lean_inc_ref(x_1211);
lean_inc(x_1210);
lean_inc_ref(x_1209);
lean_inc(x_1208);
lean_inc_ref(x_1207);
lean_inc(x_1206);
lean_inc(x_1205);
x_1266 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_1265, x_1205, x_1206, x_1207, x_1208, x_1209, x_1210, x_1211, x_1212, x_1213, x_1214);
if (lean_obj_tag(x_1266) == 0)
{
lean_object* x_1267; lean_object* x_1268; 
x_1267 = lean_ctor_get(x_1266, 0);
lean_inc(x_1267);
lean_dec_ref(x_1266);
lean_inc(x_1214);
lean_inc_ref(x_1213);
lean_inc(x_1212);
lean_inc_ref(x_1211);
lean_inc_ref(x_1);
lean_inc(x_999);
x_1268 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(x_999, x_1, x_1205, x_1206, x_1207, x_1208, x_1209, x_1210, x_1211, x_1212, x_1213, x_1214);
if (lean_obj_tag(x_1268) == 0)
{
lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; 
x_1269 = lean_ctor_get(x_1268, 0);
lean_inc(x_1269);
lean_dec_ref(x_1268);
x_1270 = l_Lean_Nat_mkType;
lean_inc(x_1269);
lean_inc_ref_n(x_1, 2);
x_1271 = l_Lean_mkApp4(x_1263, x_1270, x_1, x_1, x_1269);
lean_inc(x_1214);
lean_inc_ref(x_1213);
lean_inc(x_1212);
lean_inc_ref(x_1211);
lean_inc(x_1210);
lean_inc_ref(x_1209);
lean_inc(x_1208);
lean_inc_ref(x_1207);
lean_inc(x_1206);
lean_inc(x_1205);
x_1272 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_1271, x_1205, x_1206, x_1207, x_1208, x_1209, x_1210, x_1211, x_1212, x_1213, x_1214);
if (lean_obj_tag(x_1272) == 0)
{
lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; 
x_1273 = lean_ctor_get(x_1272, 0);
lean_inc(x_1273);
lean_dec_ref(x_1272);
x_1274 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__31));
x_1275 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__32));
lean_inc_ref(x_1189);
lean_inc_ref(x_1188);
x_1276 = l_Lean_Name_mkStr4(x_1188, x_1189, x_1274, x_1275);
lean_inc(x_1214);
lean_inc_ref(x_1213);
lean_inc(x_1212);
lean_inc_ref(x_1211);
lean_inc_ref(x_1);
lean_inc(x_999);
lean_inc_ref(x_1190);
x_1277 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(x_1220, x_1190, x_1276, x_999, x_1, x_1211, x_1212, x_1213, x_1214);
if (lean_obj_tag(x_1277) == 0)
{
lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; 
lean_dec_ref(x_1277);
x_1278 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__33));
lean_inc_ref(x_1189);
lean_inc_ref(x_1188);
x_1279 = l_Lean_Name_mkStr4(x_1188, x_1189, x_1274, x_1278);
x_1280 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__35));
x_1281 = lean_box(0);
lean_inc(x_1214);
lean_inc_ref(x_1213);
lean_inc(x_1212);
lean_inc_ref(x_1211);
lean_inc_ref(x_1);
lean_inc(x_999);
x_1282 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(x_1197, x_1190, x_1279, x_1280, x_999, x_1, x_1281, x_1211, x_1212, x_1213, x_1214);
if (lean_obj_tag(x_1282) == 0)
{
lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; 
lean_dec_ref(x_1282);
x_1283 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__36));
lean_inc_ref(x_1194);
lean_inc_ref(x_1189);
lean_inc_ref(x_1188);
x_1284 = l_Lean_Name_mkStr4(x_1188, x_1189, x_1194, x_1283);
x_1285 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__38));
lean_inc(x_1214);
lean_inc_ref(x_1213);
lean_inc(x_1212);
lean_inc_ref(x_1211);
lean_inc_ref(x_1);
lean_inc(x_999);
lean_inc_ref(x_1201);
x_1286 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(x_1244, x_1201, x_1284, x_1285, x_999, x_1, x_1281, x_1211, x_1212, x_1213, x_1214);
if (lean_obj_tag(x_1286) == 0)
{
lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; 
lean_dec_ref(x_1286);
x_1287 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__39));
lean_inc_ref(x_1189);
lean_inc_ref(x_1188);
x_1288 = l_Lean_Name_mkStr4(x_1188, x_1189, x_1194, x_1287);
lean_inc(x_1214);
lean_inc_ref(x_1213);
lean_inc(x_1212);
lean_inc_ref(x_1211);
lean_inc_ref(x_1);
lean_inc(x_999);
x_1289 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(x_1252, x_1201, x_1288, x_999, x_1, x_1211, x_1212, x_1213, x_1214);
if (lean_obj_tag(x_1289) == 0)
{
lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; 
lean_dec_ref(x_1289);
x_1290 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__40));
lean_inc_ref(x_1185);
lean_inc_ref(x_1189);
lean_inc_ref(x_1188);
x_1291 = l_Lean_Name_mkStr4(x_1188, x_1189, x_1185, x_1290);
x_1292 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__42));
x_1293 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__43;
lean_inc(x_1214);
lean_inc_ref(x_1213);
lean_inc(x_1212);
lean_inc_ref(x_1211);
lean_inc_ref(x_1);
lean_inc(x_999);
lean_inc_ref(x_1192);
x_1294 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(x_1259, x_1192, x_1291, x_1292, x_999, x_1, x_1293, x_1211, x_1212, x_1213, x_1214);
if (lean_obj_tag(x_1294) == 0)
{
lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; 
lean_dec_ref(x_1294);
x_1295 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__44));
x_1296 = l_Lean_Name_mkStr4(x_1188, x_1189, x_1185, x_1295);
x_1297 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__45;
lean_inc(x_1214);
lean_inc_ref(x_1213);
lean_inc(x_1212);
lean_inc_ref(x_1211);
lean_inc_ref(x_1);
lean_inc(x_999);
lean_inc_ref(x_1192);
x_1298 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(x_1269, x_1192, x_1296, x_1292, x_999, x_1, x_1297, x_1211, x_1212, x_1213, x_1214);
if (lean_obj_tag(x_1298) == 0)
{
lean_dec_ref(x_1298);
if (lean_obj_tag(x_1006) == 1)
{
lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; 
x_1299 = lean_ctor_get(x_1006, 0);
x_1300 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__47));
lean_inc(x_1196);
x_1301 = l_Lean_mkConst(x_1300, x_1196);
lean_inc(x_1299);
lean_inc_ref(x_1);
x_1302 = l_Lean_mkAppB(x_1301, x_1, x_1299);
lean_inc(x_1214);
lean_inc_ref(x_1213);
lean_inc(x_1212);
lean_inc_ref(x_1211);
lean_inc(x_1210);
lean_inc_ref(x_1209);
lean_inc(x_1208);
lean_inc_ref(x_1207);
lean_inc(x_1206);
lean_inc(x_1205);
x_1303 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_1302, x_1205, x_1206, x_1207, x_1208, x_1209, x_1210, x_1211, x_1212, x_1213, x_1214);
if (lean_obj_tag(x_1303) == 0)
{
lean_object* x_1304; lean_object* x_1305; 
x_1304 = lean_ctor_get(x_1303, 0);
lean_inc(x_1304);
lean_dec_ref(x_1303);
if (lean_is_scalar(x_1235)) {
 x_1305 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1305 = x_1235;
}
lean_ctor_set(x_1305, 0, x_1304);
x_1137 = x_1281;
x_1138 = x_1267;
x_1139 = x_1228;
x_1140 = x_1183;
x_1141 = x_1249;
x_1142 = x_1184;
x_1143 = x_1186;
x_1144 = x_1187;
x_1145 = x_1204;
x_1146 = x_1273;
x_1147 = x_1191;
x_1148 = x_1192;
x_1149 = x_1193;
x_1150 = x_1196;
x_1151 = x_1195;
x_1152 = x_1198;
x_1153 = x_1199;
x_1154 = x_1217;
x_1155 = x_1202;
x_1156 = x_1203;
x_1157 = x_1257;
x_1158 = x_1240;
x_1159 = x_1225;
x_1160 = x_1305;
x_1161 = x_1205;
x_1162 = x_1206;
x_1163 = x_1207;
x_1164 = x_1208;
x_1165 = x_1209;
x_1166 = x_1210;
x_1167 = x_1211;
x_1168 = x_1212;
x_1169 = x_1213;
x_1170 = x_1214;
x_1171 = lean_box(0);
goto block_1182;
}
else
{
lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; 
lean_dec(x_1273);
lean_dec(x_1267);
lean_dec(x_1257);
lean_dec(x_1249);
lean_dec(x_1240);
lean_dec(x_1235);
lean_dec(x_1225);
lean_dec(x_1217);
lean_dec(x_1214);
lean_dec_ref(x_1213);
lean_dec(x_1212);
lean_dec_ref(x_1211);
lean_dec(x_1210);
lean_dec_ref(x_1209);
lean_dec(x_1208);
lean_dec_ref(x_1207);
lean_dec(x_1206);
lean_dec(x_1205);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec(x_1198);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec(x_1193);
lean_dec_ref(x_1192);
lean_dec(x_1191);
lean_dec(x_1187);
lean_dec(x_1186);
lean_dec(x_1184);
lean_dec(x_1183);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec_ref(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1306 = lean_ctor_get(x_1303, 0);
lean_inc(x_1306);
if (lean_is_exclusive(x_1303)) {
 lean_ctor_release(x_1303, 0);
 x_1307 = x_1303;
} else {
 lean_dec_ref(x_1303);
 x_1307 = lean_box(0);
}
if (lean_is_scalar(x_1307)) {
 x_1308 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1308 = x_1307;
}
lean_ctor_set(x_1308, 0, x_1306);
return x_1308;
}
}
else
{
lean_dec(x_1235);
x_1137 = x_1281;
x_1138 = x_1267;
x_1139 = x_1228;
x_1140 = x_1183;
x_1141 = x_1249;
x_1142 = x_1184;
x_1143 = x_1186;
x_1144 = x_1187;
x_1145 = x_1204;
x_1146 = x_1273;
x_1147 = x_1191;
x_1148 = x_1192;
x_1149 = x_1193;
x_1150 = x_1196;
x_1151 = x_1195;
x_1152 = x_1198;
x_1153 = x_1199;
x_1154 = x_1217;
x_1155 = x_1202;
x_1156 = x_1203;
x_1157 = x_1257;
x_1158 = x_1240;
x_1159 = x_1225;
x_1160 = x_1281;
x_1161 = x_1205;
x_1162 = x_1206;
x_1163 = x_1207;
x_1164 = x_1208;
x_1165 = x_1209;
x_1166 = x_1210;
x_1167 = x_1211;
x_1168 = x_1212;
x_1169 = x_1213;
x_1170 = x_1214;
x_1171 = lean_box(0);
goto block_1182;
}
}
else
{
lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; 
lean_dec(x_1273);
lean_dec(x_1267);
lean_dec(x_1257);
lean_dec(x_1249);
lean_dec(x_1240);
lean_dec(x_1235);
lean_dec(x_1225);
lean_dec(x_1217);
lean_dec(x_1214);
lean_dec_ref(x_1213);
lean_dec(x_1212);
lean_dec_ref(x_1211);
lean_dec(x_1210);
lean_dec_ref(x_1209);
lean_dec(x_1208);
lean_dec_ref(x_1207);
lean_dec(x_1206);
lean_dec(x_1205);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec(x_1198);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec(x_1193);
lean_dec_ref(x_1192);
lean_dec(x_1191);
lean_dec(x_1187);
lean_dec(x_1186);
lean_dec(x_1184);
lean_dec(x_1183);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1309 = lean_ctor_get(x_1298, 0);
lean_inc(x_1309);
if (lean_is_exclusive(x_1298)) {
 lean_ctor_release(x_1298, 0);
 x_1310 = x_1298;
} else {
 lean_dec_ref(x_1298);
 x_1310 = lean_box(0);
}
if (lean_is_scalar(x_1310)) {
 x_1311 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1311 = x_1310;
}
lean_ctor_set(x_1311, 0, x_1309);
return x_1311;
}
}
else
{
lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; 
lean_dec(x_1273);
lean_dec(x_1269);
lean_dec(x_1267);
lean_dec(x_1257);
lean_dec(x_1249);
lean_dec(x_1240);
lean_dec(x_1235);
lean_dec(x_1225);
lean_dec(x_1217);
lean_dec(x_1214);
lean_dec_ref(x_1213);
lean_dec(x_1212);
lean_dec_ref(x_1211);
lean_dec(x_1210);
lean_dec_ref(x_1209);
lean_dec(x_1208);
lean_dec_ref(x_1207);
lean_dec(x_1206);
lean_dec(x_1205);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec(x_1198);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec(x_1193);
lean_dec_ref(x_1192);
lean_dec(x_1191);
lean_dec_ref(x_1189);
lean_dec_ref(x_1188);
lean_dec(x_1187);
lean_dec(x_1186);
lean_dec_ref(x_1185);
lean_dec(x_1184);
lean_dec(x_1183);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1312 = lean_ctor_get(x_1294, 0);
lean_inc(x_1312);
if (lean_is_exclusive(x_1294)) {
 lean_ctor_release(x_1294, 0);
 x_1313 = x_1294;
} else {
 lean_dec_ref(x_1294);
 x_1313 = lean_box(0);
}
if (lean_is_scalar(x_1313)) {
 x_1314 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1314 = x_1313;
}
lean_ctor_set(x_1314, 0, x_1312);
return x_1314;
}
}
else
{
lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; 
lean_dec(x_1273);
lean_dec(x_1269);
lean_dec(x_1267);
lean_dec(x_1259);
lean_dec(x_1257);
lean_dec(x_1249);
lean_dec(x_1240);
lean_dec(x_1235);
lean_dec(x_1225);
lean_dec(x_1217);
lean_dec(x_1214);
lean_dec_ref(x_1213);
lean_dec(x_1212);
lean_dec_ref(x_1211);
lean_dec(x_1210);
lean_dec_ref(x_1209);
lean_dec(x_1208);
lean_dec_ref(x_1207);
lean_dec(x_1206);
lean_dec(x_1205);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec(x_1198);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec(x_1193);
lean_dec_ref(x_1192);
lean_dec(x_1191);
lean_dec_ref(x_1189);
lean_dec_ref(x_1188);
lean_dec(x_1187);
lean_dec(x_1186);
lean_dec_ref(x_1185);
lean_dec(x_1184);
lean_dec(x_1183);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1315 = lean_ctor_get(x_1289, 0);
lean_inc(x_1315);
if (lean_is_exclusive(x_1289)) {
 lean_ctor_release(x_1289, 0);
 x_1316 = x_1289;
} else {
 lean_dec_ref(x_1289);
 x_1316 = lean_box(0);
}
if (lean_is_scalar(x_1316)) {
 x_1317 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1317 = x_1316;
}
lean_ctor_set(x_1317, 0, x_1315);
return x_1317;
}
}
else
{
lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; 
lean_dec(x_1273);
lean_dec(x_1269);
lean_dec(x_1267);
lean_dec(x_1259);
lean_dec(x_1257);
lean_dec(x_1252);
lean_dec(x_1249);
lean_dec(x_1240);
lean_dec(x_1235);
lean_dec(x_1225);
lean_dec(x_1217);
lean_dec(x_1214);
lean_dec_ref(x_1213);
lean_dec(x_1212);
lean_dec_ref(x_1211);
lean_dec(x_1210);
lean_dec_ref(x_1209);
lean_dec(x_1208);
lean_dec_ref(x_1207);
lean_dec(x_1206);
lean_dec(x_1205);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec_ref(x_1201);
lean_dec(x_1198);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec_ref(x_1194);
lean_dec(x_1193);
lean_dec_ref(x_1192);
lean_dec(x_1191);
lean_dec_ref(x_1189);
lean_dec_ref(x_1188);
lean_dec(x_1187);
lean_dec(x_1186);
lean_dec_ref(x_1185);
lean_dec(x_1184);
lean_dec(x_1183);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1318 = lean_ctor_get(x_1286, 0);
lean_inc(x_1318);
if (lean_is_exclusive(x_1286)) {
 lean_ctor_release(x_1286, 0);
 x_1319 = x_1286;
} else {
 lean_dec_ref(x_1286);
 x_1319 = lean_box(0);
}
if (lean_is_scalar(x_1319)) {
 x_1320 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1320 = x_1319;
}
lean_ctor_set(x_1320, 0, x_1318);
return x_1320;
}
}
else
{
lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; 
lean_dec(x_1273);
lean_dec(x_1269);
lean_dec(x_1267);
lean_dec(x_1259);
lean_dec(x_1257);
lean_dec(x_1252);
lean_dec(x_1249);
lean_dec(x_1244);
lean_dec(x_1240);
lean_dec(x_1235);
lean_dec(x_1225);
lean_dec(x_1217);
lean_dec(x_1214);
lean_dec_ref(x_1213);
lean_dec(x_1212);
lean_dec_ref(x_1211);
lean_dec(x_1210);
lean_dec_ref(x_1209);
lean_dec(x_1208);
lean_dec_ref(x_1207);
lean_dec(x_1206);
lean_dec(x_1205);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec_ref(x_1201);
lean_dec(x_1198);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec_ref(x_1194);
lean_dec(x_1193);
lean_dec_ref(x_1192);
lean_dec(x_1191);
lean_dec_ref(x_1189);
lean_dec_ref(x_1188);
lean_dec(x_1187);
lean_dec(x_1186);
lean_dec_ref(x_1185);
lean_dec(x_1184);
lean_dec(x_1183);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1321 = lean_ctor_get(x_1282, 0);
lean_inc(x_1321);
if (lean_is_exclusive(x_1282)) {
 lean_ctor_release(x_1282, 0);
 x_1322 = x_1282;
} else {
 lean_dec_ref(x_1282);
 x_1322 = lean_box(0);
}
if (lean_is_scalar(x_1322)) {
 x_1323 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1323 = x_1322;
}
lean_ctor_set(x_1323, 0, x_1321);
return x_1323;
}
}
else
{
lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; 
lean_dec(x_1273);
lean_dec(x_1269);
lean_dec(x_1267);
lean_dec(x_1259);
lean_dec(x_1257);
lean_dec(x_1252);
lean_dec(x_1249);
lean_dec(x_1244);
lean_dec(x_1240);
lean_dec(x_1235);
lean_dec(x_1225);
lean_dec(x_1217);
lean_dec(x_1214);
lean_dec_ref(x_1213);
lean_dec(x_1212);
lean_dec_ref(x_1211);
lean_dec(x_1210);
lean_dec_ref(x_1209);
lean_dec(x_1208);
lean_dec_ref(x_1207);
lean_dec(x_1206);
lean_dec(x_1205);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec_ref(x_1201);
lean_dec(x_1198);
lean_dec_ref(x_1197);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec_ref(x_1194);
lean_dec(x_1193);
lean_dec_ref(x_1192);
lean_dec(x_1191);
lean_dec_ref(x_1190);
lean_dec_ref(x_1189);
lean_dec_ref(x_1188);
lean_dec(x_1187);
lean_dec(x_1186);
lean_dec_ref(x_1185);
lean_dec(x_1184);
lean_dec(x_1183);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1324 = lean_ctor_get(x_1277, 0);
lean_inc(x_1324);
if (lean_is_exclusive(x_1277)) {
 lean_ctor_release(x_1277, 0);
 x_1325 = x_1277;
} else {
 lean_dec_ref(x_1277);
 x_1325 = lean_box(0);
}
if (lean_is_scalar(x_1325)) {
 x_1326 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1326 = x_1325;
}
lean_ctor_set(x_1326, 0, x_1324);
return x_1326;
}
}
else
{
lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; 
lean_dec(x_1269);
lean_dec(x_1267);
lean_dec(x_1259);
lean_dec(x_1257);
lean_dec(x_1252);
lean_dec(x_1249);
lean_dec(x_1244);
lean_dec(x_1240);
lean_dec(x_1235);
lean_dec(x_1225);
lean_dec(x_1220);
lean_dec(x_1217);
lean_dec(x_1214);
lean_dec_ref(x_1213);
lean_dec(x_1212);
lean_dec_ref(x_1211);
lean_dec(x_1210);
lean_dec_ref(x_1209);
lean_dec(x_1208);
lean_dec_ref(x_1207);
lean_dec(x_1206);
lean_dec(x_1205);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec_ref(x_1201);
lean_dec(x_1198);
lean_dec_ref(x_1197);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec_ref(x_1194);
lean_dec(x_1193);
lean_dec_ref(x_1192);
lean_dec(x_1191);
lean_dec_ref(x_1190);
lean_dec_ref(x_1189);
lean_dec_ref(x_1188);
lean_dec(x_1187);
lean_dec(x_1186);
lean_dec_ref(x_1185);
lean_dec(x_1184);
lean_dec(x_1183);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1327 = lean_ctor_get(x_1272, 0);
lean_inc(x_1327);
if (lean_is_exclusive(x_1272)) {
 lean_ctor_release(x_1272, 0);
 x_1328 = x_1272;
} else {
 lean_dec_ref(x_1272);
 x_1328 = lean_box(0);
}
if (lean_is_scalar(x_1328)) {
 x_1329 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1329 = x_1328;
}
lean_ctor_set(x_1329, 0, x_1327);
return x_1329;
}
}
else
{
lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; 
lean_dec(x_1267);
lean_dec_ref(x_1263);
lean_dec(x_1259);
lean_dec(x_1257);
lean_dec(x_1252);
lean_dec(x_1249);
lean_dec(x_1244);
lean_dec(x_1240);
lean_dec(x_1235);
lean_dec(x_1225);
lean_dec(x_1220);
lean_dec(x_1217);
lean_dec(x_1214);
lean_dec_ref(x_1213);
lean_dec(x_1212);
lean_dec_ref(x_1211);
lean_dec(x_1210);
lean_dec_ref(x_1209);
lean_dec(x_1208);
lean_dec_ref(x_1207);
lean_dec(x_1206);
lean_dec(x_1205);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec_ref(x_1201);
lean_dec(x_1198);
lean_dec_ref(x_1197);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec_ref(x_1194);
lean_dec(x_1193);
lean_dec_ref(x_1192);
lean_dec(x_1191);
lean_dec_ref(x_1190);
lean_dec_ref(x_1189);
lean_dec_ref(x_1188);
lean_dec(x_1187);
lean_dec(x_1186);
lean_dec_ref(x_1185);
lean_dec(x_1184);
lean_dec(x_1183);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1330 = lean_ctor_get(x_1268, 0);
lean_inc(x_1330);
if (lean_is_exclusive(x_1268)) {
 lean_ctor_release(x_1268, 0);
 x_1331 = x_1268;
} else {
 lean_dec_ref(x_1268);
 x_1331 = lean_box(0);
}
if (lean_is_scalar(x_1331)) {
 x_1332 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1332 = x_1331;
}
lean_ctor_set(x_1332, 0, x_1330);
return x_1332;
}
}
else
{
lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; 
lean_dec_ref(x_1263);
lean_dec(x_1259);
lean_dec(x_1257);
lean_dec(x_1252);
lean_dec(x_1249);
lean_dec(x_1244);
lean_dec(x_1240);
lean_dec(x_1235);
lean_dec(x_1225);
lean_dec(x_1220);
lean_dec(x_1217);
lean_dec(x_1214);
lean_dec_ref(x_1213);
lean_dec(x_1212);
lean_dec_ref(x_1211);
lean_dec(x_1210);
lean_dec_ref(x_1209);
lean_dec(x_1208);
lean_dec_ref(x_1207);
lean_dec(x_1206);
lean_dec(x_1205);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec_ref(x_1201);
lean_dec(x_1198);
lean_dec_ref(x_1197);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec_ref(x_1194);
lean_dec(x_1193);
lean_dec_ref(x_1192);
lean_dec(x_1191);
lean_dec_ref(x_1190);
lean_dec_ref(x_1189);
lean_dec_ref(x_1188);
lean_dec(x_1187);
lean_dec(x_1186);
lean_dec_ref(x_1185);
lean_dec(x_1184);
lean_dec(x_1183);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1333 = lean_ctor_get(x_1266, 0);
lean_inc(x_1333);
if (lean_is_exclusive(x_1266)) {
 lean_ctor_release(x_1266, 0);
 x_1334 = x_1266;
} else {
 lean_dec_ref(x_1266);
 x_1334 = lean_box(0);
}
if (lean_is_scalar(x_1334)) {
 x_1335 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1335 = x_1334;
}
lean_ctor_set(x_1335, 0, x_1333);
return x_1335;
}
}
else
{
lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; 
lean_dec(x_1257);
lean_dec(x_1252);
lean_dec(x_1249);
lean_dec(x_1244);
lean_dec(x_1240);
lean_dec(x_1235);
lean_dec(x_1225);
lean_dec(x_1220);
lean_dec(x_1217);
lean_dec(x_1214);
lean_dec_ref(x_1213);
lean_dec(x_1212);
lean_dec_ref(x_1211);
lean_dec(x_1210);
lean_dec_ref(x_1209);
lean_dec(x_1208);
lean_dec_ref(x_1207);
lean_dec(x_1206);
lean_dec(x_1205);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec_ref(x_1201);
lean_dec(x_1200);
lean_dec(x_1198);
lean_dec_ref(x_1197);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec_ref(x_1194);
lean_dec(x_1193);
lean_dec_ref(x_1192);
lean_dec(x_1191);
lean_dec_ref(x_1190);
lean_dec_ref(x_1189);
lean_dec_ref(x_1188);
lean_dec(x_1187);
lean_dec(x_1186);
lean_dec_ref(x_1185);
lean_dec(x_1184);
lean_dec(x_1183);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1336 = lean_ctor_get(x_1258, 0);
lean_inc(x_1336);
if (lean_is_exclusive(x_1258)) {
 lean_ctor_release(x_1258, 0);
 x_1337 = x_1258;
} else {
 lean_dec_ref(x_1258);
 x_1337 = lean_box(0);
}
if (lean_is_scalar(x_1337)) {
 x_1338 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1338 = x_1337;
}
lean_ctor_set(x_1338, 0, x_1336);
return x_1338;
}
}
else
{
lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; 
lean_dec(x_1252);
lean_dec(x_1249);
lean_dec(x_1244);
lean_dec(x_1240);
lean_dec(x_1235);
lean_dec(x_1225);
lean_dec(x_1220);
lean_dec(x_1217);
lean_dec(x_1214);
lean_dec_ref(x_1213);
lean_dec(x_1212);
lean_dec_ref(x_1211);
lean_dec(x_1210);
lean_dec_ref(x_1209);
lean_dec(x_1208);
lean_dec_ref(x_1207);
lean_dec(x_1206);
lean_dec(x_1205);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec_ref(x_1201);
lean_dec(x_1200);
lean_dec(x_1198);
lean_dec_ref(x_1197);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec_ref(x_1194);
lean_dec(x_1193);
lean_dec_ref(x_1192);
lean_dec(x_1191);
lean_dec_ref(x_1190);
lean_dec_ref(x_1189);
lean_dec_ref(x_1188);
lean_dec(x_1187);
lean_dec(x_1186);
lean_dec_ref(x_1185);
lean_dec(x_1184);
lean_dec(x_1183);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1339 = lean_ctor_get(x_1256, 0);
lean_inc(x_1339);
if (lean_is_exclusive(x_1256)) {
 lean_ctor_release(x_1256, 0);
 x_1340 = x_1256;
} else {
 lean_dec_ref(x_1256);
 x_1340 = lean_box(0);
}
if (lean_is_scalar(x_1340)) {
 x_1341 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1341 = x_1340;
}
lean_ctor_set(x_1341, 0, x_1339);
return x_1341;
}
}
else
{
lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; 
lean_dec(x_1249);
lean_dec(x_1244);
lean_dec(x_1240);
lean_dec(x_1235);
lean_dec(x_1225);
lean_dec(x_1220);
lean_dec(x_1217);
lean_dec(x_1214);
lean_dec_ref(x_1213);
lean_dec(x_1212);
lean_dec_ref(x_1211);
lean_dec(x_1210);
lean_dec_ref(x_1209);
lean_dec(x_1208);
lean_dec_ref(x_1207);
lean_dec(x_1206);
lean_dec(x_1205);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec_ref(x_1201);
lean_dec(x_1200);
lean_dec(x_1198);
lean_dec_ref(x_1197);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec_ref(x_1194);
lean_dec(x_1193);
lean_dec_ref(x_1192);
lean_dec(x_1191);
lean_dec_ref(x_1190);
lean_dec_ref(x_1189);
lean_dec_ref(x_1188);
lean_dec(x_1187);
lean_dec(x_1186);
lean_dec_ref(x_1185);
lean_dec(x_1184);
lean_dec(x_1183);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1342 = lean_ctor_get(x_1251, 0);
lean_inc(x_1342);
if (lean_is_exclusive(x_1251)) {
 lean_ctor_release(x_1251, 0);
 x_1343 = x_1251;
} else {
 lean_dec_ref(x_1251);
 x_1343 = lean_box(0);
}
if (lean_is_scalar(x_1343)) {
 x_1344 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1344 = x_1343;
}
lean_ctor_set(x_1344, 0, x_1342);
return x_1344;
}
}
else
{
lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; 
lean_dec(x_1244);
lean_dec(x_1240);
lean_dec(x_1235);
lean_dec(x_1225);
lean_dec(x_1220);
lean_dec(x_1217);
lean_dec(x_1214);
lean_dec_ref(x_1213);
lean_dec(x_1212);
lean_dec_ref(x_1211);
lean_dec(x_1210);
lean_dec_ref(x_1209);
lean_dec(x_1208);
lean_dec_ref(x_1207);
lean_dec(x_1206);
lean_dec(x_1205);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec_ref(x_1201);
lean_dec(x_1200);
lean_dec(x_1198);
lean_dec_ref(x_1197);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec_ref(x_1194);
lean_dec(x_1193);
lean_dec_ref(x_1192);
lean_dec(x_1191);
lean_dec_ref(x_1190);
lean_dec_ref(x_1189);
lean_dec_ref(x_1188);
lean_dec(x_1187);
lean_dec(x_1186);
lean_dec_ref(x_1185);
lean_dec(x_1184);
lean_dec(x_1183);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1345 = lean_ctor_get(x_1248, 0);
lean_inc(x_1345);
if (lean_is_exclusive(x_1248)) {
 lean_ctor_release(x_1248, 0);
 x_1346 = x_1248;
} else {
 lean_dec_ref(x_1248);
 x_1346 = lean_box(0);
}
if (lean_is_scalar(x_1346)) {
 x_1347 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1347 = x_1346;
}
lean_ctor_set(x_1347, 0, x_1345);
return x_1347;
}
}
else
{
lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; 
lean_dec(x_1240);
lean_dec(x_1235);
lean_dec(x_1225);
lean_dec(x_1220);
lean_dec(x_1217);
lean_dec(x_1214);
lean_dec_ref(x_1213);
lean_dec(x_1212);
lean_dec_ref(x_1211);
lean_dec(x_1210);
lean_dec_ref(x_1209);
lean_dec(x_1208);
lean_dec_ref(x_1207);
lean_dec(x_1206);
lean_dec(x_1205);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec_ref(x_1201);
lean_dec(x_1200);
lean_dec(x_1198);
lean_dec_ref(x_1197);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec_ref(x_1194);
lean_dec(x_1193);
lean_dec_ref(x_1192);
lean_dec(x_1191);
lean_dec_ref(x_1190);
lean_dec_ref(x_1189);
lean_dec_ref(x_1188);
lean_dec(x_1187);
lean_dec(x_1186);
lean_dec_ref(x_1185);
lean_dec(x_1184);
lean_dec(x_1183);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1348 = lean_ctor_get(x_1243, 0);
lean_inc(x_1348);
if (lean_is_exclusive(x_1243)) {
 lean_ctor_release(x_1243, 0);
 x_1349 = x_1243;
} else {
 lean_dec_ref(x_1243);
 x_1349 = lean_box(0);
}
if (lean_is_scalar(x_1349)) {
 x_1350 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1350 = x_1349;
}
lean_ctor_set(x_1350, 0, x_1348);
return x_1350;
}
}
else
{
lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; 
lean_dec(x_1240);
lean_dec(x_1235);
lean_dec(x_1225);
lean_dec(x_1220);
lean_dec(x_1217);
lean_dec(x_1214);
lean_dec_ref(x_1213);
lean_dec(x_1212);
lean_dec_ref(x_1211);
lean_dec(x_1210);
lean_dec_ref(x_1209);
lean_dec(x_1208);
lean_dec_ref(x_1207);
lean_dec(x_1206);
lean_dec(x_1205);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec_ref(x_1201);
lean_dec(x_1200);
lean_dec(x_1198);
lean_dec_ref(x_1197);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec_ref(x_1194);
lean_dec(x_1193);
lean_dec_ref(x_1192);
lean_dec(x_1191);
lean_dec_ref(x_1190);
lean_dec_ref(x_1189);
lean_dec_ref(x_1188);
lean_dec(x_1187);
lean_dec(x_1186);
lean_dec_ref(x_1185);
lean_dec(x_1184);
lean_dec(x_1183);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1351 = lean_ctor_get(x_1241, 0);
lean_inc(x_1351);
if (lean_is_exclusive(x_1241)) {
 lean_ctor_release(x_1241, 0);
 x_1352 = x_1241;
} else {
 lean_dec_ref(x_1241);
 x_1352 = lean_box(0);
}
if (lean_is_scalar(x_1352)) {
 x_1353 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1353 = x_1352;
}
lean_ctor_set(x_1353, 0, x_1351);
return x_1353;
}
}
else
{
lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; 
lean_dec(x_1235);
lean_dec(x_1225);
lean_dec(x_1220);
lean_dec(x_1217);
lean_dec(x_1214);
lean_dec_ref(x_1213);
lean_dec(x_1212);
lean_dec_ref(x_1211);
lean_dec(x_1210);
lean_dec_ref(x_1209);
lean_dec(x_1208);
lean_dec_ref(x_1207);
lean_dec(x_1206);
lean_dec(x_1205);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec_ref(x_1201);
lean_dec(x_1200);
lean_dec(x_1198);
lean_dec_ref(x_1197);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec_ref(x_1194);
lean_dec(x_1193);
lean_dec_ref(x_1192);
lean_dec(x_1191);
lean_dec_ref(x_1190);
lean_dec_ref(x_1189);
lean_dec_ref(x_1188);
lean_dec(x_1187);
lean_dec(x_1186);
lean_dec_ref(x_1185);
lean_dec(x_1184);
lean_dec(x_1183);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1354 = lean_ctor_get(x_1239, 0);
lean_inc(x_1354);
if (lean_is_exclusive(x_1239)) {
 lean_ctor_release(x_1239, 0);
 x_1355 = x_1239;
} else {
 lean_dec_ref(x_1239);
 x_1355 = lean_box(0);
}
if (lean_is_scalar(x_1355)) {
 x_1356 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1356 = x_1355;
}
lean_ctor_set(x_1356, 0, x_1354);
return x_1356;
}
}
else
{
lean_object* x_1357; lean_object* x_1358; 
lean_dec(x_1232);
lean_dec(x_1225);
lean_dec(x_1220);
lean_dec(x_1217);
lean_dec(x_1214);
lean_dec_ref(x_1213);
lean_dec(x_1212);
lean_dec_ref(x_1211);
lean_dec(x_1210);
lean_dec_ref(x_1209);
lean_dec(x_1208);
lean_dec_ref(x_1207);
lean_dec(x_1206);
lean_dec(x_1205);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec_ref(x_1201);
lean_dec(x_1200);
lean_dec(x_1198);
lean_dec_ref(x_1197);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec_ref(x_1194);
lean_dec(x_1193);
lean_dec_ref(x_1192);
lean_dec(x_1191);
lean_dec_ref(x_1190);
lean_dec_ref(x_1189);
lean_dec_ref(x_1188);
lean_dec(x_1187);
lean_dec(x_1186);
lean_dec_ref(x_1185);
lean_dec(x_1184);
lean_dec(x_1183);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1357 = lean_box(0);
if (lean_is_scalar(x_1233)) {
 x_1358 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1358 = x_1233;
}
lean_ctor_set(x_1358, 0, x_1357);
return x_1358;
}
}
else
{
lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; 
lean_dec(x_1225);
lean_dec(x_1220);
lean_dec(x_1217);
lean_dec(x_1214);
lean_dec_ref(x_1213);
lean_dec(x_1212);
lean_dec_ref(x_1211);
lean_dec(x_1210);
lean_dec_ref(x_1209);
lean_dec(x_1208);
lean_dec_ref(x_1207);
lean_dec(x_1206);
lean_dec(x_1205);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec_ref(x_1201);
lean_dec(x_1200);
lean_dec(x_1198);
lean_dec_ref(x_1197);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec_ref(x_1194);
lean_dec(x_1193);
lean_dec_ref(x_1192);
lean_dec(x_1191);
lean_dec_ref(x_1190);
lean_dec_ref(x_1189);
lean_dec_ref(x_1188);
lean_dec(x_1187);
lean_dec(x_1186);
lean_dec_ref(x_1185);
lean_dec(x_1184);
lean_dec(x_1183);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1359 = lean_ctor_get(x_1231, 0);
lean_inc(x_1359);
if (lean_is_exclusive(x_1231)) {
 lean_ctor_release(x_1231, 0);
 x_1360 = x_1231;
} else {
 lean_dec_ref(x_1231);
 x_1360 = lean_box(0);
}
if (lean_is_scalar(x_1360)) {
 x_1361 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1361 = x_1360;
}
lean_ctor_set(x_1361, 0, x_1359);
return x_1361;
}
}
else
{
lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; 
lean_dec(x_1220);
lean_dec(x_1217);
lean_dec(x_1214);
lean_dec_ref(x_1213);
lean_dec(x_1212);
lean_dec_ref(x_1211);
lean_dec(x_1210);
lean_dec_ref(x_1209);
lean_dec(x_1208);
lean_dec_ref(x_1207);
lean_dec(x_1206);
lean_dec(x_1205);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec_ref(x_1201);
lean_dec(x_1200);
lean_dec(x_1198);
lean_dec_ref(x_1197);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec_ref(x_1194);
lean_dec(x_1193);
lean_dec_ref(x_1192);
lean_dec(x_1191);
lean_dec_ref(x_1190);
lean_dec_ref(x_1189);
lean_dec_ref(x_1188);
lean_dec(x_1187);
lean_dec(x_1186);
lean_dec_ref(x_1185);
lean_dec(x_1184);
lean_dec(x_1183);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1362 = lean_ctor_get(x_1224, 0);
lean_inc(x_1362);
if (lean_is_exclusive(x_1224)) {
 lean_ctor_release(x_1224, 0);
 x_1363 = x_1224;
} else {
 lean_dec_ref(x_1224);
 x_1363 = lean_box(0);
}
if (lean_is_scalar(x_1363)) {
 x_1364 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1364 = x_1363;
}
lean_ctor_set(x_1364, 0, x_1362);
return x_1364;
}
}
else
{
lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; 
lean_dec(x_1217);
lean_dec(x_1214);
lean_dec_ref(x_1213);
lean_dec(x_1212);
lean_dec_ref(x_1211);
lean_dec(x_1210);
lean_dec_ref(x_1209);
lean_dec(x_1208);
lean_dec_ref(x_1207);
lean_dec(x_1206);
lean_dec(x_1205);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec_ref(x_1201);
lean_dec(x_1200);
lean_dec(x_1198);
lean_dec_ref(x_1197);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec_ref(x_1194);
lean_dec(x_1193);
lean_dec_ref(x_1192);
lean_dec(x_1191);
lean_dec_ref(x_1190);
lean_dec_ref(x_1189);
lean_dec_ref(x_1188);
lean_dec(x_1187);
lean_dec(x_1186);
lean_dec_ref(x_1185);
lean_dec(x_1184);
lean_dec(x_1183);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1365 = lean_ctor_get(x_1219, 0);
lean_inc(x_1365);
if (lean_is_exclusive(x_1219)) {
 lean_ctor_release(x_1219, 0);
 x_1366 = x_1219;
} else {
 lean_dec_ref(x_1219);
 x_1366 = lean_box(0);
}
if (lean_is_scalar(x_1366)) {
 x_1367 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1367 = x_1366;
}
lean_ctor_set(x_1367, 0, x_1365);
return x_1367;
}
}
else
{
lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; 
lean_dec(x_1214);
lean_dec_ref(x_1213);
lean_dec(x_1212);
lean_dec_ref(x_1211);
lean_dec(x_1210);
lean_dec_ref(x_1209);
lean_dec(x_1208);
lean_dec_ref(x_1207);
lean_dec(x_1206);
lean_dec(x_1205);
lean_dec(x_1204);
lean_dec(x_1203);
lean_dec(x_1202);
lean_dec_ref(x_1201);
lean_dec(x_1200);
lean_dec(x_1198);
lean_dec_ref(x_1197);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec_ref(x_1194);
lean_dec(x_1193);
lean_dec_ref(x_1192);
lean_dec(x_1191);
lean_dec_ref(x_1190);
lean_dec_ref(x_1189);
lean_dec_ref(x_1188);
lean_dec(x_1187);
lean_dec(x_1186);
lean_dec_ref(x_1185);
lean_dec(x_1184);
lean_dec(x_1183);
lean_dec(x_1011);
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec_ref(x_1);
x_1368 = lean_ctor_get(x_1216, 0);
lean_inc(x_1368);
if (lean_is_exclusive(x_1216)) {
 lean_ctor_release(x_1216, 0);
 x_1369 = x_1216;
} else {
 lean_dec_ref(x_1216);
 x_1369 = lean_box(0);
}
if (lean_is_scalar(x_1369)) {
 x_1370 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1370 = x_1369;
}
lean_ctor_set(x_1370, 0, x_1368);
return x_1370;
}
}
}
else
{
lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; 
lean_dec(x_1009);
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1634 = lean_ctor_get(x_1010, 0);
lean_inc(x_1634);
if (lean_is_exclusive(x_1010)) {
 lean_ctor_release(x_1010, 0);
 x_1635 = x_1010;
} else {
 lean_dec_ref(x_1010);
 x_1635 = lean_box(0);
}
if (lean_is_scalar(x_1635)) {
 x_1636 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1636 = x_1635;
}
lean_ctor_set(x_1636, 0, x_1634);
return x_1636;
}
}
else
{
lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; 
lean_dec(x_1006);
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1637 = lean_ctor_get(x_1008, 0);
lean_inc(x_1637);
if (lean_is_exclusive(x_1008)) {
 lean_ctor_release(x_1008, 0);
 x_1638 = x_1008;
} else {
 lean_dec_ref(x_1008);
 x_1638 = lean_box(0);
}
if (lean_is_scalar(x_1638)) {
 x_1639 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1639 = x_1638;
}
lean_ctor_set(x_1639, 0, x_1637);
return x_1639;
}
}
else
{
lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; 
lean_dec(x_1003);
lean_dec(x_1002);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1640 = lean_ctor_get(x_1005, 0);
lean_inc(x_1640);
if (lean_is_exclusive(x_1005)) {
 lean_ctor_release(x_1005, 0);
 x_1641 = x_1005;
} else {
 lean_dec_ref(x_1005);
 x_1641 = lean_box(0);
}
if (lean_is_scalar(x_1641)) {
 x_1642 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1642 = x_1641;
}
lean_ctor_set(x_1642, 0, x_1640);
return x_1642;
}
}
else
{
lean_dec(x_1000);
lean_dec(x_999);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_1001;
}
}
else
{
lean_object* x_1643; lean_object* x_1644; 
lean_dec(x_998);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1643 = lean_box(0);
x_1644 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1644, 0, x_1643);
return x_1644;
}
}
}
else
{
uint8_t x_1645; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1645 = !lean_is_exclusive(x_67);
if (x_1645 == 0)
{
return x_67;
}
else
{
lean_object* x_1646; lean_object* x_1647; 
x_1646 = lean_ctor_get(x_67, 0);
lean_inc(x_1646);
lean_dec(x_67);
x_1647 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1647, 0, x_1646);
return x_1647;
}
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
block_23:
{
if (lean_obj_tag(x_19) == 0)
{
lean_dec_ref(x_19);
x_13 = x_18;
x_14 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_20; 
lean_dec(x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
block_45:
{
lean_object* x_38; 
lean_inc(x_24);
lean_inc(x_26);
x_38 = l_Lean_Meta_Grind_Arith_Linear_mkVar(x_32, x_31, x_26, x_24, x_34, x_28, x_27, x_37, x_30, x_25, x_36, x_29, x_33);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
lean_inc(x_26);
lean_inc(x_39);
x_40 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(x_39, x_26, x_24);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
lean_dec_ref(x_40);
lean_inc(x_26);
x_41 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(x_39, x_26, x_24);
lean_dec(x_24);
x_18 = x_26;
x_19 = x_41;
goto block_23;
}
else
{
lean_dec(x_39);
lean_dec(x_24);
x_18 = x_26;
x_19 = x_40;
goto block_23;
}
}
else
{
uint8_t x_42; 
lean_dec(x_26);
lean_dec(x_24);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_38, 0);
lean_inc(x_43);
lean_dec(x_38);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
block_66:
{
lean_object* x_60; 
lean_inc(x_46);
lean_inc(x_48);
x_60 = l_Lean_Meta_Grind_Arith_Linear_mkVar(x_54, x_53, x_48, x_46, x_56, x_50, x_49, x_58, x_52, x_47, x_59, x_51, x_55);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
lean_inc(x_48);
x_62 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(x_61, x_48, x_46);
lean_dec(x_46);
x_18 = x_48;
x_19 = x_62;
goto block_23;
}
else
{
uint8_t x_63; 
lean_dec(x_48);
lean_dec(x_46);
x_63 = !lean_is_exclusive(x_60);
if (x_63 == 0)
{
return x_60;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_60, 0);
lean_inc(x_64);
lean_dec(x_60);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1_spec__2___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0___redArg(x_5, x_1, x_2);
lean_ctor_set(x_3, 1, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_3, 2);
x_10 = lean_ctor_get(x_3, 3);
x_11 = lean_ctor_get(x_3, 4);
x_12 = lean_ctor_get(x_3, 5);
x_13 = lean_ctor_get(x_3, 6);
x_14 = lean_ctor_get(x_3, 7);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_15 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0___redArg(x_8, x_1, x_2);
x_16 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_9);
lean_ctor_set(x_16, 3, x_10);
lean_ctor_set(x_16, 4, x_11);
lean_ctor_set(x_16, 5, x_12);
lean_ctor_set(x_16, 6, x_13);
lean_ctor_set(x_16, 7, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget_borrowed(x_1, x_3);
x_9 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget_borrowed(x_2, x_3);
lean_dec(x_3);
lean_inc(x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_box(2);
x_7 = 5;
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1;
x_9 = lean_usize_land(x_2, x_8);
x_10 = lean_usize_to_nat(x_9);
x_11 = lean_array_get(x_6, x_5, x_10);
lean_dec(x_10);
lean_dec_ref(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_free_object(x_1);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
lean_free_object(x_1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec_ref(x_11);
x_17 = lean_usize_shift_right(x_2, x_7);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_box(2);
x_22 = 5;
x_23 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1;
x_24 = lean_usize_land(x_2, x_23);
x_25 = lean_usize_to_nat(x_24);
x_26 = lean_array_get(x_21, x_20, x_25);
lean_dec(x_25);
lean_dec_ref(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
}
case 1:
{
lean_object* x_32; size_t x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec_ref(x_26);
x_33 = lean_usize_shift_right(x_2, x_22);
x_1 = x_32;
x_2 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; 
x_35 = lean_box(0);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_37);
lean_dec_ref(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(x_36, x_37, x_38, x_3);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*11 + 21);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; 
lean_free_object(x_13);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_18 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_free_object(x_18);
x_22 = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(x_2, x_10);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_25);
lean_dec(x_24);
x_26 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(x_25, x_1);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_27; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
lean_ctor_set(x_22, 0, x_27);
return x_22;
}
else
{
lean_object* x_28; 
lean_dec(x_26);
lean_free_object(x_22);
lean_inc(x_2);
lean_inc_ref(x_1);
x_28 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
lean_inc(x_29);
x_30 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___lam__0), 3, 2);
lean_closure_set(x_30, 0, x_1);
lean_closure_set(x_30, 1, x_29);
x_31 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_32 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_31, x_30, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_29);
return x_32;
}
else
{
lean_object* x_35; 
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_29);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_29);
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_28;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_22, 0);
lean_inc(x_39);
lean_dec(x_22);
x_40 = lean_ctor_get(x_39, 1);
lean_inc_ref(x_40);
lean_dec(x_39);
x_41 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(x_40, x_1);
if (lean_obj_tag(x_41) == 1)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
else
{
lean_object* x_44; 
lean_dec(x_41);
lean_inc(x_2);
lean_inc_ref(x_1);
x_44 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
lean_inc(x_45);
x_46 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___lam__0), 3, 2);
lean_closure_set(x_46, 0, x_1);
lean_closure_set(x_46, 1, x_45);
x_47 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_48 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_47, x_46, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_49 = x_48;
} else {
 lean_dec_ref(x_48);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 1, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_45);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_45);
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_52 = x_48;
} else {
 lean_dec_ref(x_48);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_51);
return x_53;
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_44;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_54 = !lean_is_exclusive(x_22);
if (x_54 == 0)
{
return x_22;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_22, 0);
lean_inc(x_55);
lean_dec(x_22);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_57 = lean_box(0);
lean_ctor_set(x_18, 0, x_57);
return x_18;
}
}
else
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_18, 0);
lean_inc(x_58);
lean_dec(x_18);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(x_2, x_10);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_ctor_get(x_61, 1);
lean_inc_ref(x_63);
lean_dec(x_61);
x_64 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(x_63, x_1);
if (lean_obj_tag(x_64) == 1)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
if (lean_is_scalar(x_62)) {
 x_66 = lean_alloc_ctor(0, 1, 0);
} else {
 x_66 = x_62;
}
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
else
{
lean_object* x_67; 
lean_dec(x_64);
lean_dec(x_62);
lean_inc(x_2);
lean_inc_ref(x_1);
x_67 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
lean_inc(x_68);
x_69 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___lam__0), 3, 2);
lean_closure_set(x_69, 0, x_1);
lean_closure_set(x_69, 1, x_68);
x_70 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_71 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_70, x_69, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 x_72 = x_71;
} else {
 lean_dec_ref(x_71);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 1, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_68);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_68);
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 x_75 = x_71;
} else {
 lean_dec_ref(x_71);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_74);
return x_76;
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_67;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_77 = lean_ctor_get(x_60, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 x_78 = x_60;
} else {
 lean_dec_ref(x_60);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 1, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_77);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_82 = !lean_is_exclusive(x_18);
if (x_82 == 0)
{
return x_18;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_18, 0);
lean_inc(x_83);
lean_dec(x_18);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
}
}
else
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_13, 0);
lean_inc(x_85);
lean_dec(x_13);
x_86 = lean_ctor_get_uint8(x_85, sizeof(void*)*11 + 21);
lean_dec(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
else
{
lean_object* x_89; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_89 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 x_91 = x_89;
} else {
 lean_dec_ref(x_89);
 x_91 = lean_box(0);
}
x_92 = lean_unbox(x_90);
lean_dec(x_90);
if (x_92 == 0)
{
lean_object* x_93; 
lean_dec(x_91);
x_93 = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(x_2, x_10);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get(x_94, 1);
lean_inc_ref(x_96);
lean_dec(x_94);
x_97 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(x_96, x_1);
if (lean_obj_tag(x_97) == 1)
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
if (lean_is_scalar(x_95)) {
 x_99 = lean_alloc_ctor(0, 1, 0);
} else {
 x_99 = x_95;
}
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
else
{
lean_object* x_100; 
lean_dec(x_97);
lean_dec(x_95);
lean_inc(x_2);
lean_inc_ref(x_1);
x_100 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec_ref(x_100);
lean_inc(x_101);
x_102 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___lam__0), 3, 2);
lean_closure_set(x_102, 0, x_1);
lean_closure_set(x_102, 1, x_101);
x_103 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_104 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_103, x_102, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; 
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 x_105 = x_104;
} else {
 lean_dec_ref(x_104);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 1, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_101);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_101);
x_107 = lean_ctor_get(x_104, 0);
lean_inc(x_107);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 x_108 = x_104;
} else {
 lean_dec_ref(x_104);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 1, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_107);
return x_109;
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_100;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_110 = lean_ctor_get(x_93, 0);
lean_inc(x_110);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_111 = x_93;
} else {
 lean_dec_ref(x_93);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 1, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_110);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_113 = lean_box(0);
if (lean_is_scalar(x_91)) {
 x_114 = lean_alloc_ctor(0, 1, 0);
} else {
 x_114 = x_91;
}
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_115 = lean_ctor_get(x_89, 0);
lean_inc(x_115);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 x_116 = x_89;
} else {
 lean_dec_ref(x_89);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 1, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_115);
return x_117;
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_118 = !lean_is_exclusive(x_13);
if (x_118 == 0)
{
return x_13;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_13, 0);
lean_inc(x_119);
lean_dec(x_13);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1));
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_mkConst(x_8, x_10);
x_12 = l_Lean_Expr_app___override(x_11, x_2);
x_13 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_12, x_3, x_4, x_5, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(x_1, x_2, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 5);
x_5 = lean_array_push(x_4, x_1);
lean_ctor_set(x_2, 5, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get(x_2, 4);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_ctor_get(x_2, 6);
x_13 = lean_ctor_get(x_2, 7);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_14 = lean_array_push(x_11, x_1);
x_15 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_7);
lean_ctor_set(x_15, 2, x_8);
lean_ctor_set(x_15, 3, x_9);
lean_ctor_set(x_15, 4, x_10);
lean_ctor_set(x_15, 5, x_14);
lean_ctor_set(x_15, 6, x_12);
lean_ctor_set(x_15, 7, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__12;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__14));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
x_13 = l_Lean_Meta_getDecLevel(x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
lean_inc(x_14);
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(x_14, x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2));
x_20 = lean_box(0);
lean_inc(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
lean_inc_ref(x_21);
x_22 = l_Lean_mkConst(x_19, x_21);
lean_inc(x_18);
lean_inc_ref(x_1);
x_23 = l_Lean_mkAppB(x_22, x_1, x_18);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_24 = lean_grind_canon(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = l_Lean_Meta_Sym_shareCommon___redArg(x_25, x_7);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_27);
x_28 = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
if (lean_obj_tag(x_29) == 1)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1));
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
lean_inc(x_14);
x_33 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(x_32, x_14, x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__3));
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
lean_inc(x_14);
x_36 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(x_35, x_14, x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_34);
lean_inc_ref(x_1);
lean_inc(x_14);
x_38 = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(x_14, x_1, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_34);
lean_inc(x_37);
lean_inc_ref(x_1);
lean_inc(x_14);
x_40 = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(x_14, x_1, x_37, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_34);
lean_inc_ref(x_1);
lean_inc(x_14);
x_42 = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(x_14, x_1, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__63));
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
lean_inc(x_14);
x_45 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(x_44, x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__65));
lean_inc_ref(x_21);
lean_inc(x_14);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_14);
lean_ctor_set(x_48, 1, x_21);
lean_inc_ref(x_48);
lean_inc(x_14);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_14);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_mkConst(x_47, x_49);
lean_inc(x_46);
lean_inc_ref_n(x_1, 3);
x_51 = l_Lean_mkApp4(x_50, x_1, x_1, x_1, x_46);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_52 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
if (lean_obj_tag(x_34) == 1)
{
if (lean_obj_tag(x_39) == 1)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_158 = lean_ctor_get(x_34, 0);
x_159 = lean_ctor_get(x_39, 0);
x_160 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__67));
lean_inc_ref(x_21);
x_161 = l_Lean_mkConst(x_160, x_21);
lean_inc(x_159);
lean_inc(x_158);
lean_inc_ref(x_1);
x_162 = l_Lean_mkApp4(x_161, x_1, x_46, x_158, x_159);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_163 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_162, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
lean_dec_ref(x_163);
x_54 = x_164;
x_55 = x_2;
x_56 = x_3;
x_57 = x_4;
x_58 = x_5;
x_59 = x_6;
x_60 = x_7;
x_61 = x_8;
x_62 = x_9;
x_63 = x_10;
x_64 = x_11;
x_65 = lean_box(0);
goto block_145;
}
else
{
uint8_t x_165; 
lean_dec(x_53);
lean_dec_ref(x_48);
lean_dec(x_43);
lean_dec(x_41);
lean_dec_ref(x_39);
lean_dec(x_37);
lean_dec_ref(x_34);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_27);
lean_dec_ref(x_21);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_165 = !lean_is_exclusive(x_163);
if (x_165 == 0)
{
return x_163;
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_163, 0);
lean_inc(x_166);
lean_dec(x_163);
x_167 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_167, 0, x_166);
return x_167;
}
}
}
else
{
lean_dec(x_46);
x_146 = x_2;
x_147 = x_3;
x_148 = x_4;
x_149 = x_5;
x_150 = x_6;
x_151 = x_7;
x_152 = x_8;
x_153 = x_9;
x_154 = x_10;
x_155 = x_11;
goto block_157;
}
}
else
{
lean_dec(x_46);
x_146 = x_2;
x_147 = x_3;
x_148 = x_4;
x_149 = x_5;
x_150 = x_6;
x_151 = x_7;
x_152 = x_8;
x_153 = x_9;
x_154 = x_10;
x_155 = x_11;
goto block_157;
}
block_145:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4));
lean_inc_ref(x_21);
x_67 = l_Lean_mkConst(x_66, x_21);
lean_inc_ref(x_1);
x_68 = l_Lean_Expr_app___override(x_67, x_1);
lean_inc(x_64);
lean_inc_ref(x_63);
lean_inc(x_62);
lean_inc_ref(x_61);
x_69 = l_Lean_Meta_Grind_synthInstance(x_68, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_63, x_64);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_71 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6));
lean_inc_ref(x_21);
x_72 = l_Lean_mkConst(x_71, x_21);
lean_inc_ref(x_1);
x_73 = l_Lean_mkAppB(x_72, x_1, x_70);
lean_inc(x_64);
lean_inc_ref(x_63);
lean_inc(x_62);
lean_inc_ref(x_61);
x_74 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_73, x_61, x_62, x_63, x_64);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
x_76 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8));
lean_inc_ref(x_21);
x_77 = l_Lean_mkConst(x_76, x_21);
lean_inc(x_18);
lean_inc_ref(x_1);
x_78 = l_Lean_mkAppB(x_77, x_1, x_18);
lean_inc(x_64);
lean_inc_ref(x_63);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_79 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_78, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_63, x_64);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
x_81 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__15));
lean_inc(x_64);
lean_inc_ref(x_63);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc_ref(x_1);
lean_inc(x_14);
x_82 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(x_81, x_14, x_1, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_63, x_64);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
x_84 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__17));
x_85 = l_Lean_mkConst(x_84, x_21);
lean_inc_ref(x_1);
x_86 = l_Lean_mkAppB(x_85, x_1, x_83);
lean_inc(x_64);
lean_inc_ref(x_63);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_87 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(x_86, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_63, x_64);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
lean_inc(x_64);
lean_inc_ref(x_63);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc_ref(x_1);
lean_inc(x_14);
x_89 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(x_14, x_1, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_63, x_64);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
x_91 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__1));
x_92 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2;
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_48);
x_94 = l_Lean_mkConst(x_91, x_93);
x_95 = l_Lean_Nat_mkType;
lean_inc_ref_n(x_1, 2);
x_96 = l_Lean_mkApp4(x_94, x_95, x_1, x_1, x_90);
lean_inc_ref(x_63);
lean_inc(x_55);
x_97 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_96, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_63, x_64);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
x_99 = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(x_55, x_63);
lean_dec_ref(x_63);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec_ref(x_99);
x_101 = lean_ctor_get(x_100, 5);
lean_inc_ref(x_101);
lean_dec(x_100);
x_102 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__11));
lean_inc(x_14);
x_103 = l_Lean_Level_succ___override(x_14);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_20);
x_105 = l_Lean_mkConst(x_102, x_104);
x_106 = l_Lean_Expr_app___override(x_105, x_27);
x_107 = lean_array_get_size(x_101);
lean_dec_ref(x_101);
x_108 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__13;
x_109 = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_30);
lean_ctor_set(x_109, 2, x_1);
lean_ctor_set(x_109, 3, x_14);
lean_ctor_set(x_109, 4, x_18);
lean_ctor_set(x_109, 5, x_34);
lean_ctor_set(x_109, 6, x_37);
lean_ctor_set(x_109, 7, x_41);
lean_ctor_set(x_109, 8, x_39);
lean_ctor_set(x_109, 9, x_54);
lean_ctor_set(x_109, 10, x_43);
lean_ctor_set(x_109, 11, x_75);
lean_ctor_set(x_109, 12, x_106);
lean_ctor_set(x_109, 13, x_88);
lean_ctor_set(x_109, 14, x_80);
lean_ctor_set(x_109, 15, x_53);
lean_ctor_set(x_109, 16, x_98);
lean_ctor_set(x_109, 17, x_108);
x_110 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(x_110, 0, x_109);
x_111 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_112 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_111, x_110, x_55);
lean_dec(x_55);
if (lean_obj_tag(x_112) == 0)
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_112, 0);
lean_dec(x_114);
if (lean_is_scalar(x_31)) {
 x_115 = lean_alloc_ctor(1, 1, 0);
} else {
 x_115 = x_31;
}
lean_ctor_set(x_115, 0, x_107);
lean_ctor_set(x_112, 0, x_115);
return x_112;
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_112);
if (lean_is_scalar(x_31)) {
 x_116 = lean_alloc_ctor(1, 1, 0);
} else {
 x_116 = x_31;
}
lean_ctor_set(x_116, 0, x_107);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
}
else
{
uint8_t x_118; 
lean_dec(x_31);
x_118 = !lean_is_exclusive(x_112);
if (x_118 == 0)
{
return x_112;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_112, 0);
lean_inc(x_119);
lean_dec(x_112);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_98);
lean_dec(x_88);
lean_dec(x_80);
lean_dec(x_75);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_1);
x_121 = !lean_is_exclusive(x_99);
if (x_121 == 0)
{
return x_99;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_99, 0);
lean_inc(x_122);
lean_dec(x_99);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_88);
lean_dec(x_80);
lean_dec(x_75);
lean_dec_ref(x_63);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_1);
x_124 = !lean_is_exclusive(x_97);
if (x_124 == 0)
{
return x_97;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_97, 0);
lean_inc(x_125);
lean_dec(x_97);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_88);
lean_dec(x_80);
lean_dec(x_75);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec_ref(x_48);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_1);
x_127 = !lean_is_exclusive(x_89);
if (x_127 == 0)
{
return x_89;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_89, 0);
lean_inc(x_128);
lean_dec(x_89);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_80);
lean_dec(x_75);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec_ref(x_48);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_1);
x_130 = !lean_is_exclusive(x_87);
if (x_130 == 0)
{
return x_87;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_87, 0);
lean_inc(x_131);
lean_dec(x_87);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_131);
return x_132;
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_80);
lean_dec(x_75);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec_ref(x_48);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_27);
lean_dec_ref(x_21);
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_1);
x_133 = !lean_is_exclusive(x_82);
if (x_133 == 0)
{
return x_82;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_82, 0);
lean_inc(x_134);
lean_dec(x_82);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
}
}
else
{
uint8_t x_136; 
lean_dec(x_75);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec_ref(x_48);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_27);
lean_dec_ref(x_21);
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_1);
x_136 = !lean_is_exclusive(x_79);
if (x_136 == 0)
{
return x_79;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_79, 0);
lean_inc(x_137);
lean_dec(x_79);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_137);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec_ref(x_48);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_27);
lean_dec_ref(x_21);
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_1);
x_139 = !lean_is_exclusive(x_74);
if (x_139 == 0)
{
return x_74;
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_74, 0);
lean_inc(x_140);
lean_dec(x_74);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_140);
return x_141;
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec_ref(x_48);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_27);
lean_dec_ref(x_21);
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_1);
x_142 = !lean_is_exclusive(x_69);
if (x_142 == 0)
{
return x_69;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_69, 0);
lean_inc(x_143);
lean_dec(x_69);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_143);
return x_144;
}
}
}
block_157:
{
lean_object* x_156; 
x_156 = lean_box(0);
x_54 = x_156;
x_55 = x_146;
x_56 = x_147;
x_57 = x_148;
x_58 = x_149;
x_59 = x_150;
x_60 = x_151;
x_61 = x_152;
x_62 = x_153;
x_63 = x_154;
x_64 = x_155;
x_65 = lean_box(0);
goto block_145;
}
}
else
{
uint8_t x_168; 
lean_dec_ref(x_48);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_27);
lean_dec_ref(x_21);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_168 = !lean_is_exclusive(x_52);
if (x_168 == 0)
{
return x_52;
}
else
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_52, 0);
lean_inc(x_169);
lean_dec(x_52);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_169);
return x_170;
}
}
}
else
{
uint8_t x_171; 
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_27);
lean_dec_ref(x_21);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_171 = !lean_is_exclusive(x_45);
if (x_171 == 0)
{
return x_45;
}
else
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_45, 0);
lean_inc(x_172);
lean_dec(x_45);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_172);
return x_173;
}
}
}
else
{
uint8_t x_174; 
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_27);
lean_dec_ref(x_21);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_174 = !lean_is_exclusive(x_42);
if (x_174 == 0)
{
return x_42;
}
else
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_42, 0);
lean_inc(x_175);
lean_dec(x_42);
x_176 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_176, 0, x_175);
return x_176;
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_27);
lean_dec_ref(x_21);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_177 = !lean_is_exclusive(x_40);
if (x_177 == 0)
{
return x_40;
}
else
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_40, 0);
lean_inc(x_178);
lean_dec(x_40);
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_178);
return x_179;
}
}
}
else
{
uint8_t x_180; 
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_27);
lean_dec_ref(x_21);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_180 = !lean_is_exclusive(x_38);
if (x_180 == 0)
{
return x_38;
}
else
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_38, 0);
lean_inc(x_181);
lean_dec(x_38);
x_182 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_182, 0, x_181);
return x_182;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_27);
lean_dec_ref(x_21);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_183 = !lean_is_exclusive(x_36);
if (x_183 == 0)
{
return x_36;
}
else
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_36, 0);
lean_inc(x_184);
lean_dec(x_36);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_184);
return x_185;
}
}
}
else
{
uint8_t x_186; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_27);
lean_dec_ref(x_21);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_186 = !lean_is_exclusive(x_33);
if (x_186 == 0)
{
return x_33;
}
else
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_33, 0);
lean_inc(x_187);
lean_dec(x_33);
x_188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_188, 0, x_187);
return x_188;
}
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_29);
lean_dec_ref(x_21);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_189 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__15;
x_190 = l_Lean_indentExpr(x_27);
x_191 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
x_192 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(x_191, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_192;
}
}
else
{
lean_dec(x_27);
lean_dec_ref(x_21);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_28;
}
}
else
{
uint8_t x_193; 
lean_dec_ref(x_21);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_193 = !lean_is_exclusive(x_26);
if (x_193 == 0)
{
return x_26;
}
else
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_26, 0);
lean_inc(x_194);
lean_dec(x_26);
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_194);
return x_195;
}
}
}
else
{
uint8_t x_196; 
lean_dec_ref(x_21);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_196 = !lean_is_exclusive(x_24);
if (x_196 == 0)
{
return x_24;
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_24, 0);
lean_inc(x_197);
lean_dec(x_24);
x_198 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_198, 0, x_197);
return x_198;
}
}
}
else
{
lean_object* x_199; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_199 = lean_box(0);
lean_ctor_set(x_15, 0, x_199);
return x_15;
}
}
else
{
lean_object* x_200; 
x_200 = lean_ctor_get(x_15, 0);
lean_inc(x_200);
lean_dec(x_15);
if (lean_obj_tag(x_200) == 1)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
lean_dec_ref(x_200);
x_202 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2));
x_203 = lean_box(0);
lean_inc(x_14);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_14);
lean_ctor_set(x_204, 1, x_203);
lean_inc_ref(x_204);
x_205 = l_Lean_mkConst(x_202, x_204);
lean_inc(x_201);
lean_inc_ref(x_1);
x_206 = l_Lean_mkAppB(x_205, x_1, x_201);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_207 = lean_grind_canon(x_206, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec_ref(x_207);
x_209 = l_Lean_Meta_Sym_shareCommon___redArg(x_208, x_7);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
lean_dec_ref(x_209);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_210);
x_211 = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(x_210, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
lean_dec_ref(x_211);
if (lean_obj_tag(x_212) == 1)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 x_214 = x_212;
} else {
 lean_dec_ref(x_212);
 x_214 = lean_box(0);
}
x_215 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1));
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
lean_inc(x_14);
x_216 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(x_215, x_14, x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
lean_dec_ref(x_216);
x_218 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__3));
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
lean_inc(x_14);
x_219 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(x_218, x_14, x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
lean_dec_ref(x_219);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_217);
lean_inc_ref(x_1);
lean_inc(x_14);
x_221 = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(x_14, x_1, x_217, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
lean_dec_ref(x_221);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_217);
lean_inc(x_220);
lean_inc_ref(x_1);
lean_inc(x_14);
x_223 = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(x_14, x_1, x_220, x_217, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
lean_dec_ref(x_223);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_217);
lean_inc_ref(x_1);
lean_inc(x_14);
x_225 = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(x_14, x_1, x_217, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
lean_dec_ref(x_225);
x_227 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__63));
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
lean_inc(x_14);
x_228 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(x_227, x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
lean_dec_ref(x_228);
x_230 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__65));
lean_inc_ref(x_204);
lean_inc(x_14);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_14);
lean_ctor_set(x_231, 1, x_204);
lean_inc_ref(x_231);
lean_inc(x_14);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_14);
lean_ctor_set(x_232, 1, x_231);
x_233 = l_Lean_mkConst(x_230, x_232);
lean_inc(x_229);
lean_inc_ref_n(x_1, 3);
x_234 = l_Lean_mkApp4(x_233, x_1, x_1, x_1, x_229);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_235 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_234, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
lean_dec_ref(x_235);
if (lean_obj_tag(x_217) == 1)
{
if (lean_obj_tag(x_222) == 1)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_339 = lean_ctor_get(x_217, 0);
x_340 = lean_ctor_get(x_222, 0);
x_341 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__67));
lean_inc_ref(x_204);
x_342 = l_Lean_mkConst(x_341, x_204);
lean_inc(x_340);
lean_inc(x_339);
lean_inc_ref(x_1);
x_343 = l_Lean_mkApp4(x_342, x_1, x_229, x_339, x_340);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_344 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_343, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; 
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
lean_dec_ref(x_344);
x_237 = x_345;
x_238 = x_2;
x_239 = x_3;
x_240 = x_4;
x_241 = x_5;
x_242 = x_6;
x_243 = x_7;
x_244 = x_8;
x_245 = x_9;
x_246 = x_10;
x_247 = x_11;
x_248 = lean_box(0);
goto block_326;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_dec(x_236);
lean_dec_ref(x_231);
lean_dec(x_226);
lean_dec(x_224);
lean_dec_ref(x_222);
lean_dec(x_220);
lean_dec_ref(x_217);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_210);
lean_dec_ref(x_204);
lean_dec(x_201);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_346 = lean_ctor_get(x_344, 0);
lean_inc(x_346);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 x_347 = x_344;
} else {
 lean_dec_ref(x_344);
 x_347 = lean_box(0);
}
if (lean_is_scalar(x_347)) {
 x_348 = lean_alloc_ctor(1, 1, 0);
} else {
 x_348 = x_347;
}
lean_ctor_set(x_348, 0, x_346);
return x_348;
}
}
else
{
lean_dec(x_229);
x_327 = x_2;
x_328 = x_3;
x_329 = x_4;
x_330 = x_5;
x_331 = x_6;
x_332 = x_7;
x_333 = x_8;
x_334 = x_9;
x_335 = x_10;
x_336 = x_11;
goto block_338;
}
}
else
{
lean_dec(x_229);
x_327 = x_2;
x_328 = x_3;
x_329 = x_4;
x_330 = x_5;
x_331 = x_6;
x_332 = x_7;
x_333 = x_8;
x_334 = x_9;
x_335 = x_10;
x_336 = x_11;
goto block_338;
}
block_326:
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_249 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4));
lean_inc_ref(x_204);
x_250 = l_Lean_mkConst(x_249, x_204);
lean_inc_ref(x_1);
x_251 = l_Lean_Expr_app___override(x_250, x_1);
lean_inc(x_247);
lean_inc_ref(x_246);
lean_inc(x_245);
lean_inc_ref(x_244);
x_252 = l_Lean_Meta_Grind_synthInstance(x_251, x_238, x_239, x_240, x_241, x_242, x_243, x_244, x_245, x_246, x_247);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
lean_dec_ref(x_252);
x_254 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6));
lean_inc_ref(x_204);
x_255 = l_Lean_mkConst(x_254, x_204);
lean_inc_ref(x_1);
x_256 = l_Lean_mkAppB(x_255, x_1, x_253);
lean_inc(x_247);
lean_inc_ref(x_246);
lean_inc(x_245);
lean_inc_ref(x_244);
x_257 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_256, x_244, x_245, x_246, x_247);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
lean_dec_ref(x_257);
x_259 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8));
lean_inc_ref(x_204);
x_260 = l_Lean_mkConst(x_259, x_204);
lean_inc(x_201);
lean_inc_ref(x_1);
x_261 = l_Lean_mkAppB(x_260, x_1, x_201);
lean_inc(x_247);
lean_inc_ref(x_246);
lean_inc(x_245);
lean_inc_ref(x_244);
lean_inc(x_243);
lean_inc_ref(x_242);
lean_inc(x_241);
lean_inc_ref(x_240);
lean_inc(x_239);
lean_inc(x_238);
x_262 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_261, x_238, x_239, x_240, x_241, x_242, x_243, x_244, x_245, x_246, x_247);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
lean_dec_ref(x_262);
x_264 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__15));
lean_inc(x_247);
lean_inc_ref(x_246);
lean_inc(x_245);
lean_inc_ref(x_244);
lean_inc_ref(x_1);
lean_inc(x_14);
x_265 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(x_264, x_14, x_1, x_238, x_239, x_240, x_241, x_242, x_243, x_244, x_245, x_246, x_247);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
lean_dec_ref(x_265);
x_267 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__17));
x_268 = l_Lean_mkConst(x_267, x_204);
lean_inc_ref(x_1);
x_269 = l_Lean_mkAppB(x_268, x_1, x_266);
lean_inc(x_247);
lean_inc_ref(x_246);
lean_inc(x_245);
lean_inc_ref(x_244);
lean_inc(x_243);
lean_inc_ref(x_242);
lean_inc(x_241);
lean_inc_ref(x_240);
lean_inc(x_239);
lean_inc(x_238);
x_270 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(x_269, x_238, x_239, x_240, x_241, x_242, x_243, x_244, x_245, x_246, x_247);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
lean_dec_ref(x_270);
lean_inc(x_247);
lean_inc_ref(x_246);
lean_inc(x_245);
lean_inc_ref(x_244);
lean_inc_ref(x_1);
lean_inc(x_14);
x_272 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(x_14, x_1, x_238, x_239, x_240, x_241, x_242, x_243, x_244, x_245, x_246, x_247);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
lean_dec_ref(x_272);
x_274 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__1));
x_275 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2;
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_231);
x_277 = l_Lean_mkConst(x_274, x_276);
x_278 = l_Lean_Nat_mkType;
lean_inc_ref_n(x_1, 2);
x_279 = l_Lean_mkApp4(x_277, x_278, x_1, x_1, x_273);
lean_inc_ref(x_246);
lean_inc(x_238);
x_280 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(x_279, x_238, x_239, x_240, x_241, x_242, x_243, x_244, x_245, x_246, x_247);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
lean_dec_ref(x_280);
x_282 = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(x_238, x_246);
lean_dec_ref(x_246);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
lean_dec_ref(x_282);
x_284 = lean_ctor_get(x_283, 5);
lean_inc_ref(x_284);
lean_dec(x_283);
x_285 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__11));
lean_inc(x_14);
x_286 = l_Lean_Level_succ___override(x_14);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_203);
x_288 = l_Lean_mkConst(x_285, x_287);
x_289 = l_Lean_Expr_app___override(x_288, x_210);
x_290 = lean_array_get_size(x_284);
lean_dec_ref(x_284);
x_291 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__13;
x_292 = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_213);
lean_ctor_set(x_292, 2, x_1);
lean_ctor_set(x_292, 3, x_14);
lean_ctor_set(x_292, 4, x_201);
lean_ctor_set(x_292, 5, x_217);
lean_ctor_set(x_292, 6, x_220);
lean_ctor_set(x_292, 7, x_224);
lean_ctor_set(x_292, 8, x_222);
lean_ctor_set(x_292, 9, x_237);
lean_ctor_set(x_292, 10, x_226);
lean_ctor_set(x_292, 11, x_258);
lean_ctor_set(x_292, 12, x_289);
lean_ctor_set(x_292, 13, x_271);
lean_ctor_set(x_292, 14, x_263);
lean_ctor_set(x_292, 15, x_236);
lean_ctor_set(x_292, 16, x_281);
lean_ctor_set(x_292, 17, x_291);
x_293 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(x_293, 0, x_292);
x_294 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_295 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_294, x_293, x_238);
lean_dec(x_238);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 x_296 = x_295;
} else {
 lean_dec_ref(x_295);
 x_296 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_297 = lean_alloc_ctor(1, 1, 0);
} else {
 x_297 = x_214;
}
lean_ctor_set(x_297, 0, x_290);
if (lean_is_scalar(x_296)) {
 x_298 = lean_alloc_ctor(0, 1, 0);
} else {
 x_298 = x_296;
}
lean_ctor_set(x_298, 0, x_297);
return x_298;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_214);
x_299 = lean_ctor_get(x_295, 0);
lean_inc(x_299);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 x_300 = x_295;
} else {
 lean_dec_ref(x_295);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(1, 1, 0);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_299);
return x_301;
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_281);
lean_dec(x_271);
lean_dec(x_263);
lean_dec(x_258);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_226);
lean_dec(x_224);
lean_dec(x_222);
lean_dec(x_220);
lean_dec(x_217);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_210);
lean_dec(x_201);
lean_dec(x_14);
lean_dec_ref(x_1);
x_302 = lean_ctor_get(x_282, 0);
lean_inc(x_302);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 x_303 = x_282;
} else {
 lean_dec_ref(x_282);
 x_303 = lean_box(0);
}
if (lean_is_scalar(x_303)) {
 x_304 = lean_alloc_ctor(1, 1, 0);
} else {
 x_304 = x_303;
}
lean_ctor_set(x_304, 0, x_302);
return x_304;
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_271);
lean_dec(x_263);
lean_dec(x_258);
lean_dec_ref(x_246);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_226);
lean_dec(x_224);
lean_dec(x_222);
lean_dec(x_220);
lean_dec(x_217);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_210);
lean_dec(x_201);
lean_dec(x_14);
lean_dec_ref(x_1);
x_305 = lean_ctor_get(x_280, 0);
lean_inc(x_305);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 x_306 = x_280;
} else {
 lean_dec_ref(x_280);
 x_306 = lean_box(0);
}
if (lean_is_scalar(x_306)) {
 x_307 = lean_alloc_ctor(1, 1, 0);
} else {
 x_307 = x_306;
}
lean_ctor_set(x_307, 0, x_305);
return x_307;
}
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_271);
lean_dec(x_263);
lean_dec(x_258);
lean_dec(x_247);
lean_dec_ref(x_246);
lean_dec(x_245);
lean_dec_ref(x_244);
lean_dec(x_243);
lean_dec_ref(x_242);
lean_dec(x_241);
lean_dec_ref(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_236);
lean_dec_ref(x_231);
lean_dec(x_226);
lean_dec(x_224);
lean_dec(x_222);
lean_dec(x_220);
lean_dec(x_217);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_210);
lean_dec(x_201);
lean_dec(x_14);
lean_dec_ref(x_1);
x_308 = lean_ctor_get(x_272, 0);
lean_inc(x_308);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 x_309 = x_272;
} else {
 lean_dec_ref(x_272);
 x_309 = lean_box(0);
}
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(1, 1, 0);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_308);
return x_310;
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_263);
lean_dec(x_258);
lean_dec(x_247);
lean_dec_ref(x_246);
lean_dec(x_245);
lean_dec_ref(x_244);
lean_dec(x_243);
lean_dec_ref(x_242);
lean_dec(x_241);
lean_dec_ref(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_236);
lean_dec_ref(x_231);
lean_dec(x_226);
lean_dec(x_224);
lean_dec(x_222);
lean_dec(x_220);
lean_dec(x_217);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_210);
lean_dec(x_201);
lean_dec(x_14);
lean_dec_ref(x_1);
x_311 = lean_ctor_get(x_270, 0);
lean_inc(x_311);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 x_312 = x_270;
} else {
 lean_dec_ref(x_270);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(1, 1, 0);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_311);
return x_313;
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_dec(x_263);
lean_dec(x_258);
lean_dec(x_247);
lean_dec_ref(x_246);
lean_dec(x_245);
lean_dec_ref(x_244);
lean_dec(x_243);
lean_dec_ref(x_242);
lean_dec(x_241);
lean_dec_ref(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_236);
lean_dec_ref(x_231);
lean_dec(x_226);
lean_dec(x_224);
lean_dec(x_222);
lean_dec(x_220);
lean_dec(x_217);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_210);
lean_dec_ref(x_204);
lean_dec(x_201);
lean_dec(x_14);
lean_dec_ref(x_1);
x_314 = lean_ctor_get(x_265, 0);
lean_inc(x_314);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 x_315 = x_265;
} else {
 lean_dec_ref(x_265);
 x_315 = lean_box(0);
}
if (lean_is_scalar(x_315)) {
 x_316 = lean_alloc_ctor(1, 1, 0);
} else {
 x_316 = x_315;
}
lean_ctor_set(x_316, 0, x_314);
return x_316;
}
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_258);
lean_dec(x_247);
lean_dec_ref(x_246);
lean_dec(x_245);
lean_dec_ref(x_244);
lean_dec(x_243);
lean_dec_ref(x_242);
lean_dec(x_241);
lean_dec_ref(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_236);
lean_dec_ref(x_231);
lean_dec(x_226);
lean_dec(x_224);
lean_dec(x_222);
lean_dec(x_220);
lean_dec(x_217);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_210);
lean_dec_ref(x_204);
lean_dec(x_201);
lean_dec(x_14);
lean_dec_ref(x_1);
x_317 = lean_ctor_get(x_262, 0);
lean_inc(x_317);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 x_318 = x_262;
} else {
 lean_dec_ref(x_262);
 x_318 = lean_box(0);
}
if (lean_is_scalar(x_318)) {
 x_319 = lean_alloc_ctor(1, 1, 0);
} else {
 x_319 = x_318;
}
lean_ctor_set(x_319, 0, x_317);
return x_319;
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
lean_dec(x_247);
lean_dec_ref(x_246);
lean_dec(x_245);
lean_dec_ref(x_244);
lean_dec(x_243);
lean_dec_ref(x_242);
lean_dec(x_241);
lean_dec_ref(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_236);
lean_dec_ref(x_231);
lean_dec(x_226);
lean_dec(x_224);
lean_dec(x_222);
lean_dec(x_220);
lean_dec(x_217);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_210);
lean_dec_ref(x_204);
lean_dec(x_201);
lean_dec(x_14);
lean_dec_ref(x_1);
x_320 = lean_ctor_get(x_257, 0);
lean_inc(x_320);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 x_321 = x_257;
} else {
 lean_dec_ref(x_257);
 x_321 = lean_box(0);
}
if (lean_is_scalar(x_321)) {
 x_322 = lean_alloc_ctor(1, 1, 0);
} else {
 x_322 = x_321;
}
lean_ctor_set(x_322, 0, x_320);
return x_322;
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_247);
lean_dec_ref(x_246);
lean_dec(x_245);
lean_dec_ref(x_244);
lean_dec(x_243);
lean_dec_ref(x_242);
lean_dec(x_241);
lean_dec_ref(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_236);
lean_dec_ref(x_231);
lean_dec(x_226);
lean_dec(x_224);
lean_dec(x_222);
lean_dec(x_220);
lean_dec(x_217);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_210);
lean_dec_ref(x_204);
lean_dec(x_201);
lean_dec(x_14);
lean_dec_ref(x_1);
x_323 = lean_ctor_get(x_252, 0);
lean_inc(x_323);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 x_324 = x_252;
} else {
 lean_dec_ref(x_252);
 x_324 = lean_box(0);
}
if (lean_is_scalar(x_324)) {
 x_325 = lean_alloc_ctor(1, 1, 0);
} else {
 x_325 = x_324;
}
lean_ctor_set(x_325, 0, x_323);
return x_325;
}
}
block_338:
{
lean_object* x_337; 
x_337 = lean_box(0);
x_237 = x_337;
x_238 = x_327;
x_239 = x_328;
x_240 = x_329;
x_241 = x_330;
x_242 = x_331;
x_243 = x_332;
x_244 = x_333;
x_245 = x_334;
x_246 = x_335;
x_247 = x_336;
x_248 = lean_box(0);
goto block_326;
}
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
lean_dec_ref(x_231);
lean_dec(x_229);
lean_dec(x_226);
lean_dec(x_224);
lean_dec(x_222);
lean_dec(x_220);
lean_dec(x_217);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_210);
lean_dec_ref(x_204);
lean_dec(x_201);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_349 = lean_ctor_get(x_235, 0);
lean_inc(x_349);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 x_350 = x_235;
} else {
 lean_dec_ref(x_235);
 x_350 = lean_box(0);
}
if (lean_is_scalar(x_350)) {
 x_351 = lean_alloc_ctor(1, 1, 0);
} else {
 x_351 = x_350;
}
lean_ctor_set(x_351, 0, x_349);
return x_351;
}
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_226);
lean_dec(x_224);
lean_dec(x_222);
lean_dec(x_220);
lean_dec(x_217);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_210);
lean_dec_ref(x_204);
lean_dec(x_201);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_352 = lean_ctor_get(x_228, 0);
lean_inc(x_352);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 x_353 = x_228;
} else {
 lean_dec_ref(x_228);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(1, 1, 0);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_352);
return x_354;
}
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_dec(x_224);
lean_dec(x_222);
lean_dec(x_220);
lean_dec(x_217);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_210);
lean_dec_ref(x_204);
lean_dec(x_201);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_355 = lean_ctor_get(x_225, 0);
lean_inc(x_355);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 x_356 = x_225;
} else {
 lean_dec_ref(x_225);
 x_356 = lean_box(0);
}
if (lean_is_scalar(x_356)) {
 x_357 = lean_alloc_ctor(1, 1, 0);
} else {
 x_357 = x_356;
}
lean_ctor_set(x_357, 0, x_355);
return x_357;
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec(x_222);
lean_dec(x_220);
lean_dec(x_217);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_210);
lean_dec_ref(x_204);
lean_dec(x_201);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_358 = lean_ctor_get(x_223, 0);
lean_inc(x_358);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 x_359 = x_223;
} else {
 lean_dec_ref(x_223);
 x_359 = lean_box(0);
}
if (lean_is_scalar(x_359)) {
 x_360 = lean_alloc_ctor(1, 1, 0);
} else {
 x_360 = x_359;
}
lean_ctor_set(x_360, 0, x_358);
return x_360;
}
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec(x_220);
lean_dec(x_217);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_210);
lean_dec_ref(x_204);
lean_dec(x_201);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_361 = lean_ctor_get(x_221, 0);
lean_inc(x_361);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 x_362 = x_221;
} else {
 lean_dec_ref(x_221);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(1, 1, 0);
} else {
 x_363 = x_362;
}
lean_ctor_set(x_363, 0, x_361);
return x_363;
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_217);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_210);
lean_dec_ref(x_204);
lean_dec(x_201);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_364 = lean_ctor_get(x_219, 0);
lean_inc(x_364);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 x_365 = x_219;
} else {
 lean_dec_ref(x_219);
 x_365 = lean_box(0);
}
if (lean_is_scalar(x_365)) {
 x_366 = lean_alloc_ctor(1, 1, 0);
} else {
 x_366 = x_365;
}
lean_ctor_set(x_366, 0, x_364);
return x_366;
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_210);
lean_dec_ref(x_204);
lean_dec(x_201);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_367 = lean_ctor_get(x_216, 0);
lean_inc(x_367);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 x_368 = x_216;
} else {
 lean_dec_ref(x_216);
 x_368 = lean_box(0);
}
if (lean_is_scalar(x_368)) {
 x_369 = lean_alloc_ctor(1, 1, 0);
} else {
 x_369 = x_368;
}
lean_ctor_set(x_369, 0, x_367);
return x_369;
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec(x_212);
lean_dec_ref(x_204);
lean_dec(x_201);
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_370 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__15;
x_371 = l_Lean_indentExpr(x_210);
x_372 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
x_373 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(x_372, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_373;
}
}
else
{
lean_dec(x_210);
lean_dec_ref(x_204);
lean_dec(x_201);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_211;
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
lean_dec_ref(x_204);
lean_dec(x_201);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_374 = lean_ctor_get(x_209, 0);
lean_inc(x_374);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 x_375 = x_209;
} else {
 lean_dec_ref(x_209);
 x_375 = lean_box(0);
}
if (lean_is_scalar(x_375)) {
 x_376 = lean_alloc_ctor(1, 1, 0);
} else {
 x_376 = x_375;
}
lean_ctor_set(x_376, 0, x_374);
return x_376;
}
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec_ref(x_204);
lean_dec(x_201);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_377 = lean_ctor_get(x_207, 0);
lean_inc(x_377);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 x_378 = x_207;
} else {
 lean_dec_ref(x_207);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_378)) {
 x_379 = lean_alloc_ctor(1, 1, 0);
} else {
 x_379 = x_378;
}
lean_ctor_set(x_379, 0, x_377);
return x_379;
}
}
else
{
lean_object* x_380; lean_object* x_381; 
lean_dec(x_200);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_380 = lean_box(0);
x_381 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_381, 0, x_380);
return x_381;
}
}
}
else
{
uint8_t x_382; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_382 = !lean_is_exclusive(x_15);
if (x_382 == 0)
{
return x_15;
}
else
{
lean_object* x_383; lean_object* x_384; 
x_383 = lean_ctor_get(x_15, 0);
lean_inc(x_383);
lean_dec(x_15);
x_384 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_384, 0, x_383);
return x_384;
}
}
}
else
{
uint8_t x_385; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_385 = !lean_is_exclusive(x_13);
if (x_385 == 0)
{
return x_13;
}
else
{
lean_object* x_386; lean_object* x_387; 
x_386 = lean_ctor_get(x_13, 0);
lean_inc(x_386);
lean_dec(x_13);
x_387 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_387, 0, x_386);
return x_387;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(x_2, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 6);
x_6 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0___redArg(x_5, x_1, x_2);
lean_ctor_set(x_3, 6, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_3, 2);
x_10 = lean_ctor_get(x_3, 3);
x_11 = lean_ctor_get(x_3, 4);
x_12 = lean_ctor_get(x_3, 5);
x_13 = lean_ctor_get(x_3, 6);
x_14 = lean_ctor_get(x_3, 7);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_15 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0___redArg(x_13, x_1, x_2);
x_16 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_8);
lean_ctor_set(x_16, 2, x_9);
lean_ctor_set(x_16, 3, x_10);
lean_ctor_set(x_16, 4, x_11);
lean_ctor_set(x_16, 5, x_12);
lean_ctor_set(x_16, 6, x_15);
lean_ctor_set(x_16, 7, x_14);
return x_16;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget_borrowed(x_1, x_2);
x_7 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(2);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_usize_shift_right(x_2, x_6);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(x_17, x_18, x_3);
lean_dec_ref(x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*11 + 21);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; 
lean_free_object(x_13);
x_18 = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(x_2, x_10);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_20, 4);
lean_inc_ref(x_21);
lean_dec(x_20);
x_22 = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(x_21, x_1);
if (x_22 == 0)
{
lean_object* x_23; 
lean_free_object(x_18);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_23 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_free_object(x_23);
x_27 = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(x_2, x_10);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_29, 6);
lean_inc_ref(x_30);
lean_dec(x_29);
x_31 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(x_30, x_1);
if (lean_obj_tag(x_31) == 1)
{
lean_object* x_32; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
lean_ctor_set(x_27, 0, x_32);
return x_27;
}
else
{
lean_object* x_33; 
lean_dec(x_31);
lean_free_object(x_27);
lean_inc(x_2);
lean_inc_ref(x_1);
x_33 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
lean_inc(x_34);
x_35 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___lam__0), 3, 2);
lean_closure_set(x_35, 0, x_1);
lean_closure_set(x_35, 1, x_34);
x_36 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_37 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_36, x_35, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_34);
return x_37;
}
else
{
lean_object* x_40; 
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_34);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_34);
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_37, 0);
lean_inc(x_42);
lean_dec(x_37);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_33;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_27, 0);
lean_inc(x_44);
lean_dec(x_27);
x_45 = lean_ctor_get(x_44, 6);
lean_inc_ref(x_45);
lean_dec(x_44);
x_46 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(x_45, x_1);
if (lean_obj_tag(x_46) == 1)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
else
{
lean_object* x_49; 
lean_dec(x_46);
lean_inc(x_2);
lean_inc_ref(x_1);
x_49 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
lean_inc(x_50);
x_51 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___lam__0), 3, 2);
lean_closure_set(x_51, 0, x_1);
lean_closure_set(x_51, 1, x_50);
x_52 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_53 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_52, x_51, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_54 = x_53;
} else {
 lean_dec_ref(x_53);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 1, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_50);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_50);
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_57 = x_53;
} else {
 lean_dec_ref(x_53);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_56);
return x_58;
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_49;
}
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_59 = !lean_is_exclusive(x_27);
if (x_59 == 0)
{
return x_27;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_27, 0);
lean_inc(x_60);
lean_dec(x_27);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_62 = lean_box(0);
lean_ctor_set(x_23, 0, x_62);
return x_23;
}
}
else
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_23, 0);
lean_inc(x_63);
lean_dec(x_23);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(x_2, x_10);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = lean_ctor_get(x_66, 6);
lean_inc_ref(x_68);
lean_dec(x_66);
x_69 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(x_68, x_1);
if (lean_obj_tag(x_69) == 1)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
if (lean_is_scalar(x_67)) {
 x_71 = lean_alloc_ctor(0, 1, 0);
} else {
 x_71 = x_67;
}
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
else
{
lean_object* x_72; 
lean_dec(x_69);
lean_dec(x_67);
lean_inc(x_2);
lean_inc_ref(x_1);
x_72 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec_ref(x_72);
lean_inc(x_73);
x_74 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___lam__0), 3, 2);
lean_closure_set(x_74, 0, x_1);
lean_closure_set(x_74, 1, x_73);
x_75 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_76 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_75, x_74, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; 
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_77 = x_76;
} else {
 lean_dec_ref(x_76);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 1, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_73);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_73);
x_79 = lean_ctor_get(x_76, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_80 = x_76;
} else {
 lean_dec_ref(x_76);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 1, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_79);
return x_81;
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_72;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_82 = lean_ctor_get(x_65, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_83 = x_65;
} else {
 lean_dec_ref(x_65);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 1, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_82);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_87 = !lean_is_exclusive(x_23);
if (x_87 == 0)
{
return x_23;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_23, 0);
lean_inc(x_88);
lean_dec(x_23);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_90 = lean_box(0);
lean_ctor_set(x_18, 0, x_90);
return x_18;
}
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = lean_ctor_get(x_18, 0);
lean_inc(x_91);
lean_dec(x_18);
x_92 = lean_ctor_get(x_91, 4);
lean_inc_ref(x_92);
lean_dec(x_91);
x_93 = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(x_92, x_1);
if (x_93 == 0)
{
lean_object* x_94; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_94 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 x_96 = x_94;
} else {
 lean_dec_ref(x_94);
 x_96 = lean_box(0);
}
x_97 = lean_unbox(x_95);
lean_dec(x_95);
if (x_97 == 0)
{
lean_object* x_98; 
lean_dec(x_96);
x_98 = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(x_2, x_10);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_99, 6);
lean_inc_ref(x_101);
lean_dec(x_99);
x_102 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(x_101, x_1);
if (lean_obj_tag(x_102) == 1)
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec_ref(x_102);
if (lean_is_scalar(x_100)) {
 x_104 = lean_alloc_ctor(0, 1, 0);
} else {
 x_104 = x_100;
}
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
else
{
lean_object* x_105; 
lean_dec(x_102);
lean_dec(x_100);
lean_inc(x_2);
lean_inc_ref(x_1);
x_105 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec_ref(x_105);
lean_inc(x_106);
x_107 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___lam__0), 3, 2);
lean_closure_set(x_107, 0, x_1);
lean_closure_set(x_107, 1, x_106);
x_108 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_109 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_108, x_107, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 x_110 = x_109;
} else {
 lean_dec_ref(x_109);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(0, 1, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_106);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_106);
x_112 = lean_ctor_get(x_109, 0);
lean_inc(x_112);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 x_113 = x_109;
} else {
 lean_dec_ref(x_109);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 1, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_112);
return x_114;
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_105;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_115 = lean_ctor_get(x_98, 0);
lean_inc(x_115);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 x_116 = x_98;
} else {
 lean_dec_ref(x_98);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 1, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_115);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_118 = lean_box(0);
if (lean_is_scalar(x_96)) {
 x_119 = lean_alloc_ctor(0, 1, 0);
} else {
 x_119 = x_96;
}
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_120 = lean_ctor_get(x_94, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 x_121 = x_94;
} else {
 lean_dec_ref(x_94);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 1, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_120);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_123 = lean_box(0);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_125 = !lean_is_exclusive(x_18);
if (x_125 == 0)
{
return x_18;
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_18, 0);
lean_inc(x_126);
lean_dec(x_18);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
}
}
}
else
{
lean_object* x_128; uint8_t x_129; 
x_128 = lean_ctor_get(x_13, 0);
lean_inc(x_128);
lean_dec(x_13);
x_129 = lean_ctor_get_uint8(x_128, sizeof(void*)*11 + 21);
lean_dec(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_130 = lean_box(0);
x_131 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_131, 0, x_130);
return x_131;
}
else
{
lean_object* x_132; 
x_132 = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(x_2, x_10);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 x_134 = x_132;
} else {
 lean_dec_ref(x_132);
 x_134 = lean_box(0);
}
x_135 = lean_ctor_get(x_133, 4);
lean_inc_ref(x_135);
lean_dec(x_133);
x_136 = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(x_135, x_1);
if (x_136 == 0)
{
lean_object* x_137; 
lean_dec(x_134);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_137 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 x_139 = x_137;
} else {
 lean_dec_ref(x_137);
 x_139 = lean_box(0);
}
x_140 = lean_unbox(x_138);
lean_dec(x_138);
if (x_140 == 0)
{
lean_object* x_141; 
lean_dec(x_139);
x_141 = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(x_2, x_10);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
x_144 = lean_ctor_get(x_142, 6);
lean_inc_ref(x_144);
lean_dec(x_142);
x_145 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(x_144, x_1);
if (lean_obj_tag(x_145) == 1)
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
lean_dec_ref(x_145);
if (lean_is_scalar(x_143)) {
 x_147 = lean_alloc_ctor(0, 1, 0);
} else {
 x_147 = x_143;
}
lean_ctor_set(x_147, 0, x_146);
return x_147;
}
else
{
lean_object* x_148; 
lean_dec(x_145);
lean_dec(x_143);
lean_inc(x_2);
lean_inc_ref(x_1);
x_148 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
lean_dec_ref(x_148);
lean_inc(x_149);
x_150 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___lam__0), 3, 2);
lean_closure_set(x_150, 0, x_1);
lean_closure_set(x_150, 1, x_149);
x_151 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_152 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_151, x_150, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; 
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 x_153 = x_152;
} else {
 lean_dec_ref(x_152);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(0, 1, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_149);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_149);
x_155 = lean_ctor_get(x_152, 0);
lean_inc(x_155);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 x_156 = x_152;
} else {
 lean_dec_ref(x_152);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 1, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_155);
return x_157;
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_148;
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_158 = lean_ctor_get(x_141, 0);
lean_inc(x_158);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 x_159 = x_141;
} else {
 lean_dec_ref(x_141);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 1, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_158);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_161 = lean_box(0);
if (lean_is_scalar(x_139)) {
 x_162 = lean_alloc_ctor(0, 1, 0);
} else {
 x_162 = x_139;
}
lean_ctor_set(x_162, 0, x_161);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_163 = lean_ctor_get(x_137, 0);
lean_inc(x_163);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 x_164 = x_137;
} else {
 lean_dec_ref(x_137);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 1, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_163);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_166 = lean_box(0);
if (lean_is_scalar(x_134)) {
 x_167 = lean_alloc_ctor(0, 1, 0);
} else {
 x_167 = x_134;
}
lean_ctor_set(x_167, 0, x_166);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_168 = lean_ctor_get(x_132, 0);
lean_inc(x_168);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 x_169 = x_132;
} else {
 lean_dec_ref(x_132);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 1, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_168);
return x_170;
}
}
}
}
else
{
uint8_t x_171; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_171 = !lean_is_exclusive(x_13);
if (x_171 == 0)
{
return x_13;
}
else
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_13, 0);
lean_inc(x_172);
lean_dec(x_13);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_172);
return x_173;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
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
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__3);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2);
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__0();
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1();
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__2 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__4);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__5);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__6);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__7);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__20 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__20();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__20);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__43 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__43();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__43);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__45 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__45();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__45);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__12 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__12);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__13 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__13();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__13);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__15 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__15();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__15);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
