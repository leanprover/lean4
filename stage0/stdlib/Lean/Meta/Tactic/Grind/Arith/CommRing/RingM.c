// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
// Imports: public import Lean.Meta.Tactic.Grind.SynthInstance public import Lean.Meta.Tactic.Grind.Arith.CommRing.Types public import Lean.Meta.Sym.Arith.Functions public import Lean.Meta.Sym.Arith.MonadVar import Lean.Meta.Sym.Arith.Poly
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
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_degree(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getRing(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default;
lean_object* l_Array_rightpad___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getArithState___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Sym_Arith_arithExt;
lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__2(lean_object*, lean_object*);
lean_object* l_instMonadLiftT___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "ring polynomial degree "};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = " exceeds threshold `(ringMaxDegree := "};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ")`"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__1_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "`grind` internal error, invalid ringId"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "`grind` internal error, ring does not have a characteristic"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "expression in two different rings"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "`grind` internal error, ring term has not been internalized"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___boxed(lean_object**);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__1;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__3_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__4_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__5_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__7;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__8;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__9;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__10;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__11;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__12;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__13;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__14;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__15;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__16;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__17;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__18;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__19;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__20;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__21;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__22;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__23;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__24;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__25;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__26;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__27;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__28;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__29;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__30;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__31;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__32;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__33;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__34 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__34_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__35 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__35_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__36 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__36_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__37;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__38;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__39;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__40;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__41;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__42;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__43;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__44;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__45;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__46 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__46_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__46_value),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6_value)} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__47 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__47_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__48;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__49;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__50;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__51;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__52;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__53;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__54;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 49, 23, 61, 125, 46, 165, 129)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(lean_object* v_a_1_, lean_object* v_a_2_, lean_object* v_a_3_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1_, v_a_3_);
if (lean_obj_tag(v___x_5_) == 0)
{
lean_object* v_a_6_; lean_object* v___x_7_; 
v_a_6_ = lean_ctor_get(v___x_5_, 0);
lean_inc(v_a_6_);
lean_dec_ref_known(v___x_5_, 1);
v___x_7_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2_);
if (lean_obj_tag(v___x_7_) == 0)
{
lean_object* v_a_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_19_; 
v_a_8_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_19_ == 0)
{
v___x_10_ = v___x_7_;
v_isShared_11_ = v_isSharedCheck_19_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_a_8_);
lean_dec(v___x_7_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_19_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v_ringSteps_12_; lean_object* v_steps_13_; uint8_t v___x_14_; lean_object* v___x_15_; lean_object* v___x_17_; 
v_ringSteps_12_ = lean_ctor_get(v_a_8_, 6);
lean_inc(v_ringSteps_12_);
lean_dec(v_a_8_);
v_steps_13_ = lean_ctor_get(v_a_6_, 8);
lean_inc(v_steps_13_);
lean_dec(v_a_6_);
v___x_14_ = lean_nat_dec_le(v_ringSteps_12_, v_steps_13_);
lean_dec(v_steps_13_);
lean_dec(v_ringSteps_12_);
v___x_15_ = lean_box(v___x_14_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 0, v___x_15_);
v___x_17_ = v___x_10_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_27_; 
lean_dec(v_a_6_);
v_a_20_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_27_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_27_ == 0)
{
v___x_22_ = v___x_7_;
v_isShared_23_ = v_isSharedCheck_27_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_a_20_);
lean_dec(v___x_7_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_27_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_25_; 
if (v_isShared_23_ == 0)
{
v___x_25_ = v___x_22_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_a_20_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
return v___x_25_;
}
}
}
}
else
{
lean_object* v_a_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_35_; 
v_a_28_ = lean_ctor_get(v___x_5_, 0);
v_isSharedCheck_35_ = !lean_is_exclusive(v___x_5_);
if (v_isSharedCheck_35_ == 0)
{
v___x_30_ = v___x_5_;
v_isShared_31_ = v_isSharedCheck_35_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_a_28_);
lean_dec(v___x_5_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_35_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___x_33_; 
if (v_isShared_31_ == 0)
{
v___x_33_ = v___x_30_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v_a_28_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_res_36_;
v_res_36_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(v_a_1_, v_a_2_, v_a_3_);
stack->m_obj
 = v_res_36_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg___boxed(lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(v_a_37_, v_a_38_, v_a_39_);
lean_dec_ref(v_a_39_);
lean_dec_ref(v_a_38_);
lean_dec(v_a_37_);
return v_res_41_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps(lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(v_a_42_, v_a_44_, v_a_50_);
return v___x_53_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_42_ = stack[0].m_obj;
lean_object* v_a_43_ = stack[1].m_obj;
lean_object* v_a_44_ = stack[2].m_obj;
lean_object* v_a_45_ = stack[3].m_obj;
lean_object* v_a_46_ = stack[4].m_obj;
lean_object* v_a_47_ = stack[5].m_obj;
lean_object* v_a_48_ = stack[6].m_obj;
lean_object* v_a_49_ = stack[7].m_obj;
lean_object* v_a_50_ = stack[8].m_obj;
lean_object* v_a_51_ = stack[9].m_obj;
lean_object* v_res_54_;
v_res_54_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps(v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_);
stack->m_obj
 = v_res_54_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___boxed(lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps(v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_);
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
lean_dec(v_a_58_);
lean_dec_ref(v_a_57_);
lean_dec(v_a_56_);
lean_dec(v_a_55_);
return v_res_66_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0(uint8_t v___x_67_, lean_object* v_s_68_){
_start:
{
lean_object* v_rings_69_; lean_object* v_exprToRingId_70_; lean_object* v_semirings_71_; lean_object* v_exprToSemiringId_72_; lean_object* v_ncRings_73_; lean_object* v_exprToNCRingId_74_; lean_object* v_ncSemirings_75_; lean_object* v_exprToNCSemiringId_76_; lean_object* v_steps_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_84_; 
v_rings_69_ = lean_ctor_get(v_s_68_, 0);
v_exprToRingId_70_ = lean_ctor_get(v_s_68_, 1);
v_semirings_71_ = lean_ctor_get(v_s_68_, 2);
v_exprToSemiringId_72_ = lean_ctor_get(v_s_68_, 3);
v_ncRings_73_ = lean_ctor_get(v_s_68_, 4);
v_exprToNCRingId_74_ = lean_ctor_get(v_s_68_, 5);
v_ncSemirings_75_ = lean_ctor_get(v_s_68_, 6);
v_exprToNCSemiringId_76_ = lean_ctor_get(v_s_68_, 7);
v_steps_77_ = lean_ctor_get(v_s_68_, 8);
v_isSharedCheck_84_ = !lean_is_exclusive(v_s_68_);
if (v_isSharedCheck_84_ == 0)
{
v___x_79_ = v_s_68_;
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_steps_77_);
lean_inc(v_exprToNCSemiringId_76_);
lean_inc(v_ncSemirings_75_);
lean_inc(v_exprToNCRingId_74_);
lean_inc(v_ncRings_73_);
lean_inc(v_exprToSemiringId_72_);
lean_inc(v_semirings_71_);
lean_inc(v_exprToRingId_70_);
lean_inc(v_rings_69_);
lean_dec(v_s_68_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_82_; 
if (v_isShared_80_ == 0)
{
v___x_82_ = v___x_79_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_rings_69_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v_exprToRingId_70_);
lean_ctor_set(v_reuseFailAlloc_83_, 2, v_semirings_71_);
lean_ctor_set(v_reuseFailAlloc_83_, 3, v_exprToSemiringId_72_);
lean_ctor_set(v_reuseFailAlloc_83_, 4, v_ncRings_73_);
lean_ctor_set(v_reuseFailAlloc_83_, 5, v_exprToNCRingId_74_);
lean_ctor_set(v_reuseFailAlloc_83_, 6, v_ncSemirings_75_);
lean_ctor_set(v_reuseFailAlloc_83_, 7, v_exprToNCSemiringId_76_);
lean_ctor_set(v_reuseFailAlloc_83_, 8, v_steps_77_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*9, v___x_67_);
return v___x_82_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_67_ = stack[0].m_num;
lean_object* v_s_68_ = stack[1].m_obj;
lean_object* v_res_85_;
v_res_85_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0(v___x_67_, v_s_68_);
stack->m_obj
 = v_res_85_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0___boxed(lean_object* v___x_86_, lean_object* v_s_87_){
_start:
{
uint8_t v___x_5932__boxed_88_; lean_object* v_res_89_; 
v___x_5932__boxed_88_ = lean_unbox(v___x_86_);
v_res_89_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0(v___x_5932__boxed_88_, v_s_87_);
return v_res_89_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__0));
v___x_92_ = l_Lean_stringToMessageData(v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__2));
v___x_95_ = l_Lean_stringToMessageData(v___x_94_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__4));
v___x_98_ = l_Lean_stringToMessageData(v___x_97_);
return v___x_98_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg(lean_object* v_p_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_101_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_199_; 
v_a_110_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_199_ == 0)
{
v___x_112_ = v___x_109_;
v_isShared_113_ = v_isSharedCheck_199_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_109_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_199_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v_ringMaxDegree_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v_ringMaxDegree_114_ = lean_ctor_get(v_a_110_, 7);
lean_inc(v_ringMaxDegree_114_);
lean_dec(v_a_110_);
v___x_115_ = l_Lean_Grind_CommRing_Poly_degree(v_p_99_);
v___x_116_ = lean_nat_dec_le(v_ringMaxDegree_114_, v___x_115_);
lean_dec(v_ringMaxDegree_114_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; lean_object* v___x_119_; 
lean_dec(v___x_115_);
v___x_117_ = lean_box(v___x_116_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 0, v___x_117_);
v___x_119_ = v___x_112_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_117_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
else
{
lean_object* v___x_121_; lean_object* v___f_122_; lean_object* v___x_123_; 
lean_del_object(v___x_112_);
v___x_121_ = lean_box(v___x_116_);
v___f_122_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_122_, 0, v___x_121_);
v___x_123_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_100_, v_a_106_);
if (lean_obj_tag(v___x_123_) == 0)
{
lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_190_; 
v_a_124_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_190_ == 0)
{
v___x_126_ = v___x_123_;
v_isShared_127_ = v_isSharedCheck_190_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___x_123_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_190_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
uint8_t v_reportedMaxDegreeIssue_128_; 
v_reportedMaxDegreeIssue_128_ = lean_ctor_get_uint8(v_a_124_, sizeof(void*)*9);
lean_dec(v_a_124_);
if (v_reportedMaxDegreeIssue_128_ == 0)
{
lean_object* v___x_129_; lean_object* v___x_130_; 
lean_del_object(v___x_126_);
v___x_129_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_130_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_129_, v___f_122_, v_a_100_);
if (lean_obj_tag(v___x_130_) == 0)
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
lean_dec_ref_known(v___x_130_, 1);
v___x_131_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1);
v___x_132_ = l_Nat_reprFast(v___x_115_);
v___x_133_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
v___x_134_ = l_Lean_MessageData_ofFormat(v___x_133_);
lean_inc_ref(v___x_134_);
v___x_135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_131_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
v___x_136_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3, &l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3);
v___x_137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_135_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v___x_138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v___x_134_);
v___x_139_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5, &l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5);
v___x_140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_138_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
v___x_141_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_102_);
if (lean_obj_tag(v___x_141_) == 0)
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_169_; 
v_a_142_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_169_ == 0)
{
v___x_144_ = v___x_141_;
v_isShared_145_ = v_isSharedCheck_169_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_141_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_169_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
uint8_t v_verbose_146_; 
v_verbose_146_ = lean_ctor_get_uint8(v_a_142_, 0);
lean_dec(v_a_142_);
if (v_verbose_146_ == 0)
{
lean_object* v___x_147_; lean_object* v___x_149_; 
lean_dec_ref_known(v___x_140_, 2);
v___x_147_ = lean_box(v___x_116_);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 0, v___x_147_);
v___x_149_ = v___x_144_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_147_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
else
{
lean_object* v___x_151_; 
lean_del_object(v___x_144_);
v___x_151_ = l_Lean_Meta_Sym_reportIssue(v___x_140_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_159_; 
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_159_ == 0)
{
lean_object* v_unused_160_; 
v_unused_160_ = lean_ctor_get(v___x_151_, 0);
lean_dec(v_unused_160_);
v___x_153_ = v___x_151_;
v_isShared_154_ = v_isSharedCheck_159_;
goto v_resetjp_152_;
}
else
{
lean_dec(v___x_151_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_159_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v___x_157_; 
v___x_155_ = lean_box(v___x_116_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 0, v___x_155_);
v___x_157_ = v___x_153_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_155_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
else
{
lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_168_; 
v_a_161_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_168_ == 0)
{
v___x_163_ = v___x_151_;
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_151_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_166_; 
if (v_isShared_164_ == 0)
{
v___x_166_ = v___x_163_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_a_161_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
}
}
else
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
lean_dec_ref_known(v___x_140_, 2);
v_a_170_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_177_ == 0)
{
v___x_172_ = v___x_141_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_141_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_a_170_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
else
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_185_; 
lean_dec(v___x_115_);
v_a_178_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_185_ == 0)
{
v___x_180_ = v___x_130_;
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_130_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_183_; 
if (v_isShared_181_ == 0)
{
v___x_183_ = v___x_180_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_a_178_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
else
{
lean_object* v___x_186_; lean_object* v___x_188_; 
lean_dec_ref(v___f_122_);
lean_dec(v___x_115_);
v___x_186_ = lean_box(v___x_116_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 0, v___x_186_);
v___x_188_ = v___x_126_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_186_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
else
{
lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_198_; 
lean_dec_ref(v___f_122_);
lean_dec(v___x_115_);
v_a_191_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_198_ == 0)
{
v___x_193_ = v___x_123_;
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_dec(v___x_123_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
if (v_isShared_194_ == 0)
{
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_a_191_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
}
}
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
v_a_200_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_109_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_109_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_99_ = stack[0].m_obj;
lean_object* v_a_100_ = stack[1].m_obj;
lean_object* v_a_101_ = stack[2].m_obj;
lean_object* v_a_102_ = stack[3].m_obj;
lean_object* v_a_103_ = stack[4].m_obj;
lean_object* v_a_104_ = stack[5].m_obj;
lean_object* v_a_105_ = stack[6].m_obj;
lean_object* v_a_106_ = stack[7].m_obj;
lean_object* v_a_107_ = stack[8].m_obj;
lean_object* v_res_208_;
v_res_208_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg(v_p_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
stack->m_obj
 = v_res_208_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___boxed(lean_object* v_p_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg(v_p_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_212_);
lean_dec_ref(v_a_211_);
lean_dec(v_a_210_);
lean_dec_ref(v_p_209_);
return v_res_219_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree(lean_object* v_p_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg(v_p_220_, v_a_221_, v_a_223_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
return v___x_232_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_220_ = stack[0].m_obj;
lean_object* v_a_221_ = stack[1].m_obj;
lean_object* v_a_222_ = stack[2].m_obj;
lean_object* v_a_223_ = stack[3].m_obj;
lean_object* v_a_224_ = stack[4].m_obj;
lean_object* v_a_225_ = stack[5].m_obj;
lean_object* v_a_226_ = stack[6].m_obj;
lean_object* v_a_227_ = stack[7].m_obj;
lean_object* v_a_228_ = stack[8].m_obj;
lean_object* v_a_229_ = stack[9].m_obj;
lean_object* v_a_230_ = stack[10].m_obj;
lean_object* v_res_233_;
v_res_233_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree(v_p_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
stack->m_obj
 = v_res_233_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___boxed(lean_object* v_p_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree(v_p_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
lean_dec(v_a_240_);
lean_dec_ref(v_a_239_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec(v_a_236_);
lean_dec(v_a_235_);
lean_dec_ref(v_p_234_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0(lean_object* v_n_247_, lean_object* v_s_248_){
_start:
{
lean_object* v_rings_249_; lean_object* v_exprToRingId_250_; lean_object* v_semirings_251_; lean_object* v_exprToSemiringId_252_; lean_object* v_ncRings_253_; lean_object* v_exprToNCRingId_254_; lean_object* v_ncSemirings_255_; lean_object* v_exprToNCSemiringId_256_; lean_object* v_steps_257_; uint8_t v_reportedMaxDegreeIssue_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_266_; 
v_rings_249_ = lean_ctor_get(v_s_248_, 0);
v_exprToRingId_250_ = lean_ctor_get(v_s_248_, 1);
v_semirings_251_ = lean_ctor_get(v_s_248_, 2);
v_exprToSemiringId_252_ = lean_ctor_get(v_s_248_, 3);
v_ncRings_253_ = lean_ctor_get(v_s_248_, 4);
v_exprToNCRingId_254_ = lean_ctor_get(v_s_248_, 5);
v_ncSemirings_255_ = lean_ctor_get(v_s_248_, 6);
v_exprToNCSemiringId_256_ = lean_ctor_get(v_s_248_, 7);
v_steps_257_ = lean_ctor_get(v_s_248_, 8);
v_reportedMaxDegreeIssue_258_ = lean_ctor_get_uint8(v_s_248_, sizeof(void*)*9);
v_isSharedCheck_266_ = !lean_is_exclusive(v_s_248_);
if (v_isSharedCheck_266_ == 0)
{
v___x_260_ = v_s_248_;
v_isShared_261_ = v_isSharedCheck_266_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_steps_257_);
lean_inc(v_exprToNCSemiringId_256_);
lean_inc(v_ncSemirings_255_);
lean_inc(v_exprToNCRingId_254_);
lean_inc(v_ncRings_253_);
lean_inc(v_exprToSemiringId_252_);
lean_inc(v_semirings_251_);
lean_inc(v_exprToRingId_250_);
lean_inc(v_rings_249_);
lean_dec(v_s_248_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_266_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_262_ = lean_nat_add(v_steps_257_, v_n_247_);
lean_dec(v_steps_257_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 8, v___x_262_);
v___x_264_ = v___x_260_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_rings_249_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_exprToRingId_250_);
lean_ctor_set(v_reuseFailAlloc_265_, 2, v_semirings_251_);
lean_ctor_set(v_reuseFailAlloc_265_, 3, v_exprToSemiringId_252_);
lean_ctor_set(v_reuseFailAlloc_265_, 4, v_ncRings_253_);
lean_ctor_set(v_reuseFailAlloc_265_, 5, v_exprToNCRingId_254_);
lean_ctor_set(v_reuseFailAlloc_265_, 6, v_ncSemirings_255_);
lean_ctor_set(v_reuseFailAlloc_265_, 7, v_exprToNCSemiringId_256_);
lean_ctor_set(v_reuseFailAlloc_265_, 8, v___x_262_);
lean_ctor_set_uint8(v_reuseFailAlloc_265_, sizeof(void*)*9, v_reportedMaxDegreeIssue_258_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0___boxed(lean_object* v_n_267_, lean_object* v_s_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0(v_n_267_, v_s_268_);
lean_dec(v_n_267_);
return v_res_269_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(lean_object* v_n_270_, lean_object* v_a_271_){
_start:
{
lean_object* v___f_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___f_273_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_273_, 0, v_n_270_);
v___x_274_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_275_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_274_, v___f_273_, v_a_271_);
return v___x_275_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_270_ = stack[0].m_obj;
lean_object* v_a_271_ = stack[1].m_obj;
lean_object* v_res_276_;
v_res_276_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v_n_270_, v_a_271_);
stack->m_obj
 = v_res_276_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___boxed(lean_object* v_n_277_, lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v_n_277_, v_a_278_);
lean_dec(v_a_278_);
return v_res_280_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps(lean_object* v_n_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v_n_281_, v_a_282_);
return v___x_293_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_incSteps_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_281_ = stack[0].m_obj;
lean_object* v_a_282_ = stack[1].m_obj;
lean_object* v_a_283_ = stack[2].m_obj;
lean_object* v_a_284_ = stack[3].m_obj;
lean_object* v_a_285_ = stack[4].m_obj;
lean_object* v_a_286_ = stack[5].m_obj;
lean_object* v_a_287_ = stack[6].m_obj;
lean_object* v_a_288_ = stack[7].m_obj;
lean_object* v_a_289_ = stack[8].m_obj;
lean_object* v_a_290_ = stack[9].m_obj;
lean_object* v_a_291_ = stack[10].m_obj;
lean_object* v_res_294_;
v_res_294_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps(v_n_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
stack->m_obj
 = v_res_294_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___boxed(lean_object* v_n_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps(v_n_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
lean_dec(v_a_297_);
lean_dec(v_a_296_);
return v_res_307_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg(lean_object* v_ringId_308_, lean_object* v_x_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
uint8_t v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_321_ = 0;
v___x_322_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_322_, 0, v_ringId_308_);
lean_ctor_set_uint8(v___x_322_, sizeof(void*)*1, v___x_321_);
lean_inc(v_a_319_);
lean_inc_ref(v_a_318_);
lean_inc(v_a_317_);
lean_inc_ref(v_a_316_);
lean_inc(v_a_315_);
lean_inc_ref(v_a_314_);
lean_inc(v_a_313_);
lean_inc_ref(v_a_312_);
lean_inc(v_a_311_);
lean_inc(v_a_310_);
v___x_323_ = lean_apply_12(v_x_309_, v___x_322_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, lean_box(0));
return v___x_323_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ringId_308_ = stack[0].m_obj;
lean_object* v_x_309_ = stack[1].m_obj;
lean_object* v_a_310_ = stack[2].m_obj;
lean_object* v_a_311_ = stack[3].m_obj;
lean_object* v_a_312_ = stack[4].m_obj;
lean_object* v_a_313_ = stack[5].m_obj;
lean_object* v_a_314_ = stack[6].m_obj;
lean_object* v_a_315_ = stack[7].m_obj;
lean_object* v_a_316_ = stack[8].m_obj;
lean_object* v_a_317_ = stack[9].m_obj;
lean_object* v_a_318_ = stack[10].m_obj;
lean_object* v_a_319_ = stack[11].m_obj;
lean_object* v_res_324_;
v_res_324_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg(v_ringId_308_, v_x_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
stack->m_obj
 = v_res_324_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg___boxed(lean_object* v_ringId_325_, lean_object* v_x_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg(v_ringId_325_, v_x_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec(v_a_327_);
return v_res_338_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run(lean_object* v_00_u03b1_339_, lean_object* v_ringId_340_, lean_object* v_x_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
uint8_t v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_353_ = 0;
v___x_354_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_354_, 0, v_ringId_340_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*1, v___x_353_);
lean_inc(v_a_351_);
lean_inc_ref(v_a_350_);
lean_inc(v_a_349_);
lean_inc_ref(v_a_348_);
lean_inc(v_a_347_);
lean_inc_ref(v_a_346_);
lean_inc(v_a_345_);
lean_inc_ref(v_a_344_);
lean_inc(v_a_343_);
lean_inc(v_a_342_);
v___x_355_ = lean_apply_12(v_x_341_, v___x_354_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, lean_box(0));
return v___x_355_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_RingM_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_ringId_340_ = stack[1].m_obj;
lean_object* v_x_341_ = stack[2].m_obj;
lean_object* v_a_342_ = stack[3].m_obj;
lean_object* v_a_343_ = stack[4].m_obj;
lean_object* v_a_344_ = stack[5].m_obj;
lean_object* v_a_345_ = stack[6].m_obj;
lean_object* v_a_346_ = stack[7].m_obj;
lean_object* v_a_347_ = stack[8].m_obj;
lean_object* v_a_348_ = stack[9].m_obj;
lean_object* v_a_349_ = stack[10].m_obj;
lean_object* v_a_350_ = stack[11].m_obj;
lean_object* v_a_351_ = stack[12].m_obj;
lean_object* v_res_356_;
v_res_356_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_run(lean_box(0), v_ringId_340_, v_x_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
stack->m_obj
 = v_res_356_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___boxed(lean_object* v_00_u03b1_357_, lean_object* v_ringId_358_, lean_object* v_x_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_run(v_00_u03b1_357_, v_ringId_358_, v_x_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
lean_dec(v_a_361_);
lean_dec(v_a_360_);
return v_res_371_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg(lean_object* v_a_372_){
_start:
{
lean_object* v_ringId_374_; lean_object* v___x_375_; 
v_ringId_374_ = lean_ctor_get(v_a_372_, 0);
lean_inc(v_ringId_374_);
v___x_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_375_, 0, v_ringId_374_);
return v___x_375_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_372_ = stack[0].m_obj;
lean_object* v_res_376_;
v_res_376_ = l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg(v_a_372_);
stack->m_obj
 = v_res_376_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg___boxed(lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg(v_a_377_);
lean_dec_ref(v_a_377_);
return v_res_379_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId(lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_){
_start:
{
lean_object* v_ringId_392_; lean_object* v___x_393_; 
v_ringId_392_ = lean_ctor_get(v_a_380_, 0);
lean_inc(v_ringId_392_);
v___x_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_393_, 0, v_ringId_392_);
return v___x_393_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_getRingId_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_380_ = stack[0].m_obj;
lean_object* v_a_381_ = stack[1].m_obj;
lean_object* v_a_382_ = stack[2].m_obj;
lean_object* v_a_383_ = stack[3].m_obj;
lean_object* v_a_384_ = stack[4].m_obj;
lean_object* v_a_385_ = stack[5].m_obj;
lean_object* v_a_386_ = stack[6].m_obj;
lean_object* v_a_387_ = stack[7].m_obj;
lean_object* v_a_388_ = stack[8].m_obj;
lean_object* v_a_389_ = stack[9].m_obj;
lean_object* v_a_390_ = stack[10].m_obj;
lean_object* v_res_394_;
v_res_394_ = l_Lean_Meta_Grind_Arith_CommRing_getRingId(v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
stack->m_obj
 = v_res_394_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___boxed(lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_Meta_Grind_Arith_CommRing_getRingId(v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
lean_dec(v_a_397_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
return v_res_407_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0(lean_object* v_e_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_Meta_Sym_canon(v_e_408_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_a_422_; lean_object* v___x_423_; 
v_a_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_a_422_);
lean_dec_ref_known(v___x_421_, 1);
v___x_423_ = l_Lean_Meta_Sym_shareCommon(v_a_422_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
return v___x_423_;
}
else
{
return v___x_421_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_408_ = stack[0].m_obj;
lean_object* v___y_409_ = stack[1].m_obj;
lean_object* v___y_410_ = stack[2].m_obj;
lean_object* v___y_411_ = stack[3].m_obj;
lean_object* v___y_412_ = stack[4].m_obj;
lean_object* v___y_413_ = stack[5].m_obj;
lean_object* v___y_414_ = stack[6].m_obj;
lean_object* v___y_415_ = stack[7].m_obj;
lean_object* v___y_416_ = stack[8].m_obj;
lean_object* v___y_417_ = stack[9].m_obj;
lean_object* v___y_418_ = stack[10].m_obj;
lean_object* v___y_419_ = stack[11].m_obj;
lean_object* v_res_424_;
v_res_424_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0(v_e_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
stack->m_obj
 = v_res_424_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0___boxed(lean_object* v_e_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0(v_e_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec(v___y_428_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
return v_res_438_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1(lean_object* v_e_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_e_439_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
return v___x_452_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_439_ = stack[0].m_obj;
lean_object* v___y_440_ = stack[1].m_obj;
lean_object* v___y_441_ = stack[2].m_obj;
lean_object* v___y_442_ = stack[3].m_obj;
lean_object* v___y_443_ = stack[4].m_obj;
lean_object* v___y_444_ = stack[5].m_obj;
lean_object* v___y_445_ = stack[6].m_obj;
lean_object* v___y_446_ = stack[7].m_obj;
lean_object* v___y_447_ = stack[8].m_obj;
lean_object* v___y_448_ = stack[9].m_obj;
lean_object* v___y_449_ = stack[10].m_obj;
lean_object* v___y_450_ = stack[11].m_obj;
lean_object* v_res_453_;
v_res_453_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1(v_e_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
stack->m_obj
 = v_res_453_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1___boxed(lean_object* v_e_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1(v_e_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
return v_res_467_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(lean_object* v_msgData_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v___x_480_; lean_object* v_env_481_; uint8_t v___x_482_; lean_object* v_env_483_; lean_object* v___x_484_; lean_object* v_toCold_485_; lean_object* v_mctx_486_; lean_object* v_lctx_487_; lean_object* v_options_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_480_ = lean_st_ref_get(v___y_478_);
v_env_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc_ref(v_env_481_);
lean_dec(v___x_480_);
v___x_482_ = 0;
v_env_483_ = l_Lean_Environment_setRecordingDeps(v_env_481_, v___x_482_);
v___x_484_ = lean_st_ref_get(v___y_476_);
v_toCold_485_ = lean_ctor_get(v___y_477_, 0);
v_mctx_486_ = lean_ctor_get(v___x_484_, 0);
lean_inc_ref(v_mctx_486_);
lean_dec(v___x_484_);
v_lctx_487_ = lean_ctor_get(v___y_475_, 2);
v_options_488_ = lean_ctor_get(v_toCold_485_, 2);
lean_inc_ref(v_options_488_);
lean_inc_ref(v_lctx_487_);
v___x_489_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_489_, 0, v_env_483_);
lean_ctor_set(v___x_489_, 1, v_mctx_486_);
lean_ctor_set(v___x_489_, 2, v_lctx_487_);
lean_ctor_set(v___x_489_, 3, v_options_488_);
v___x_490_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v_msgData_474_);
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_474_ = stack[0].m_obj;
lean_object* v___y_475_ = stack[1].m_obj;
lean_object* v___y_476_ = stack[2].m_obj;
lean_object* v___y_477_ = stack[3].m_obj;
lean_object* v___y_478_ = stack[4].m_obj;
lean_object* v_res_492_;
v_res_492_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(v_msgData_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
stack->m_obj
 = v_res_492_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0___boxed(lean_object* v_msgData_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(v_msgData_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
return v_res_499_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(lean_object* v_msg_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_ref_506_; lean_object* v___x_507_; lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_516_; 
v_ref_506_ = lean_ctor_get(v___y_503_, 2);
v___x_507_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(v_msg_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
v_a_508_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_516_ == 0)
{
v___x_510_ = v___x_507_;
v_isShared_511_ = v_isSharedCheck_516_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_507_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_516_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; lean_object* v___x_514_; 
lean_inc(v_ref_506_);
v___x_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_512_, 0, v_ref_506_);
lean_ctor_set(v___x_512_, 1, v_a_508_);
if (v_isShared_511_ == 0)
{
lean_ctor_set_tag(v___x_510_, 1);
lean_ctor_set(v___x_510_, 0, v___x_512_);
v___x_514_ = v___x_510_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_512_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_500_ = stack[0].m_obj;
lean_object* v___y_501_ = stack[1].m_obj;
lean_object* v___y_502_ = stack[2].m_obj;
lean_object* v___y_503_ = stack[3].m_obj;
lean_object* v___y_504_ = stack[4].m_obj;
lean_object* v_res_517_;
v_res_517_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v_msg_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
stack->m_obj
 = v_res_517_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg___boxed(lean_object* v_msg_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v_msg_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
return v_res_524_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__0));
v___x_527_ = l_Lean_stringToMessageData(v___x_526_);
return v___x_527_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_534_, v_a_537_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_555_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_555_ == 0)
{
v___x_543_ = v___x_540_;
v_isShared_544_ = v_isSharedCheck_555_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_540_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_555_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v_ringId_545_; lean_object* v_rings_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v_ringId_545_ = lean_ctor_get(v_a_528_, 0);
v_rings_546_ = lean_ctor_get(v_a_541_, 1);
lean_inc_ref(v_rings_546_);
lean_dec(v_a_541_);
v___x_547_ = lean_array_get_size(v_rings_546_);
v___x_548_ = lean_nat_dec_lt(v_ringId_545_, v___x_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; 
lean_dec_ref(v_rings_546_);
lean_del_object(v___x_543_);
v___x_549_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1);
v___x_550_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v___x_549_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
return v___x_550_;
}
else
{
lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_551_ = lean_array_fget(v_rings_546_, v_ringId_545_);
lean_dec_ref(v_rings_546_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_551_);
v___x_553_ = v___x_543_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
v_a_556_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_540_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_540_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_528_ = stack[0].m_obj;
lean_object* v_a_529_ = stack[1].m_obj;
lean_object* v_a_530_ = stack[2].m_obj;
lean_object* v_a_531_ = stack[3].m_obj;
lean_object* v_a_532_ = stack[4].m_obj;
lean_object* v_a_533_ = stack[5].m_obj;
lean_object* v_a_534_ = stack[6].m_obj;
lean_object* v_a_535_ = stack[7].m_obj;
lean_object* v_a_536_ = stack[8].m_obj;
lean_object* v_a_537_ = stack[9].m_obj;
lean_object* v_a_538_ = stack[10].m_obj;
lean_object* v_res_564_;
v_res_564_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
stack->m_obj
 = v_res_564_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___boxed(lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
lean_dec(v_a_573_);
lean_dec_ref(v_a_572_);
lean_dec(v_a_571_);
lean_dec_ref(v_a_570_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
lean_dec(v_a_567_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
return v_res_577_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0(lean_object* v_00_u03b1_578_, lean_object* v_msg_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v_msg_579_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
return v___x_592_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_579_ = stack[1].m_obj;
lean_object* v___y_580_ = stack[2].m_obj;
lean_object* v___y_581_ = stack[3].m_obj;
lean_object* v___y_582_ = stack[4].m_obj;
lean_object* v___y_583_ = stack[5].m_obj;
lean_object* v___y_584_ = stack[6].m_obj;
lean_object* v___y_585_ = stack[7].m_obj;
lean_object* v___y_586_ = stack[8].m_obj;
lean_object* v___y_587_ = stack[9].m_obj;
lean_object* v___y_588_ = stack[10].m_obj;
lean_object* v___y_589_ = stack[11].m_obj;
lean_object* v___y_590_ = stack[12].m_obj;
lean_object* v_res_593_;
v_res_593_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0(lean_box(0), v_msg_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
stack->m_obj
 = v_res_593_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___boxed(lean_object* v_00_u03b1_594_, lean_object* v_msg_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0(v_00_u03b1_594_, v_msg_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0(lean_object* v_ringId_609_, lean_object* v_f_610_, lean_object* v_s_611_){
_start:
{
lean_object* v_exp_612_; lean_object* v_rings_613_; lean_object* v_semirings_614_; lean_object* v_ncRings_615_; lean_object* v_ncSemirings_616_; lean_object* v_typeClassify_617_; lean_object* v_orders_618_; lean_object* v_typeOrderClassify_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v_exp_612_ = lean_ctor_get(v_s_611_, 0);
v_rings_613_ = lean_ctor_get(v_s_611_, 1);
v_semirings_614_ = lean_ctor_get(v_s_611_, 2);
v_ncRings_615_ = lean_ctor_get(v_s_611_, 3);
v_ncSemirings_616_ = lean_ctor_get(v_s_611_, 4);
v_typeClassify_617_ = lean_ctor_get(v_s_611_, 5);
v_orders_618_ = lean_ctor_get(v_s_611_, 6);
v_typeOrderClassify_619_ = lean_ctor_get(v_s_611_, 7);
v___x_620_ = lean_array_get_size(v_rings_613_);
v___x_621_ = lean_nat_dec_lt(v_ringId_609_, v___x_620_);
if (v___x_621_ == 0)
{
lean_dec_ref(v_f_610_);
return v_s_611_;
}
else
{
lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_633_; 
lean_inc_ref(v_typeOrderClassify_619_);
lean_inc_ref(v_orders_618_);
lean_inc_ref(v_typeClassify_617_);
lean_inc_ref(v_ncSemirings_616_);
lean_inc_ref(v_ncRings_615_);
lean_inc_ref(v_semirings_614_);
lean_inc_ref(v_rings_613_);
lean_inc(v_exp_612_);
v_isSharedCheck_633_ = !lean_is_exclusive(v_s_611_);
if (v_isSharedCheck_633_ == 0)
{
lean_object* v_unused_634_; lean_object* v_unused_635_; lean_object* v_unused_636_; lean_object* v_unused_637_; lean_object* v_unused_638_; lean_object* v_unused_639_; lean_object* v_unused_640_; lean_object* v_unused_641_; 
v_unused_634_ = lean_ctor_get(v_s_611_, 7);
lean_dec(v_unused_634_);
v_unused_635_ = lean_ctor_get(v_s_611_, 6);
lean_dec(v_unused_635_);
v_unused_636_ = lean_ctor_get(v_s_611_, 5);
lean_dec(v_unused_636_);
v_unused_637_ = lean_ctor_get(v_s_611_, 4);
lean_dec(v_unused_637_);
v_unused_638_ = lean_ctor_get(v_s_611_, 3);
lean_dec(v_unused_638_);
v_unused_639_ = lean_ctor_get(v_s_611_, 2);
lean_dec(v_unused_639_);
v_unused_640_ = lean_ctor_get(v_s_611_, 1);
lean_dec(v_unused_640_);
v_unused_641_ = lean_ctor_get(v_s_611_, 0);
lean_dec(v_unused_641_);
v___x_623_ = v_s_611_;
v_isShared_624_ = v_isSharedCheck_633_;
goto v_resetjp_622_;
}
else
{
lean_dec(v_s_611_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_633_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v_v_625_; lean_object* v___x_626_; lean_object* v_xs_x27_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_631_; 
v_v_625_ = lean_array_fget(v_rings_613_, v_ringId_609_);
v___x_626_ = lean_box(0);
v_xs_x27_627_ = lean_array_fset(v_rings_613_, v_ringId_609_, v___x_626_);
v___x_628_ = lean_apply_1(v_f_610_, v_v_625_);
v___x_629_ = lean_array_fset(v_xs_x27_627_, v_ringId_609_, v___x_628_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 1, v___x_629_);
v___x_631_ = v___x_623_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_exp_612_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v_semirings_614_);
lean_ctor_set(v_reuseFailAlloc_632_, 3, v_ncRings_615_);
lean_ctor_set(v_reuseFailAlloc_632_, 4, v_ncSemirings_616_);
lean_ctor_set(v_reuseFailAlloc_632_, 5, v_typeClassify_617_);
lean_ctor_set(v_reuseFailAlloc_632_, 6, v_orders_618_);
lean_ctor_set(v_reuseFailAlloc_632_, 7, v_typeOrderClassify_619_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0___boxed(lean_object* v_ringId_642_, lean_object* v_f_643_, lean_object* v_s_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0(v_ringId_642_, v_f_643_, v_s_644_);
lean_dec(v_ringId_642_);
return v_res_645_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(lean_object* v_f_646_, lean_object* v_a_647_, lean_object* v_a_648_){
_start:
{
lean_object* v_ringId_650_; lean_object* v___f_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v_ringId_650_ = lean_ctor_get(v_a_647_, 0);
lean_inc(v_ringId_650_);
v___f_651_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_651_, 0, v_ringId_650_);
lean_closure_set(v___f_651_, 1, v_f_646_);
v___x_652_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_653_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_652_, v___f_651_, v_a_648_);
return v___x_653_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_646_ = stack[0].m_obj;
lean_object* v_a_647_ = stack[1].m_obj;
lean_object* v_a_648_ = stack[2].m_obj;
lean_object* v_res_654_;
v_res_654_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v_f_646_, v_a_647_, v_a_648_);
stack->m_obj
 = v_res_654_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___boxed(lean_object* v_f_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v_f_655_, v_a_656_, v_a_657_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
return v_res_659_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing(lean_object* v_f_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v_f_660_, v_a_661_, v_a_667_);
return v___x_673_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_660_ = stack[0].m_obj;
lean_object* v_a_661_ = stack[1].m_obj;
lean_object* v_a_662_ = stack[2].m_obj;
lean_object* v_a_663_ = stack[3].m_obj;
lean_object* v_a_664_ = stack[4].m_obj;
lean_object* v_a_665_ = stack[5].m_obj;
lean_object* v_a_666_ = stack[6].m_obj;
lean_object* v_a_667_ = stack[7].m_obj;
lean_object* v_a_668_ = stack[8].m_obj;
lean_object* v_a_669_ = stack[9].m_obj;
lean_object* v_a_670_ = stack[10].m_obj;
lean_object* v_a_671_ = stack[11].m_obj;
lean_object* v_res_674_;
v_res_674_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing(v_f_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
stack->m_obj
 = v_res_674_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___boxed(lean_object* v_f_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing(v_f_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
lean_dec(v_a_684_);
lean_dec_ref(v_a_683_);
lean_dec(v_a_682_);
lean_dec_ref(v_a_681_);
lean_dec(v_a_680_);
lean_dec_ref(v_a_679_);
lean_dec(v_a_678_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
return v_res_688_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_690_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__0));
v___x_691_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___boxed), 12, 0);
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v___x_690_);
return v___x_692_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM(void){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1);
return v___x_693_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_695_, v_a_696_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_708_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_708_ == 0)
{
v___x_701_ = v___x_698_;
v_isShared_702_ = v_isSharedCheck_708_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_698_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_708_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v_ringId_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
v_ringId_703_ = lean_ctor_get(v_a_694_, 0);
v___x_704_ = l_Lean_Meta_Grind_Arith_CommRing_State_getRing(v_a_699_, v_ringId_703_);
lean_dec(v_a_699_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_704_);
v___x_706_ = v___x_701_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
v_a_709_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_698_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_698_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_694_ = stack[0].m_obj;
lean_object* v_a_695_ = stack[1].m_obj;
lean_object* v_a_696_ = stack[2].m_obj;
lean_object* v_res_717_;
v_res_717_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_694_, v_a_695_, v_a_696_);
stack->m_obj
 = v_res_717_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg___boxed(lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_718_, v_a_719_, v_a_720_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
return v_res_722_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState(lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_723_, v_a_724_, v_a_732_);
return v___x_735_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_723_ = stack[0].m_obj;
lean_object* v_a_724_ = stack[1].m_obj;
lean_object* v_a_725_ = stack[2].m_obj;
lean_object* v_a_726_ = stack[3].m_obj;
lean_object* v_a_727_ = stack[4].m_obj;
lean_object* v_a_728_ = stack[5].m_obj;
lean_object* v_a_729_ = stack[6].m_obj;
lean_object* v_a_730_ = stack[7].m_obj;
lean_object* v_a_731_ = stack[8].m_obj;
lean_object* v_a_732_ = stack[9].m_obj;
lean_object* v_a_733_ = stack[10].m_obj;
lean_object* v_res_736_;
v_res_736_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState(v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
stack->m_obj
 = v_res_736_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___boxed(lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState(v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
lean_dec(v_a_745_);
lean_dec_ref(v_a_744_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec(v_a_739_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg___lam__0(lean_object* v_ringId_750_, lean_object* v_f_751_, lean_object* v_s_752_){
_start:
{
lean_object* v_rings_753_; lean_object* v_exprToRingId_754_; lean_object* v_semirings_755_; lean_object* v_exprToSemiringId_756_; lean_object* v_ncRings_757_; lean_object* v_exprToNCRingId_758_; lean_object* v_ncSemirings_759_; lean_object* v_exprToNCSemiringId_760_; lean_object* v_steps_761_; uint8_t v_reportedMaxDegreeIssue_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_783_; 
v_rings_753_ = lean_ctor_get(v_s_752_, 0);
v_exprToRingId_754_ = lean_ctor_get(v_s_752_, 1);
v_semirings_755_ = lean_ctor_get(v_s_752_, 2);
v_exprToSemiringId_756_ = lean_ctor_get(v_s_752_, 3);
v_ncRings_757_ = lean_ctor_get(v_s_752_, 4);
v_exprToNCRingId_758_ = lean_ctor_get(v_s_752_, 5);
v_ncSemirings_759_ = lean_ctor_get(v_s_752_, 6);
v_exprToNCSemiringId_760_ = lean_ctor_get(v_s_752_, 7);
v_steps_761_ = lean_ctor_get(v_s_752_, 8);
v_reportedMaxDegreeIssue_762_ = lean_ctor_get_uint8(v_s_752_, sizeof(void*)*9);
v_isSharedCheck_783_ = !lean_is_exclusive(v_s_752_);
if (v_isSharedCheck_783_ == 0)
{
v___x_764_ = v_s_752_;
v_isShared_765_ = v_isSharedCheck_783_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_steps_761_);
lean_inc(v_exprToNCSemiringId_760_);
lean_inc(v_ncSemirings_759_);
lean_inc(v_exprToNCRingId_758_);
lean_inc(v_ncRings_757_);
lean_inc(v_exprToSemiringId_756_);
lean_inc(v_semirings_755_);
lean_inc(v_exprToRingId_754_);
lean_inc(v_rings_753_);
lean_dec(v_s_752_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_783_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_766_ = lean_unsigned_to_nat(1u);
v___x_767_ = lean_nat_add(v_ringId_750_, v___x_766_);
v___x_768_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default;
v___x_769_ = l_Array_rightpad___redArg(v___x_767_, v___x_768_, v_rings_753_);
lean_dec(v___x_767_);
v___x_770_ = lean_array_get_size(v___x_769_);
v___x_771_ = lean_nat_dec_lt(v_ringId_750_, v___x_770_);
if (v___x_771_ == 0)
{
lean_object* v___x_773_; 
lean_dec_ref(v_f_751_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v___x_769_);
v___x_773_ = v___x_764_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_exprToRingId_754_);
lean_ctor_set(v_reuseFailAlloc_774_, 2, v_semirings_755_);
lean_ctor_set(v_reuseFailAlloc_774_, 3, v_exprToSemiringId_756_);
lean_ctor_set(v_reuseFailAlloc_774_, 4, v_ncRings_757_);
lean_ctor_set(v_reuseFailAlloc_774_, 5, v_exprToNCRingId_758_);
lean_ctor_set(v_reuseFailAlloc_774_, 6, v_ncSemirings_759_);
lean_ctor_set(v_reuseFailAlloc_774_, 7, v_exprToNCSemiringId_760_);
lean_ctor_set(v_reuseFailAlloc_774_, 8, v_steps_761_);
lean_ctor_set_uint8(v_reuseFailAlloc_774_, sizeof(void*)*9, v_reportedMaxDegreeIssue_762_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
else
{
lean_object* v_v_775_; lean_object* v___x_776_; lean_object* v_xs_x27_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_781_; 
v_v_775_ = lean_array_fget(v___x_769_, v_ringId_750_);
v___x_776_ = lean_box(0);
v_xs_x27_777_ = lean_array_fset(v___x_769_, v_ringId_750_, v___x_776_);
v___x_778_ = lean_apply_1(v_f_751_, v_v_775_);
v___x_779_ = lean_array_fset(v_xs_x27_777_, v_ringId_750_, v___x_778_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v___x_779_);
v___x_781_ = v___x_764_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_exprToRingId_754_);
lean_ctor_set(v_reuseFailAlloc_782_, 2, v_semirings_755_);
lean_ctor_set(v_reuseFailAlloc_782_, 3, v_exprToSemiringId_756_);
lean_ctor_set(v_reuseFailAlloc_782_, 4, v_ncRings_757_);
lean_ctor_set(v_reuseFailAlloc_782_, 5, v_exprToNCRingId_758_);
lean_ctor_set(v_reuseFailAlloc_782_, 6, v_ncSemirings_759_);
lean_ctor_set(v_reuseFailAlloc_782_, 7, v_exprToNCSemiringId_760_);
lean_ctor_set(v_reuseFailAlloc_782_, 8, v_steps_761_);
lean_ctor_set_uint8(v_reuseFailAlloc_782_, sizeof(void*)*9, v_reportedMaxDegreeIssue_762_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg___lam__0___boxed(lean_object* v_ringId_784_, lean_object* v_f_785_, lean_object* v_s_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg___lam__0(v_ringId_784_, v_f_785_, v_s_786_);
lean_dec(v_ringId_784_);
return v_res_787_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(lean_object* v_f_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_ringId_792_; lean_object* v___f_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v_ringId_792_ = lean_ctor_get(v_a_789_, 0);
lean_inc(v_ringId_792_);
v___f_793_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_793_, 0, v_ringId_792_);
lean_closure_set(v___f_793_, 1, v_f_788_);
v___x_794_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_795_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_794_, v___f_793_, v_a_790_);
return v___x_795_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_788_ = stack[0].m_obj;
lean_object* v_a_789_ = stack[1].m_obj;
lean_object* v_a_790_ = stack[2].m_obj;
lean_object* v_res_796_;
v_res_796_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(v_f_788_, v_a_789_, v_a_790_);
stack->m_obj
 = v_res_796_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg___boxed(lean_object* v_f_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(v_f_797_, v_a_798_, v_a_799_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
return v_res_801_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState(lean_object* v_f_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(v_f_802_, v_a_803_, v_a_804_);
return v___x_815_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_802_ = stack[0].m_obj;
lean_object* v_a_803_ = stack[1].m_obj;
lean_object* v_a_804_ = stack[2].m_obj;
lean_object* v_a_805_ = stack[3].m_obj;
lean_object* v_a_806_ = stack[4].m_obj;
lean_object* v_a_807_ = stack[5].m_obj;
lean_object* v_a_808_ = stack[6].m_obj;
lean_object* v_a_809_ = stack[7].m_obj;
lean_object* v_a_810_ = stack[8].m_obj;
lean_object* v_a_811_ = stack[9].m_obj;
lean_object* v_a_812_ = stack[10].m_obj;
lean_object* v_a_813_ = stack[11].m_obj;
lean_object* v_res_816_;
v_res_816_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState(v_f_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
stack->m_obj
 = v_res_816_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___boxed(lean_object* v_f_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState(v_f_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
lean_dec(v_a_828_);
lean_dec_ref(v_a_827_);
lean_dec(v_a_826_);
lean_dec_ref(v_a_825_);
lean_dec(v_a_824_);
lean_dec_ref(v_a_823_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
lean_dec(v_a_820_);
lean_dec(v_a_819_);
lean_dec_ref(v_a_818_);
return v_res_830_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__1(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_832_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__0));
v___x_833_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___boxed), 12, 0);
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
lean_ctor_set(v___x_834_, 1, v___x_832_);
return v___x_834_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM(void){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__1);
return v___x_835_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___lam__0(lean_object* v___x_836_, lean_object* v_x_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v___y_838_, v___y_839_, v___y_847_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_867_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_867_ == 0)
{
v___x_853_ = v___x_850_;
v_isShared_854_ = v_isSharedCheck_867_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_867_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v_toRingState_855_; lean_object* v_vars_856_; lean_object* v_size_857_; uint8_t v___x_858_; 
v_toRingState_855_ = lean_ctor_get(v_a_851_, 0);
lean_inc_ref(v_toRingState_855_);
lean_dec(v_a_851_);
v_vars_856_ = lean_ctor_get(v_toRingState_855_, 0);
lean_inc_ref(v_vars_856_);
lean_dec_ref(v_toRingState_855_);
v_size_857_ = lean_ctor_get(v_vars_856_, 2);
v___x_858_ = lean_nat_dec_lt(v_x_837_, v_size_857_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; lean_object* v___x_861_; 
lean_dec_ref(v_vars_856_);
v___x_859_ = l_outOfBounds___redArg(v___x_836_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_859_);
v___x_861_ = v___x_853_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
else
{
lean_object* v___x_863_; lean_object* v___x_865_; 
v___x_863_ = l_Lean_PersistentArray_get_x21___redArg(v___x_836_, v_vars_856_, v_x_837_);
lean_dec_ref(v_vars_856_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_863_);
v___x_865_ = v___x_853_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
v_a_868_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_850_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_850_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_836_ = stack[0].m_obj;
lean_object* v_x_837_ = stack[1].m_obj;
lean_object* v___y_838_ = stack[2].m_obj;
lean_object* v___y_839_ = stack[3].m_obj;
lean_object* v___y_840_ = stack[4].m_obj;
lean_object* v___y_841_ = stack[5].m_obj;
lean_object* v___y_842_ = stack[6].m_obj;
lean_object* v___y_843_ = stack[7].m_obj;
lean_object* v___y_844_ = stack[8].m_obj;
lean_object* v___y_845_ = stack[9].m_obj;
lean_object* v___y_846_ = stack[10].m_obj;
lean_object* v___y_847_ = stack[11].m_obj;
lean_object* v___y_848_ = stack[12].m_obj;
lean_object* v_res_876_;
v_res_876_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___lam__0(v___x_836_, v_x_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
stack->m_obj
 = v_res_876_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___lam__0___boxed(lean_object* v___x_877_, lean_object* v_x_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___lam__0(v___x_877_, v_x_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v_x_878_);
lean_dec_ref(v___x_877_);
return v_res_891_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___closed__0(void){
_start:
{
lean_object* v___x_892_; lean_object* v___f_893_; 
v___x_892_ = l_Lean_instInhabitedExpr;
v___f_893_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___lam__0___boxed), 14, 1);
lean_closure_set(v___f_893_, 0, v___x_892_);
return v___f_893_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM(void){
_start:
{
lean_object* v___f_894_; 
v___f_894_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___closed__0);
return v___f_894_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg(lean_object* v_x_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_){
_start:
{
lean_object* v_ringId_908_; uint8_t v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v_ringId_908_ = lean_ctor_get(v_a_896_, 0);
v___x_909_ = 1;
lean_inc(v_ringId_908_);
v___x_910_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_910_, 0, v_ringId_908_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*1, v___x_909_);
lean_inc(v_a_906_);
lean_inc_ref(v_a_905_);
lean_inc(v_a_904_);
lean_inc_ref(v_a_903_);
lean_inc(v_a_902_);
lean_inc_ref(v_a_901_);
lean_inc(v_a_900_);
lean_inc_ref(v_a_899_);
lean_inc(v_a_898_);
lean_inc(v_a_897_);
v___x_911_ = lean_apply_12(v_x_895_, v___x_910_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, lean_box(0));
return v___x_911_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_895_ = stack[0].m_obj;
lean_object* v_a_896_ = stack[1].m_obj;
lean_object* v_a_897_ = stack[2].m_obj;
lean_object* v_a_898_ = stack[3].m_obj;
lean_object* v_a_899_ = stack[4].m_obj;
lean_object* v_a_900_ = stack[5].m_obj;
lean_object* v_a_901_ = stack[6].m_obj;
lean_object* v_a_902_ = stack[7].m_obj;
lean_object* v_a_903_ = stack[8].m_obj;
lean_object* v_a_904_ = stack[9].m_obj;
lean_object* v_a_905_ = stack[10].m_obj;
lean_object* v_a_906_ = stack[11].m_obj;
lean_object* v_res_912_;
v_res_912_ = l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg(v_x_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_);
stack->m_obj
 = v_res_912_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg___boxed(lean_object* v_x_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg(v_x_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
lean_dec(v_a_922_);
lean_dec_ref(v_a_921_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec(v_a_916_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
return v_res_926_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd(lean_object* v_00_u03b1_927_, lean_object* v_x_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_){
_start:
{
lean_object* v_ringId_941_; uint8_t v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v_ringId_941_ = lean_ctor_get(v_a_929_, 0);
v___x_942_ = 1;
lean_inc(v_ringId_941_);
v___x_943_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_943_, 0, v_ringId_941_);
lean_ctor_set_uint8(v___x_943_, sizeof(void*)*1, v___x_942_);
lean_inc(v_a_939_);
lean_inc_ref(v_a_938_);
lean_inc(v_a_937_);
lean_inc_ref(v_a_936_);
lean_inc(v_a_935_);
lean_inc_ref(v_a_934_);
lean_inc(v_a_933_);
lean_inc_ref(v_a_932_);
lean_inc(v_a_931_);
lean_inc(v_a_930_);
v___x_944_ = lean_apply_12(v_x_928_, v___x_943_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, lean_box(0));
return v___x_944_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_928_ = stack[1].m_obj;
lean_object* v_a_929_ = stack[2].m_obj;
lean_object* v_a_930_ = stack[3].m_obj;
lean_object* v_a_931_ = stack[4].m_obj;
lean_object* v_a_932_ = stack[5].m_obj;
lean_object* v_a_933_ = stack[6].m_obj;
lean_object* v_a_934_ = stack[7].m_obj;
lean_object* v_a_935_ = stack[8].m_obj;
lean_object* v_a_936_ = stack[9].m_obj;
lean_object* v_a_937_ = stack[10].m_obj;
lean_object* v_a_938_ = stack[11].m_obj;
lean_object* v_a_939_ = stack[12].m_obj;
lean_object* v_res_945_;
v_res_945_ = l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd(lean_box(0), v_x_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_);
stack->m_obj
 = v_res_945_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___boxed(lean_object* v_00_u03b1_946_, lean_object* v_x_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd(v_00_u03b1_946_, v_x_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
return v_res_960_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(lean_object* v_a_961_){
_start:
{
uint8_t v_checkCoeffDvd_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v_checkCoeffDvd_963_ = lean_ctor_get_uint8(v_a_961_, sizeof(void*)*1);
v___x_964_ = lean_box(v_checkCoeffDvd_963_);
v___x_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
return v___x_965_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_961_ = stack[0].m_obj;
lean_object* v_res_966_;
v_res_966_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(v_a_961_);
stack->m_obj
 = v_res_966_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg___boxed(lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(v_a_967_);
lean_dec_ref(v_a_967_);
return v_res_969_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd(lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(v_a_970_);
return v___x_982_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_970_ = stack[0].m_obj;
lean_object* v_a_971_ = stack[1].m_obj;
lean_object* v_a_972_ = stack[2].m_obj;
lean_object* v_a_973_ = stack[3].m_obj;
lean_object* v_a_974_ = stack[4].m_obj;
lean_object* v_a_975_ = stack[5].m_obj;
lean_object* v_a_976_ = stack[6].m_obj;
lean_object* v_a_977_ = stack[7].m_obj;
lean_object* v_a_978_ = stack[8].m_obj;
lean_object* v_a_979_ = stack[9].m_obj;
lean_object* v_a_980_ = stack[10].m_obj;
lean_object* v_res_983_;
v_res_983_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd(v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
stack->m_obj
 = v_res_983_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___boxed(lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd(v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
lean_dec(v_a_992_);
lean_dec_ref(v_a_991_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec(v_a_986_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_997_, lean_object* v_vals_998_, lean_object* v_i_999_, lean_object* v_k_1000_){
_start:
{
lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_1001_ = lean_array_get_size(v_keys_997_);
v___x_1002_ = lean_nat_dec_lt(v_i_999_, v___x_1001_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; 
lean_dec(v_i_999_);
v___x_1003_ = lean_box(0);
return v___x_1003_;
}
else
{
lean_object* v_k_x27_1004_; size_t v___x_1005_; size_t v___x_1006_; uint8_t v___x_1007_; 
v_k_x27_1004_ = lean_array_fget_borrowed(v_keys_997_, v_i_999_);
v___x_1005_ = lean_ptr_addr(v_k_1000_);
v___x_1006_ = lean_ptr_addr(v_k_x27_1004_);
v___x_1007_ = lean_usize_dec_eq(v___x_1005_, v___x_1006_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = lean_unsigned_to_nat(1u);
v___x_1009_ = lean_nat_add(v_i_999_, v___x_1008_);
lean_dec(v_i_999_);
v_i_999_ = v___x_1009_;
goto _start;
}
else
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = lean_array_fget_borrowed(v_vals_998_, v_i_999_);
lean_dec(v_i_999_);
lean_inc(v___x_1011_);
v___x_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
return v___x_1012_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1013_, lean_object* v_vals_1014_, lean_object* v_i_1015_, lean_object* v_k_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1013_, v_vals_1014_, v_i_1015_, v_k_1016_);
lean_dec_ref(v_k_1016_);
lean_dec_ref(v_vals_1014_);
lean_dec_ref(v_keys_1013_);
return v_res_1017_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(lean_object* v_x_1018_, size_t v_x_1019_, lean_object* v_x_1020_){
_start:
{
if (lean_obj_tag(v_x_1018_) == 0)
{
lean_object* v_es_1021_; lean_object* v___x_1022_; size_t v___x_1023_; size_t v___x_1024_; lean_object* v_j_1025_; lean_object* v___x_1026_; 
v_es_1021_ = lean_ctor_get(v_x_1018_, 0);
v___x_1022_ = lean_box(2);
v___x_1023_ = ((size_t)31ULL);
v___x_1024_ = lean_usize_land(v_x_1019_, v___x_1023_);
v_j_1025_ = lean_usize_to_nat(v___x_1024_);
v___x_1026_ = lean_array_get_borrowed(v___x_1022_, v_es_1021_, v_j_1025_);
lean_dec(v_j_1025_);
switch(lean_obj_tag(v___x_1026_))
{
case 0:
{
lean_object* v_key_1027_; lean_object* v_val_1028_; size_t v___x_1029_; size_t v___x_1030_; uint8_t v___x_1031_; 
v_key_1027_ = lean_ctor_get(v___x_1026_, 0);
v_val_1028_ = lean_ctor_get(v___x_1026_, 1);
v___x_1029_ = lean_ptr_addr(v_x_1020_);
v___x_1030_ = lean_ptr_addr(v_key_1027_);
v___x_1031_ = lean_usize_dec_eq(v___x_1029_, v___x_1030_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; 
v___x_1032_ = lean_box(0);
return v___x_1032_;
}
else
{
lean_object* v___x_1033_; 
lean_inc(v_val_1028_);
v___x_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1033_, 0, v_val_1028_);
return v___x_1033_;
}
}
case 1:
{
lean_object* v_node_1034_; size_t v___x_1035_; size_t v___x_1036_; 
v_node_1034_ = lean_ctor_get(v___x_1026_, 0);
v___x_1035_ = ((size_t)5ULL);
v___x_1036_ = lean_usize_shift_right(v_x_1019_, v___x_1035_);
v_x_1018_ = v_node_1034_;
v_x_1019_ = v___x_1036_;
goto _start;
}
default: 
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_box(0);
return v___x_1038_;
}
}
}
else
{
lean_object* v_ks_1039_; lean_object* v_vs_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v_ks_1039_ = lean_ctor_get(v_x_1018_, 0);
v_vs_1040_ = lean_ctor_get(v_x_1018_, 1);
v___x_1041_ = lean_unsigned_to_nat(0u);
v___x_1042_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1039_, v_vs_1040_, v___x_1041_, v_x_1020_);
return v___x_1042_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1018_ = stack[0].m_obj;
size_t v_x_1019_ = stack[1].m_num;
lean_object* v_x_1020_ = stack[2].m_obj;
lean_object* v_res_1043_;
v_res_1043_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_1018_, v_x_1019_, v_x_1020_);
stack->m_obj
 = v_res_1043_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1044_, lean_object* v_x_1045_, lean_object* v_x_1046_){
_start:
{
size_t v_x_916__boxed_1047_; lean_object* v_res_1048_; 
v_x_916__boxed_1047_ = lean_unbox_usize(v_x_1045_);
lean_dec(v_x_1045_);
v_res_1048_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_1044_, v_x_916__boxed_1047_, v_x_1046_);
lean_dec_ref(v_x_1046_);
lean_dec_ref(v_x_1044_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(lean_object* v_x_1049_, lean_object* v_x_1050_){
_start:
{
size_t v___x_1051_; size_t v___x_1052_; size_t v___x_1053_; uint64_t v___x_1054_; size_t v___x_1055_; lean_object* v___x_1056_; 
v___x_1051_ = lean_ptr_addr(v_x_1050_);
v___x_1052_ = ((size_t)3ULL);
v___x_1053_ = lean_usize_shift_right(v___x_1051_, v___x_1052_);
v___x_1054_ = lean_usize_to_uint64(v___x_1053_);
v___x_1055_ = lean_uint64_to_usize(v___x_1054_);
v___x_1056_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_1049_, v___x_1055_, v_x_1050_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg___boxed(lean_object* v_x_1057_, lean_object* v_x_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_1057_, v_x_1058_);
lean_dec_ref(v_x_1058_);
lean_dec_ref(v_x_1057_);
return v_res_1059_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(lean_object* v_e_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1061_, v_a_1062_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1074_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1067_ = v___x_1064_;
v_isShared_1068_ = v_isSharedCheck_1074_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1064_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1074_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v_exprToRingId_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; 
v_exprToRingId_1069_ = lean_ctor_get(v_a_1065_, 1);
lean_inc_ref(v_exprToRingId_1069_);
lean_dec(v_a_1065_);
v___x_1070_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_exprToRingId_1069_, v_e_1060_);
lean_dec_ref(v_exprToRingId_1069_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v___x_1070_);
v___x_1072_ = v___x_1067_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
v_a_1075_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1064_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1064_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1060_ = stack[0].m_obj;
lean_object* v_a_1061_ = stack[1].m_obj;
lean_object* v_a_1062_ = stack[2].m_obj;
lean_object* v_res_1083_;
v_res_1083_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_1060_, v_a_1061_, v_a_1062_);
stack->m_obj
 = v_res_1083_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg___boxed(lean_object* v_e_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_1084_, v_a_1085_, v_a_1086_);
lean_dec_ref(v_a_1086_);
lean_dec(v_a_1085_);
lean_dec_ref(v_e_1084_);
return v_res_1088_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(lean_object* v_e_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_1089_, v_a_1090_, v_a_1098_);
return v___x_1101_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1089_ = stack[0].m_obj;
lean_object* v_a_1090_ = stack[1].m_obj;
lean_object* v_a_1091_ = stack[2].m_obj;
lean_object* v_a_1092_ = stack[3].m_obj;
lean_object* v_a_1093_ = stack[4].m_obj;
lean_object* v_a_1094_ = stack[5].m_obj;
lean_object* v_a_1095_ = stack[6].m_obj;
lean_object* v_a_1096_ = stack[7].m_obj;
lean_object* v_a_1097_ = stack[8].m_obj;
lean_object* v_a_1098_ = stack[9].m_obj;
lean_object* v_a_1099_ = stack[10].m_obj;
lean_object* v_res_1102_;
v_res_1102_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(v_e_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
stack->m_obj
 = v_res_1102_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___boxed(lean_object* v_e_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(v_e_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
lean_dec(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_e_1103_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(lean_object* v_00_u03b2_1116_, lean_object* v_x_1117_, lean_object* v_x_1118_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_1117_, v_x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___boxed(lean_object* v_00_u03b2_1120_, lean_object* v_x_1121_, lean_object* v_x_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(v_00_u03b2_1120_, v_x_1121_, v_x_1122_);
lean_dec_ref(v_x_1122_);
lean_dec_ref(v_x_1121_);
return v_res_1123_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1124_, lean_object* v_x_1125_, size_t v_x_1126_, lean_object* v_x_1127_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_1125_, v_x_1126_, v_x_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1125_ = stack[1].m_obj;
size_t v_x_1126_ = stack[2].m_num;
lean_object* v_x_1127_ = stack[3].m_obj;
lean_object* v_res_1129_;
v_res_1129_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(lean_box(0), v_x_1125_, v_x_1126_, v_x_1127_);
stack->m_obj
 = v_res_1129_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1130_, lean_object* v_x_1131_, lean_object* v_x_1132_, lean_object* v_x_1133_){
_start:
{
size_t v_x_1102__boxed_1134_; lean_object* v_res_1135_; 
v_x_1102__boxed_1134_ = lean_unbox_usize(v_x_1132_);
lean_dec(v_x_1132_);
v_res_1135_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(v_00_u03b2_1130_, v_x_1131_, v_x_1102__boxed_1134_, v_x_1133_);
lean_dec_ref(v_x_1133_);
lean_dec_ref(v_x_1131_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1136_, lean_object* v_keys_1137_, lean_object* v_vals_1138_, lean_object* v_heq_1139_, lean_object* v_i_1140_, lean_object* v_k_1141_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1137_, v_vals_1138_, v_i_1140_, v_k_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1143_, lean_object* v_keys_1144_, lean_object* v_vals_1145_, lean_object* v_heq_1146_, lean_object* v_i_1147_, lean_object* v_k_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1143_, v_keys_1144_, v_vals_1145_, v_heq_1146_, v_i_1147_, v_k_1148_);
lean_dec_ref(v_k_1148_);
lean_dec_ref(v_vals_1145_);
lean_dec_ref(v_keys_1144_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0(lean_object* v_toPure_1150_, lean_object* v_____do__lift_1151_){
_start:
{
lean_object* v_charInst_x3f_1155_; 
v_charInst_x3f_1155_ = lean_ctor_get(v_____do__lift_1151_, 5);
lean_inc(v_charInst_x3f_1155_);
lean_dec_ref(v_____do__lift_1151_);
if (lean_obj_tag(v_charInst_x3f_1155_) == 1)
{
lean_object* v_val_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1167_; 
v_val_1156_ = lean_ctor_get(v_charInst_x3f_1155_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_charInst_x3f_1155_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1158_ = v_charInst_x3f_1155_;
v_isShared_1159_ = v_isSharedCheck_1167_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_val_1156_);
lean_dec(v_charInst_x3f_1155_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1167_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v_snd_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; 
v_snd_1160_ = lean_ctor_get(v_val_1156_, 1);
lean_inc(v_snd_1160_);
lean_dec(v_val_1156_);
v___x_1161_ = lean_unsigned_to_nat(0u);
v___x_1162_ = lean_nat_dec_eq(v_snd_1160_, v___x_1161_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1164_; 
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 0, v_snd_1160_);
v___x_1164_ = v___x_1158_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_snd_1160_);
v___x_1164_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_apply_2(v_toPure_1150_, lean_box(0), v___x_1164_);
return v___x_1165_;
}
}
else
{
lean_dec(v_snd_1160_);
lean_del_object(v___x_1158_);
goto v___jp_1152_;
}
}
}
else
{
lean_dec(v_charInst_x3f_1155_);
goto v___jp_1152_;
}
v___jp_1152_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = lean_box(0);
v___x_1154_ = lean_apply_2(v_toPure_1150_, lean_box(0), v___x_1153_);
return v___x_1154_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(lean_object* v_inst_1168_, lean_object* v_inst_1169_){
_start:
{
lean_object* v_toApplicative_1170_; lean_object* v_toBind_1171_; lean_object* v_getRing_1172_; lean_object* v_toPure_1173_; lean_object* v___f_1174_; lean_object* v___x_1175_; 
v_toApplicative_1170_ = lean_ctor_get(v_inst_1168_, 0);
lean_inc_ref(v_toApplicative_1170_);
v_toBind_1171_ = lean_ctor_get(v_inst_1168_, 1);
lean_inc(v_toBind_1171_);
lean_dec_ref(v_inst_1168_);
v_getRing_1172_ = lean_ctor_get(v_inst_1169_, 0);
lean_inc(v_getRing_1172_);
lean_dec_ref(v_inst_1169_);
v_toPure_1173_ = lean_ctor_get(v_toApplicative_1170_, 1);
lean_inc(v_toPure_1173_);
lean_dec_ref(v_toApplicative_1170_);
v___f_1174_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1174_, 0, v_toPure_1173_);
v___x_1175_ = lean_apply_4(v_toBind_1171_, lean_box(0), lean_box(0), v_getRing_1172_, v___f_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f(lean_object* v_m_1176_, lean_object* v_inst_1177_, lean_object* v_inst_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(v_inst_1177_, v_inst_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0(lean_object* v_toPure_1180_, lean_object* v_____do__lift_1181_){
_start:
{
lean_object* v_charInst_x3f_1185_; 
v_charInst_x3f_1185_ = lean_ctor_get(v_____do__lift_1181_, 5);
lean_inc(v_charInst_x3f_1185_);
lean_dec_ref(v_____do__lift_1181_);
if (lean_obj_tag(v_charInst_x3f_1185_) == 1)
{
lean_object* v_val_1186_; lean_object* v_snd_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
v_val_1186_ = lean_ctor_get(v_charInst_x3f_1185_, 0);
v_snd_1187_ = lean_ctor_get(v_val_1186_, 1);
v___x_1188_ = lean_unsigned_to_nat(0u);
v___x_1189_ = lean_nat_dec_eq(v_snd_1187_, v___x_1188_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; 
v___x_1190_ = lean_apply_2(v_toPure_1180_, lean_box(0), v_charInst_x3f_1185_);
return v___x_1190_;
}
else
{
lean_dec_ref_known(v_charInst_x3f_1185_, 1);
goto v___jp_1182_;
}
}
else
{
lean_dec(v_charInst_x3f_1185_);
goto v___jp_1182_;
}
v___jp_1182_:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = lean_box(0);
v___x_1184_ = lean_apply_2(v_toPure_1180_, lean_box(0), v___x_1183_);
return v___x_1184_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(lean_object* v_inst_1191_, lean_object* v_inst_1192_){
_start:
{
lean_object* v_toApplicative_1193_; lean_object* v_toBind_1194_; lean_object* v_getRing_1195_; lean_object* v_toPure_1196_; lean_object* v___f_1197_; lean_object* v___x_1198_; 
v_toApplicative_1193_ = lean_ctor_get(v_inst_1191_, 0);
lean_inc_ref(v_toApplicative_1193_);
v_toBind_1194_ = lean_ctor_get(v_inst_1191_, 1);
lean_inc(v_toBind_1194_);
lean_dec_ref(v_inst_1191_);
v_getRing_1195_ = lean_ctor_get(v_inst_1192_, 0);
lean_inc(v_getRing_1195_);
lean_dec_ref(v_inst_1192_);
v_toPure_1196_ = lean_ctor_get(v_toApplicative_1193_, 1);
lean_inc(v_toPure_1196_);
lean_dec_ref(v_toApplicative_1193_);
v___f_1197_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1197_, 0, v_toPure_1196_);
v___x_1198_ = lean_apply_4(v_toBind_1194_, lean_box(0), lean_box(0), v_getRing_1195_, v___f_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f(lean_object* v_m_1199_, lean_object* v_inst_1200_, lean_object* v_inst_1201_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(v_inst_1200_, v_inst_1201_);
return v___x_1202_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1224_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1218_ = v___x_1215_;
v_isShared_1219_ = v_isSharedCheck_1224_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1215_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1224_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v_noZeroDivInst_x3f_1220_; lean_object* v___x_1222_; 
v_noZeroDivInst_x3f_1220_ = lean_ctor_get(v_a_1216_, 6);
lean_inc(v_noZeroDivInst_x3f_1220_);
lean_dec(v_a_1216_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 0, v_noZeroDivInst_x3f_1220_);
v___x_1222_ = v___x_1218_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_noZeroDivInst_x3f_1220_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
v_a_1225_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1215_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1215_);
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
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1203_ = stack[0].m_obj;
lean_object* v_a_1204_ = stack[1].m_obj;
lean_object* v_a_1205_ = stack[2].m_obj;
lean_object* v_a_1206_ = stack[3].m_obj;
lean_object* v_a_1207_ = stack[4].m_obj;
lean_object* v_a_1208_ = stack[5].m_obj;
lean_object* v_a_1209_ = stack[6].m_obj;
lean_object* v_a_1210_ = stack[7].m_obj;
lean_object* v_a_1211_ = stack[8].m_obj;
lean_object* v_a_1212_ = stack[9].m_obj;
lean_object* v_a_1213_ = stack[10].m_obj;
lean_object* v_res_1233_;
v_res_1233_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
stack->m_obj
 = v_res_1233_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f___boxed(lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_);
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
lean_dec_ref(v_a_1234_);
return v_res_1246_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1275_; 
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1262_ = v___x_1259_;
v_isShared_1263_ = v_isSharedCheck_1275_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1259_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1275_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v_noZeroDivInst_x3f_1264_; 
v_noZeroDivInst_x3f_1264_ = lean_ctor_get(v_a_1260_, 6);
lean_inc(v_noZeroDivInst_x3f_1264_);
lean_dec(v_a_1260_);
if (lean_obj_tag(v_noZeroDivInst_x3f_1264_) == 0)
{
uint8_t v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1268_; 
v___x_1265_ = 0;
v___x_1266_ = lean_box(v___x_1265_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v___x_1266_);
v___x_1268_ = v___x_1262_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1266_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
else
{
uint8_t v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1273_; 
lean_dec_ref_known(v_noZeroDivInst_x3f_1264_, 1);
v___x_1270_ = 1;
v___x_1271_ = lean_box(v___x_1270_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v___x_1271_);
v___x_1273_ = v___x_1262_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1271_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
v_a_1276_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1259_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1259_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1247_ = stack[0].m_obj;
lean_object* v_a_1248_ = stack[1].m_obj;
lean_object* v_a_1249_ = stack[2].m_obj;
lean_object* v_a_1250_ = stack[3].m_obj;
lean_object* v_a_1251_ = stack[4].m_obj;
lean_object* v_a_1252_ = stack[5].m_obj;
lean_object* v_a_1253_ = stack[6].m_obj;
lean_object* v_a_1254_ = stack[7].m_obj;
lean_object* v_a_1255_ = stack[8].m_obj;
lean_object* v_a_1256_ = stack[9].m_obj;
lean_object* v_a_1257_ = stack[10].m_obj;
lean_object* v_res_1284_;
v_res_1284_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
stack->m_obj
 = v_res_1284_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors___boxed(lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
lean_dec(v_a_1291_);
lean_dec_ref(v_a_1290_);
lean_dec(v_a_1289_);
lean_dec_ref(v_a_1288_);
lean_dec(v_a_1287_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
return v_res_1297_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar(lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1327_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1313_ = v___x_1310_;
v_isShared_1314_ = v_isSharedCheck_1327_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1310_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1327_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v_toRing_1315_; lean_object* v_charInst_x3f_1316_; 
v_toRing_1315_ = lean_ctor_get(v_a_1311_, 0);
lean_inc_ref(v_toRing_1315_);
lean_dec(v_a_1311_);
v_charInst_x3f_1316_ = lean_ctor_get(v_toRing_1315_, 5);
lean_inc(v_charInst_x3f_1316_);
lean_dec_ref(v_toRing_1315_);
if (lean_obj_tag(v_charInst_x3f_1316_) == 0)
{
uint8_t v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1320_; 
v___x_1317_ = 0;
v___x_1318_ = lean_box(v___x_1317_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v___x_1318_);
v___x_1320_ = v___x_1313_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1318_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
else
{
uint8_t v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1325_; 
lean_dec_ref_known(v_charInst_x3f_1316_, 1);
v___x_1322_ = 1;
v___x_1323_ = lean_box(v___x_1322_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v___x_1323_);
v___x_1325_ = v___x_1313_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1323_);
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
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
v_a_1328_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1310_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1310_);
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
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_hasChar_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1298_ = stack[0].m_obj;
lean_object* v_a_1299_ = stack[1].m_obj;
lean_object* v_a_1300_ = stack[2].m_obj;
lean_object* v_a_1301_ = stack[3].m_obj;
lean_object* v_a_1302_ = stack[4].m_obj;
lean_object* v_a_1303_ = stack[5].m_obj;
lean_object* v_a_1304_ = stack[6].m_obj;
lean_object* v_a_1305_ = stack[7].m_obj;
lean_object* v_a_1306_ = stack[8].m_obj;
lean_object* v_a_1307_ = stack[9].m_obj;
lean_object* v_a_1308_ = stack[10].m_obj;
lean_object* v_res_1336_;
v_res_1336_ = l_Lean_Meta_Grind_Arith_CommRing_hasChar(v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
stack->m_obj
 = v_res_1336_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar___boxed(lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_Meta_Grind_Arith_CommRing_hasChar(v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
lean_dec(v_a_1347_);
lean_dec_ref(v_a_1346_);
lean_dec(v_a_1345_);
lean_dec_ref(v_a_1344_);
lean_dec(v_a_1343_);
lean_dec_ref(v_a_1342_);
lean_dec(v_a_1341_);
lean_dec_ref(v_a_1340_);
lean_dec(v_a_1339_);
lean_dec(v_a_1338_);
lean_dec_ref(v_a_1337_);
return v_res_1349_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1(void){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0));
v___x_1352_ = l_Lean_stringToMessageData(v___x_1351_);
return v___x_1352_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst(lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1378_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1368_ = v___x_1365_;
v_isShared_1369_ = v_isSharedCheck_1378_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1365_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1378_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v_toRing_1370_; lean_object* v_charInst_x3f_1371_; 
v_toRing_1370_ = lean_ctor_get(v_a_1366_, 0);
lean_inc_ref(v_toRing_1370_);
lean_dec(v_a_1366_);
v_charInst_x3f_1371_ = lean_ctor_get(v_toRing_1370_, 5);
lean_inc(v_charInst_x3f_1371_);
lean_dec_ref(v_toRing_1370_);
if (lean_obj_tag(v_charInst_x3f_1371_) == 1)
{
lean_object* v_val_1372_; lean_object* v___x_1374_; 
v_val_1372_ = lean_ctor_get(v_charInst_x3f_1371_, 0);
lean_inc(v_val_1372_);
lean_dec_ref_known(v_charInst_x3f_1371_, 1);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 0, v_val_1372_);
v___x_1374_ = v___x_1368_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_val_1372_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
lean_dec(v_charInst_x3f_1371_);
lean_del_object(v___x_1368_);
v___x_1376_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1);
v___x_1377_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v___x_1376_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
return v___x_1377_;
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
v_a_1379_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1365_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1365_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_getCharInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1353_ = stack[0].m_obj;
lean_object* v_a_1354_ = stack[1].m_obj;
lean_object* v_a_1355_ = stack[2].m_obj;
lean_object* v_a_1356_ = stack[3].m_obj;
lean_object* v_a_1357_ = stack[4].m_obj;
lean_object* v_a_1358_ = stack[5].m_obj;
lean_object* v_a_1359_ = stack[6].m_obj;
lean_object* v_a_1360_ = stack[7].m_obj;
lean_object* v_a_1361_ = stack[8].m_obj;
lean_object* v_a_1362_ = stack[9].m_obj;
lean_object* v_a_1363_ = stack[10].m_obj;
lean_object* v_res_1387_;
v_res_1387_ = l_Lean_Meta_Grind_Arith_CommRing_getCharInst(v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
stack->m_obj
 = v_res_1387_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst___boxed(lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_Meta_Grind_Arith_CommRing_getCharInst(v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
lean_dec(v_a_1394_);
lean_dec_ref(v_a_1393_);
lean_dec(v_a_1392_);
lean_dec_ref(v_a_1391_);
lean_dec(v_a_1390_);
lean_dec(v_a_1389_);
lean_dec_ref(v_a_1388_);
return v_res_1400_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField(lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1429_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1416_ = v___x_1413_;
v_isShared_1417_ = v_isSharedCheck_1429_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1429_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v_fieldInst_x3f_1418_; 
v_fieldInst_x3f_1418_ = lean_ctor_get(v_a_1414_, 7);
lean_inc(v_fieldInst_x3f_1418_);
lean_dec(v_a_1414_);
if (lean_obj_tag(v_fieldInst_x3f_1418_) == 0)
{
uint8_t v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1419_ = 0;
v___x_1420_ = lean_box(v___x_1419_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v___x_1420_);
v___x_1422_ = v___x_1416_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
else
{
uint8_t v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1427_; 
lean_dec_ref_known(v_fieldInst_x3f_1418_, 1);
v___x_1424_ = 1;
v___x_1425_ = lean_box(v___x_1424_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v___x_1425_);
v___x_1427_ = v___x_1416_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
v_a_1430_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1413_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1413_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_isField_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1401_ = stack[0].m_obj;
lean_object* v_a_1402_ = stack[1].m_obj;
lean_object* v_a_1403_ = stack[2].m_obj;
lean_object* v_a_1404_ = stack[3].m_obj;
lean_object* v_a_1405_ = stack[4].m_obj;
lean_object* v_a_1406_ = stack[5].m_obj;
lean_object* v_a_1407_ = stack[6].m_obj;
lean_object* v_a_1408_ = stack[7].m_obj;
lean_object* v_a_1409_ = stack[8].m_obj;
lean_object* v_a_1410_ = stack[9].m_obj;
lean_object* v_a_1411_ = stack[10].m_obj;
lean_object* v_res_1438_;
v_res_1438_ = l_Lean_Meta_Grind_Arith_CommRing_isField(v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_);
stack->m_obj
 = v_res_1438_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField___boxed(lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_Meta_Grind_Arith_CommRing_isField(v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
lean_dec(v_a_1445_);
lean_dec_ref(v_a_1444_);
lean_dec(v_a_1443_);
lean_dec_ref(v_a_1442_);
lean_dec(v_a_1441_);
lean_dec(v_a_1440_);
lean_dec_ref(v_a_1439_);
return v_res_1451_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___redArg(lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_1452_, v_a_1453_, v_a_1454_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1472_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1459_ = v___x_1456_;
v_isShared_1460_ = v_isSharedCheck_1472_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1456_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1472_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v_queue_1461_; 
v_queue_1461_ = lean_ctor_get(v_a_1457_, 4);
lean_inc(v_queue_1461_);
lean_dec(v_a_1457_);
if (lean_obj_tag(v_queue_1461_) == 0)
{
uint8_t v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1465_; 
lean_dec_ref_known(v_queue_1461_, 5);
v___x_1462_ = 0;
v___x_1463_ = lean_box(v___x_1462_);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 0, v___x_1463_);
v___x_1465_ = v___x_1459_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1463_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
else
{
uint8_t v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1470_; 
v___x_1467_ = 1;
v___x_1468_ = lean_box(v___x_1467_);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 0, v___x_1468_);
v___x_1470_ = v___x_1459_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
v_a_1473_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1456_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1456_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1452_ = stack[0].m_obj;
lean_object* v_a_1453_ = stack[1].m_obj;
lean_object* v_a_1454_ = stack[2].m_obj;
lean_object* v_res_1481_;
v_res_1481_ = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___redArg(v_a_1452_, v_a_1453_, v_a_1454_);
stack->m_obj
 = v_res_1481_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___redArg___boxed(lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___redArg(v_a_1482_, v_a_1483_, v_a_1484_);
lean_dec_ref(v_a_1484_);
lean_dec(v_a_1483_);
lean_dec_ref(v_a_1482_);
return v_res_1486_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___redArg(v_a_1487_, v_a_1488_, v_a_1496_);
return v___x_1499_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1487_ = stack[0].m_obj;
lean_object* v_a_1488_ = stack[1].m_obj;
lean_object* v_a_1489_ = stack[2].m_obj;
lean_object* v_a_1490_ = stack[3].m_obj;
lean_object* v_a_1491_ = stack[4].m_obj;
lean_object* v_a_1492_ = stack[5].m_obj;
lean_object* v_a_1493_ = stack[6].m_obj;
lean_object* v_a_1494_ = stack[7].m_obj;
lean_object* v_a_1495_ = stack[8].m_obj;
lean_object* v_a_1496_ = stack[9].m_obj;
lean_object* v_a_1497_ = stack[10].m_obj;
lean_object* v_res_1500_;
v_res_1500_ = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_);
stack->m_obj
 = v_res_1500_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___boxed(lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_);
lean_dec(v_a_1511_);
lean_dec_ref(v_a_1510_);
lean_dec(v_a_1509_);
lean_dec_ref(v_a_1508_);
lean_dec(v_a_1507_);
lean_dec_ref(v_a_1506_);
lean_dec(v_a_1505_);
lean_dec_ref(v_a_1504_);
lean_dec(v_a_1503_);
lean_dec(v_a_1502_);
lean_dec_ref(v_a_1501_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(lean_object* v_k_1514_, lean_object* v_t_1515_){
_start:
{
if (lean_obj_tag(v_t_1515_) == 0)
{
lean_object* v_k_1516_; lean_object* v_v_1517_; lean_object* v_l_1518_; lean_object* v_r_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_2173_; 
v_k_1516_ = lean_ctor_get(v_t_1515_, 1);
v_v_1517_ = lean_ctor_get(v_t_1515_, 2);
v_l_1518_ = lean_ctor_get(v_t_1515_, 3);
v_r_1519_ = lean_ctor_get(v_t_1515_, 4);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_t_1515_);
if (v_isSharedCheck_2173_ == 0)
{
lean_object* v_unused_2174_; 
v_unused_2174_ = lean_ctor_get(v_t_1515_, 0);
lean_dec(v_unused_2174_);
v___x_1521_ = v_t_1515_;
v_isShared_1522_ = v_isSharedCheck_2173_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_r_1519_);
lean_inc(v_l_1518_);
lean_inc(v_v_1517_);
lean_inc(v_k_1516_);
lean_dec(v_t_1515_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_2173_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
uint8_t v___x_1523_; 
v___x_1523_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(v_k_1514_, v_k_1516_);
switch(v___x_1523_)
{
case 0:
{
lean_object* v_impl_1524_; lean_object* v___x_1525_; 
v_impl_1524_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1514_, v_l_1518_);
v___x_1525_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1524_) == 0)
{
if (lean_obj_tag(v_r_1519_) == 0)
{
lean_object* v_size_1526_; lean_object* v_size_1527_; lean_object* v_k_1528_; lean_object* v_v_1529_; lean_object* v_l_1530_; lean_object* v_r_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; 
v_size_1526_ = lean_ctor_get(v_impl_1524_, 0);
v_size_1527_ = lean_ctor_get(v_r_1519_, 0);
v_k_1528_ = lean_ctor_get(v_r_1519_, 1);
v_v_1529_ = lean_ctor_get(v_r_1519_, 2);
v_l_1530_ = lean_ctor_get(v_r_1519_, 3);
lean_inc(v_l_1530_);
v_r_1531_ = lean_ctor_get(v_r_1519_, 4);
v___x_1532_ = lean_unsigned_to_nat(3u);
v___x_1533_ = lean_nat_mul(v___x_1532_, v_size_1526_);
v___x_1534_ = lean_nat_dec_lt(v___x_1533_, v_size_1527_);
lean_dec(v___x_1533_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1538_; 
lean_dec(v_l_1530_);
v___x_1535_ = lean_nat_add(v___x_1525_, v_size_1526_);
v___x_1536_ = lean_nat_add(v___x_1535_, v_size_1527_);
lean_dec(v___x_1535_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 3, v_impl_1524_);
lean_ctor_set(v___x_1521_, 0, v___x_1536_);
v___x_1538_ = v___x_1521_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_k_1516_);
lean_ctor_set(v_reuseFailAlloc_1539_, 2, v_v_1517_);
lean_ctor_set(v_reuseFailAlloc_1539_, 3, v_impl_1524_);
lean_ctor_set(v_reuseFailAlloc_1539_, 4, v_r_1519_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
else
{
lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1603_; 
lean_inc(v_r_1531_);
lean_inc(v_v_1529_);
lean_inc(v_k_1528_);
lean_inc(v_size_1527_);
v_isSharedCheck_1603_ = !lean_is_exclusive(v_r_1519_);
if (v_isSharedCheck_1603_ == 0)
{
lean_object* v_unused_1604_; lean_object* v_unused_1605_; lean_object* v_unused_1606_; lean_object* v_unused_1607_; lean_object* v_unused_1608_; 
v_unused_1604_ = lean_ctor_get(v_r_1519_, 4);
lean_dec(v_unused_1604_);
v_unused_1605_ = lean_ctor_get(v_r_1519_, 3);
lean_dec(v_unused_1605_);
v_unused_1606_ = lean_ctor_get(v_r_1519_, 2);
lean_dec(v_unused_1606_);
v_unused_1607_ = lean_ctor_get(v_r_1519_, 1);
lean_dec(v_unused_1607_);
v_unused_1608_ = lean_ctor_get(v_r_1519_, 0);
lean_dec(v_unused_1608_);
v___x_1541_ = v_r_1519_;
v_isShared_1542_ = v_isSharedCheck_1603_;
goto v_resetjp_1540_;
}
else
{
lean_dec(v_r_1519_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1603_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v_size_1543_; lean_object* v_k_1544_; lean_object* v_v_1545_; lean_object* v_l_1546_; lean_object* v_r_1547_; lean_object* v_size_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; 
v_size_1543_ = lean_ctor_get(v_l_1530_, 0);
v_k_1544_ = lean_ctor_get(v_l_1530_, 1);
v_v_1545_ = lean_ctor_get(v_l_1530_, 2);
v_l_1546_ = lean_ctor_get(v_l_1530_, 3);
v_r_1547_ = lean_ctor_get(v_l_1530_, 4);
v_size_1548_ = lean_ctor_get(v_r_1531_, 0);
v___x_1549_ = lean_unsigned_to_nat(2u);
v___x_1550_ = lean_nat_mul(v___x_1549_, v_size_1548_);
v___x_1551_ = lean_nat_dec_lt(v_size_1543_, v___x_1550_);
lean_dec(v___x_1550_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1579_; 
lean_inc(v_r_1547_);
lean_inc(v_l_1546_);
lean_inc(v_v_1545_);
lean_inc(v_k_1544_);
v_isSharedCheck_1579_ = !lean_is_exclusive(v_l_1530_);
if (v_isSharedCheck_1579_ == 0)
{
lean_object* v_unused_1580_; lean_object* v_unused_1581_; lean_object* v_unused_1582_; lean_object* v_unused_1583_; lean_object* v_unused_1584_; 
v_unused_1580_ = lean_ctor_get(v_l_1530_, 4);
lean_dec(v_unused_1580_);
v_unused_1581_ = lean_ctor_get(v_l_1530_, 3);
lean_dec(v_unused_1581_);
v_unused_1582_ = lean_ctor_get(v_l_1530_, 2);
lean_dec(v_unused_1582_);
v_unused_1583_ = lean_ctor_get(v_l_1530_, 1);
lean_dec(v_unused_1583_);
v_unused_1584_ = lean_ctor_get(v_l_1530_, 0);
lean_dec(v_unused_1584_);
v___x_1553_ = v_l_1530_;
v_isShared_1554_ = v_isSharedCheck_1579_;
goto v_resetjp_1552_;
}
else
{
lean_dec(v_l_1530_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1579_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1569_; 
v___x_1555_ = lean_nat_add(v___x_1525_, v_size_1526_);
v___x_1556_ = lean_nat_add(v___x_1555_, v_size_1527_);
lean_dec(v_size_1527_);
if (lean_obj_tag(v_l_1546_) == 0)
{
lean_object* v_size_1577_; 
v_size_1577_ = lean_ctor_get(v_l_1546_, 0);
lean_inc(v_size_1577_);
v___y_1569_ = v_size_1577_;
goto v___jp_1568_;
}
else
{
lean_object* v___x_1578_; 
v___x_1578_ = lean_unsigned_to_nat(0u);
v___y_1569_ = v___x_1578_;
goto v___jp_1568_;
}
v___jp_1557_:
{
lean_object* v___x_1561_; lean_object* v___x_1563_; 
v___x_1561_ = lean_nat_add(v___y_1559_, v___y_1560_);
lean_dec(v___y_1560_);
lean_dec(v___y_1559_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 4, v_r_1531_);
lean_ctor_set(v___x_1553_, 3, v_r_1547_);
lean_ctor_set(v___x_1553_, 2, v_v_1529_);
lean_ctor_set(v___x_1553_, 1, v_k_1528_);
lean_ctor_set(v___x_1553_, 0, v___x_1561_);
v___x_1563_ = v___x_1553_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1561_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_k_1528_);
lean_ctor_set(v_reuseFailAlloc_1567_, 2, v_v_1529_);
lean_ctor_set(v_reuseFailAlloc_1567_, 3, v_r_1547_);
lean_ctor_set(v_reuseFailAlloc_1567_, 4, v_r_1531_);
v___x_1563_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
lean_object* v___x_1565_; 
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 4, v___x_1563_);
lean_ctor_set(v___x_1541_, 3, v___y_1558_);
lean_ctor_set(v___x_1541_, 2, v_v_1545_);
lean_ctor_set(v___x_1541_, 1, v_k_1544_);
lean_ctor_set(v___x_1541_, 0, v___x_1556_);
v___x_1565_ = v___x_1541_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1556_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_k_1544_);
lean_ctor_set(v_reuseFailAlloc_1566_, 2, v_v_1545_);
lean_ctor_set(v_reuseFailAlloc_1566_, 3, v___y_1558_);
lean_ctor_set(v_reuseFailAlloc_1566_, 4, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
v___jp_1568_:
{
lean_object* v___x_1570_; lean_object* v___x_1572_; 
v___x_1570_ = lean_nat_add(v___x_1555_, v___y_1569_);
lean_dec(v___y_1569_);
lean_dec(v___x_1555_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 4, v_l_1546_);
lean_ctor_set(v___x_1521_, 3, v_impl_1524_);
lean_ctor_set(v___x_1521_, 0, v___x_1570_);
v___x_1572_ = v___x_1521_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1570_);
lean_ctor_set(v_reuseFailAlloc_1576_, 1, v_k_1516_);
lean_ctor_set(v_reuseFailAlloc_1576_, 2, v_v_1517_);
lean_ctor_set(v_reuseFailAlloc_1576_, 3, v_impl_1524_);
lean_ctor_set(v_reuseFailAlloc_1576_, 4, v_l_1546_);
v___x_1572_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
lean_object* v___x_1573_; 
v___x_1573_ = lean_nat_add(v___x_1525_, v_size_1548_);
if (lean_obj_tag(v_r_1547_) == 0)
{
lean_object* v_size_1574_; 
v_size_1574_ = lean_ctor_get(v_r_1547_, 0);
lean_inc(v_size_1574_);
v___y_1558_ = v___x_1572_;
v___y_1559_ = v___x_1573_;
v___y_1560_ = v_size_1574_;
goto v___jp_1557_;
}
else
{
lean_object* v___x_1575_; 
v___x_1575_ = lean_unsigned_to_nat(0u);
v___y_1558_ = v___x_1572_;
v___y_1559_ = v___x_1573_;
v___y_1560_ = v___x_1575_;
goto v___jp_1557_;
}
}
}
}
}
else
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1589_; 
lean_del_object(v___x_1521_);
v___x_1585_ = lean_nat_add(v___x_1525_, v_size_1526_);
v___x_1586_ = lean_nat_add(v___x_1585_, v_size_1527_);
lean_dec(v_size_1527_);
v___x_1587_ = lean_nat_add(v___x_1585_, v_size_1543_);
lean_dec(v___x_1585_);
lean_inc_ref(v_impl_1524_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 4, v_l_1530_);
lean_ctor_set(v___x_1541_, 3, v_impl_1524_);
lean_ctor_set(v___x_1541_, 2, v_v_1517_);
lean_ctor_set(v___x_1541_, 1, v_k_1516_);
lean_ctor_set(v___x_1541_, 0, v___x_1587_);
v___x_1589_ = v___x_1541_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1587_);
lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_k_1516_);
lean_ctor_set(v_reuseFailAlloc_1602_, 2, v_v_1517_);
lean_ctor_set(v_reuseFailAlloc_1602_, 3, v_impl_1524_);
lean_ctor_set(v_reuseFailAlloc_1602_, 4, v_l_1530_);
v___x_1589_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
v_isSharedCheck_1596_ = !lean_is_exclusive(v_impl_1524_);
if (v_isSharedCheck_1596_ == 0)
{
lean_object* v_unused_1597_; lean_object* v_unused_1598_; lean_object* v_unused_1599_; lean_object* v_unused_1600_; lean_object* v_unused_1601_; 
v_unused_1597_ = lean_ctor_get(v_impl_1524_, 4);
lean_dec(v_unused_1597_);
v_unused_1598_ = lean_ctor_get(v_impl_1524_, 3);
lean_dec(v_unused_1598_);
v_unused_1599_ = lean_ctor_get(v_impl_1524_, 2);
lean_dec(v_unused_1599_);
v_unused_1600_ = lean_ctor_get(v_impl_1524_, 1);
lean_dec(v_unused_1600_);
v_unused_1601_ = lean_ctor_get(v_impl_1524_, 0);
lean_dec(v_unused_1601_);
v___x_1591_ = v_impl_1524_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_dec(v_impl_1524_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 4, v_r_1531_);
lean_ctor_set(v___x_1591_, 3, v___x_1589_);
lean_ctor_set(v___x_1591_, 2, v_v_1529_);
lean_ctor_set(v___x_1591_, 1, v_k_1528_);
lean_ctor_set(v___x_1591_, 0, v___x_1586_);
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_k_1528_);
lean_ctor_set(v_reuseFailAlloc_1595_, 2, v_v_1529_);
lean_ctor_set(v_reuseFailAlloc_1595_, 3, v___x_1589_);
lean_ctor_set(v_reuseFailAlloc_1595_, 4, v_r_1531_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1609_; lean_object* v___x_1610_; lean_object* v___x_1612_; 
v_size_1609_ = lean_ctor_get(v_impl_1524_, 0);
v___x_1610_ = lean_nat_add(v___x_1525_, v_size_1609_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 3, v_impl_1524_);
lean_ctor_set(v___x_1521_, 0, v___x_1610_);
v___x_1612_ = v___x_1521_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1610_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_k_1516_);
lean_ctor_set(v_reuseFailAlloc_1613_, 2, v_v_1517_);
lean_ctor_set(v_reuseFailAlloc_1613_, 3, v_impl_1524_);
lean_ctor_set(v_reuseFailAlloc_1613_, 4, v_r_1519_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
else
{
if (lean_obj_tag(v_r_1519_) == 0)
{
lean_object* v_l_1614_; 
v_l_1614_ = lean_ctor_get(v_r_1519_, 3);
lean_inc(v_l_1614_);
if (lean_obj_tag(v_l_1614_) == 0)
{
lean_object* v_r_1615_; 
v_r_1615_ = lean_ctor_get(v_r_1519_, 4);
lean_inc(v_r_1615_);
if (lean_obj_tag(v_r_1615_) == 0)
{
lean_object* v_size_1616_; lean_object* v_k_1617_; lean_object* v_v_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1631_; 
v_size_1616_ = lean_ctor_get(v_r_1519_, 0);
v_k_1617_ = lean_ctor_get(v_r_1519_, 1);
v_v_1618_ = lean_ctor_get(v_r_1519_, 2);
v_isSharedCheck_1631_ = !lean_is_exclusive(v_r_1519_);
if (v_isSharedCheck_1631_ == 0)
{
lean_object* v_unused_1632_; lean_object* v_unused_1633_; 
v_unused_1632_ = lean_ctor_get(v_r_1519_, 4);
lean_dec(v_unused_1632_);
v_unused_1633_ = lean_ctor_get(v_r_1519_, 3);
lean_dec(v_unused_1633_);
v___x_1620_ = v_r_1519_;
v_isShared_1621_ = v_isSharedCheck_1631_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_v_1618_);
lean_inc(v_k_1617_);
lean_inc(v_size_1616_);
lean_dec(v_r_1519_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1631_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v_size_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1626_; 
v_size_1622_ = lean_ctor_get(v_l_1614_, 0);
v___x_1623_ = lean_nat_add(v___x_1525_, v_size_1616_);
lean_dec(v_size_1616_);
v___x_1624_ = lean_nat_add(v___x_1525_, v_size_1622_);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 4, v_l_1614_);
lean_ctor_set(v___x_1620_, 3, v_impl_1524_);
lean_ctor_set(v___x_1620_, 2, v_v_1517_);
lean_ctor_set(v___x_1620_, 1, v_k_1516_);
lean_ctor_set(v___x_1620_, 0, v___x_1624_);
v___x_1626_ = v___x_1620_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1624_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_k_1516_);
lean_ctor_set(v_reuseFailAlloc_1630_, 2, v_v_1517_);
lean_ctor_set(v_reuseFailAlloc_1630_, 3, v_impl_1524_);
lean_ctor_set(v_reuseFailAlloc_1630_, 4, v_l_1614_);
v___x_1626_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
lean_object* v___x_1628_; 
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 4, v_r_1615_);
lean_ctor_set(v___x_1521_, 3, v___x_1626_);
lean_ctor_set(v___x_1521_, 2, v_v_1618_);
lean_ctor_set(v___x_1521_, 1, v_k_1617_);
lean_ctor_set(v___x_1521_, 0, v___x_1623_);
v___x_1628_ = v___x_1521_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1623_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v_k_1617_);
lean_ctor_set(v_reuseFailAlloc_1629_, 2, v_v_1618_);
lean_ctor_set(v_reuseFailAlloc_1629_, 3, v___x_1626_);
lean_ctor_set(v_reuseFailAlloc_1629_, 4, v_r_1615_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
else
{
lean_object* v_k_1634_; lean_object* v_v_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1658_; 
v_k_1634_ = lean_ctor_get(v_r_1519_, 1);
v_v_1635_ = lean_ctor_get(v_r_1519_, 2);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_r_1519_);
if (v_isSharedCheck_1658_ == 0)
{
lean_object* v_unused_1659_; lean_object* v_unused_1660_; lean_object* v_unused_1661_; 
v_unused_1659_ = lean_ctor_get(v_r_1519_, 4);
lean_dec(v_unused_1659_);
v_unused_1660_ = lean_ctor_get(v_r_1519_, 3);
lean_dec(v_unused_1660_);
v_unused_1661_ = lean_ctor_get(v_r_1519_, 0);
lean_dec(v_unused_1661_);
v___x_1637_ = v_r_1519_;
v_isShared_1638_ = v_isSharedCheck_1658_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_v_1635_);
lean_inc(v_k_1634_);
lean_dec(v_r_1519_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1658_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v_k_1639_; lean_object* v_v_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1654_; 
v_k_1639_ = lean_ctor_get(v_l_1614_, 1);
v_v_1640_ = lean_ctor_get(v_l_1614_, 2);
v_isSharedCheck_1654_ = !lean_is_exclusive(v_l_1614_);
if (v_isSharedCheck_1654_ == 0)
{
lean_object* v_unused_1655_; lean_object* v_unused_1656_; lean_object* v_unused_1657_; 
v_unused_1655_ = lean_ctor_get(v_l_1614_, 4);
lean_dec(v_unused_1655_);
v_unused_1656_ = lean_ctor_get(v_l_1614_, 3);
lean_dec(v_unused_1656_);
v_unused_1657_ = lean_ctor_get(v_l_1614_, 0);
lean_dec(v_unused_1657_);
v___x_1642_ = v_l_1614_;
v_isShared_1643_ = v_isSharedCheck_1654_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_v_1640_);
lean_inc(v_k_1639_);
lean_dec(v_l_1614_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1654_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1644_ = lean_unsigned_to_nat(3u);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 4, v_r_1615_);
lean_ctor_set(v___x_1642_, 3, v_r_1615_);
lean_ctor_set(v___x_1642_, 2, v_v_1517_);
lean_ctor_set(v___x_1642_, 1, v_k_1516_);
lean_ctor_set(v___x_1642_, 0, v___x_1525_);
v___x_1646_ = v___x_1642_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1653_, 1, v_k_1516_);
lean_ctor_set(v_reuseFailAlloc_1653_, 2, v_v_1517_);
lean_ctor_set(v_reuseFailAlloc_1653_, 3, v_r_1615_);
lean_ctor_set(v_reuseFailAlloc_1653_, 4, v_r_1615_);
v___x_1646_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
lean_object* v___x_1648_; 
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 3, v_r_1615_);
lean_ctor_set(v___x_1637_, 0, v___x_1525_);
v___x_1648_ = v___x_1637_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v_k_1634_);
lean_ctor_set(v_reuseFailAlloc_1652_, 2, v_v_1635_);
lean_ctor_set(v_reuseFailAlloc_1652_, 3, v_r_1615_);
lean_ctor_set(v_reuseFailAlloc_1652_, 4, v_r_1615_);
v___x_1648_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
lean_object* v___x_1650_; 
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 4, v___x_1648_);
lean_ctor_set(v___x_1521_, 3, v___x_1646_);
lean_ctor_set(v___x_1521_, 2, v_v_1640_);
lean_ctor_set(v___x_1521_, 1, v_k_1639_);
lean_ctor_set(v___x_1521_, 0, v___x_1644_);
v___x_1650_ = v___x_1521_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1644_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v_k_1639_);
lean_ctor_set(v_reuseFailAlloc_1651_, 2, v_v_1640_);
lean_ctor_set(v_reuseFailAlloc_1651_, 3, v___x_1646_);
lean_ctor_set(v_reuseFailAlloc_1651_, 4, v___x_1648_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1662_; 
v_r_1662_ = lean_ctor_get(v_r_1519_, 4);
lean_inc(v_r_1662_);
if (lean_obj_tag(v_r_1662_) == 0)
{
lean_object* v_k_1663_; lean_object* v_v_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1675_; 
v_k_1663_ = lean_ctor_get(v_r_1519_, 1);
v_v_1664_ = lean_ctor_get(v_r_1519_, 2);
v_isSharedCheck_1675_ = !lean_is_exclusive(v_r_1519_);
if (v_isSharedCheck_1675_ == 0)
{
lean_object* v_unused_1676_; lean_object* v_unused_1677_; lean_object* v_unused_1678_; 
v_unused_1676_ = lean_ctor_get(v_r_1519_, 4);
lean_dec(v_unused_1676_);
v_unused_1677_ = lean_ctor_get(v_r_1519_, 3);
lean_dec(v_unused_1677_);
v_unused_1678_ = lean_ctor_get(v_r_1519_, 0);
lean_dec(v_unused_1678_);
v___x_1666_ = v_r_1519_;
v_isShared_1667_ = v_isSharedCheck_1675_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_v_1664_);
lean_inc(v_k_1663_);
lean_dec(v_r_1519_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1675_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1668_ = lean_unsigned_to_nat(3u);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 4, v_l_1614_);
lean_ctor_set(v___x_1666_, 2, v_v_1517_);
lean_ctor_set(v___x_1666_, 1, v_k_1516_);
lean_ctor_set(v___x_1666_, 0, v___x_1525_);
v___x_1670_ = v___x_1666_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v_k_1516_);
lean_ctor_set(v_reuseFailAlloc_1674_, 2, v_v_1517_);
lean_ctor_set(v_reuseFailAlloc_1674_, 3, v_l_1614_);
lean_ctor_set(v_reuseFailAlloc_1674_, 4, v_l_1614_);
v___x_1670_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_object* v___x_1672_; 
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 4, v_r_1662_);
lean_ctor_set(v___x_1521_, 3, v___x_1670_);
lean_ctor_set(v___x_1521_, 2, v_v_1664_);
lean_ctor_set(v___x_1521_, 1, v_k_1663_);
lean_ctor_set(v___x_1521_, 0, v___x_1668_);
v___x_1672_ = v___x_1521_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1668_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v_k_1663_);
lean_ctor_set(v_reuseFailAlloc_1673_, 2, v_v_1664_);
lean_ctor_set(v_reuseFailAlloc_1673_, 3, v___x_1670_);
lean_ctor_set(v_reuseFailAlloc_1673_, 4, v_r_1662_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
else
{
lean_object* v_size_1679_; lean_object* v_k_1680_; lean_object* v_v_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1692_; 
v_size_1679_ = lean_ctor_get(v_r_1519_, 0);
v_k_1680_ = lean_ctor_get(v_r_1519_, 1);
v_v_1681_ = lean_ctor_get(v_r_1519_, 2);
v_isSharedCheck_1692_ = !lean_is_exclusive(v_r_1519_);
if (v_isSharedCheck_1692_ == 0)
{
lean_object* v_unused_1693_; lean_object* v_unused_1694_; 
v_unused_1693_ = lean_ctor_get(v_r_1519_, 4);
lean_dec(v_unused_1693_);
v_unused_1694_ = lean_ctor_get(v_r_1519_, 3);
lean_dec(v_unused_1694_);
v___x_1683_ = v_r_1519_;
v_isShared_1684_ = v_isSharedCheck_1692_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_v_1681_);
lean_inc(v_k_1680_);
lean_inc(v_size_1679_);
lean_dec(v_r_1519_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1692_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 3, v_r_1662_);
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_size_1679_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v_k_1680_);
lean_ctor_set(v_reuseFailAlloc_1691_, 2, v_v_1681_);
lean_ctor_set(v_reuseFailAlloc_1691_, 3, v_r_1662_);
lean_ctor_set(v_reuseFailAlloc_1691_, 4, v_r_1662_);
v___x_1686_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
lean_object* v___x_1687_; lean_object* v___x_1689_; 
v___x_1687_ = lean_unsigned_to_nat(2u);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 4, v___x_1686_);
lean_ctor_set(v___x_1521_, 3, v_r_1662_);
lean_ctor_set(v___x_1521_, 0, v___x_1687_);
v___x_1689_ = v___x_1521_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1687_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v_k_1516_);
lean_ctor_set(v_reuseFailAlloc_1690_, 2, v_v_1517_);
lean_ctor_set(v_reuseFailAlloc_1690_, 3, v_r_1662_);
lean_ctor_set(v_reuseFailAlloc_1690_, 4, v___x_1686_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
}
}
else
{
lean_object* v___x_1696_; 
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 3, v_r_1519_);
lean_ctor_set(v___x_1521_, 0, v___x_1525_);
v___x_1696_ = v___x_1521_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v_k_1516_);
lean_ctor_set(v_reuseFailAlloc_1697_, 2, v_v_1517_);
lean_ctor_set(v_reuseFailAlloc_1697_, 3, v_r_1519_);
lean_ctor_set(v_reuseFailAlloc_1697_, 4, v_r_1519_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1521_);
lean_dec(v_v_1517_);
lean_dec(v_k_1516_);
if (lean_obj_tag(v_l_1518_) == 0)
{
if (lean_obj_tag(v_r_1519_) == 0)
{
lean_object* v_size_1698_; lean_object* v_k_1699_; lean_object* v_v_1700_; lean_object* v_l_1701_; lean_object* v_r_1702_; lean_object* v_size_1703_; lean_object* v_k_1704_; lean_object* v_v_1705_; lean_object* v_l_1706_; lean_object* v_r_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; 
v_size_1698_ = lean_ctor_get(v_l_1518_, 0);
v_k_1699_ = lean_ctor_get(v_l_1518_, 1);
v_v_1700_ = lean_ctor_get(v_l_1518_, 2);
v_l_1701_ = lean_ctor_get(v_l_1518_, 3);
v_r_1702_ = lean_ctor_get(v_l_1518_, 4);
lean_inc(v_r_1702_);
v_size_1703_ = lean_ctor_get(v_r_1519_, 0);
v_k_1704_ = lean_ctor_get(v_r_1519_, 1);
v_v_1705_ = lean_ctor_get(v_r_1519_, 2);
v_l_1706_ = lean_ctor_get(v_r_1519_, 3);
lean_inc(v_l_1706_);
v_r_1707_ = lean_ctor_get(v_r_1519_, 4);
v___x_1708_ = lean_unsigned_to_nat(1u);
v___x_1709_ = lean_nat_dec_lt(v_size_1698_, v_size_1703_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1845_; 
lean_inc(v_l_1701_);
lean_inc(v_v_1700_);
lean_inc(v_k_1699_);
v_isSharedCheck_1845_ = !lean_is_exclusive(v_l_1518_);
if (v_isSharedCheck_1845_ == 0)
{
lean_object* v_unused_1846_; lean_object* v_unused_1847_; lean_object* v_unused_1848_; lean_object* v_unused_1849_; lean_object* v_unused_1850_; 
v_unused_1846_ = lean_ctor_get(v_l_1518_, 4);
lean_dec(v_unused_1846_);
v_unused_1847_ = lean_ctor_get(v_l_1518_, 3);
lean_dec(v_unused_1847_);
v_unused_1848_ = lean_ctor_get(v_l_1518_, 2);
lean_dec(v_unused_1848_);
v_unused_1849_ = lean_ctor_get(v_l_1518_, 1);
lean_dec(v_unused_1849_);
v_unused_1850_ = lean_ctor_get(v_l_1518_, 0);
lean_dec(v_unused_1850_);
v___x_1711_ = v_l_1518_;
v_isShared_1712_ = v_isSharedCheck_1845_;
goto v_resetjp_1710_;
}
else
{
lean_dec(v_l_1518_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1845_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1713_; lean_object* v_tree_1714_; 
v___x_1713_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1699_, v_v_1700_, v_l_1701_, v_r_1702_);
v_tree_1714_ = lean_ctor_get(v___x_1713_, 2);
if (lean_obj_tag(v_tree_1714_) == 0)
{
lean_object* v_k_1715_; lean_object* v_v_1716_; lean_object* v_size_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; uint8_t v___x_1720_; 
lean_inc_ref(v_tree_1714_);
v_k_1715_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_k_1715_);
v_v_1716_ = lean_ctor_get(v___x_1713_, 1);
lean_inc(v_v_1716_);
lean_dec_ref(v___x_1713_);
v_size_1717_ = lean_ctor_get(v_tree_1714_, 0);
v___x_1718_ = lean_unsigned_to_nat(3u);
v___x_1719_ = lean_nat_mul(v___x_1718_, v_size_1717_);
v___x_1720_ = lean_nat_dec_lt(v___x_1719_, v_size_1703_);
lean_dec(v___x_1719_);
if (v___x_1720_ == 0)
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1724_; 
lean_dec(v_l_1706_);
v___x_1721_ = lean_nat_add(v___x_1708_, v_size_1717_);
v___x_1722_ = lean_nat_add(v___x_1721_, v_size_1703_);
lean_dec(v___x_1721_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 4, v_r_1519_);
lean_ctor_set(v___x_1711_, 3, v_tree_1714_);
lean_ctor_set(v___x_1711_, 2, v_v_1716_);
lean_ctor_set(v___x_1711_, 1, v_k_1715_);
lean_ctor_set(v___x_1711_, 0, v___x_1722_);
v___x_1724_ = v___x_1711_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1722_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_k_1715_);
lean_ctor_set(v_reuseFailAlloc_1725_, 2, v_v_1716_);
lean_ctor_set(v_reuseFailAlloc_1725_, 3, v_tree_1714_);
lean_ctor_set(v_reuseFailAlloc_1725_, 4, v_r_1519_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
else
{
lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1780_; 
lean_inc(v_r_1707_);
lean_inc(v_v_1705_);
lean_inc(v_k_1704_);
lean_inc(v_size_1703_);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_r_1519_);
if (v_isSharedCheck_1780_ == 0)
{
lean_object* v_unused_1781_; lean_object* v_unused_1782_; lean_object* v_unused_1783_; lean_object* v_unused_1784_; lean_object* v_unused_1785_; 
v_unused_1781_ = lean_ctor_get(v_r_1519_, 4);
lean_dec(v_unused_1781_);
v_unused_1782_ = lean_ctor_get(v_r_1519_, 3);
lean_dec(v_unused_1782_);
v_unused_1783_ = lean_ctor_get(v_r_1519_, 2);
lean_dec(v_unused_1783_);
v_unused_1784_ = lean_ctor_get(v_r_1519_, 1);
lean_dec(v_unused_1784_);
v_unused_1785_ = lean_ctor_get(v_r_1519_, 0);
lean_dec(v_unused_1785_);
v___x_1727_ = v_r_1519_;
v_isShared_1728_ = v_isSharedCheck_1780_;
goto v_resetjp_1726_;
}
else
{
lean_dec(v_r_1519_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1780_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v_size_1729_; lean_object* v_k_1730_; lean_object* v_v_1731_; lean_object* v_l_1732_; lean_object* v_r_1733_; lean_object* v_size_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; 
v_size_1729_ = lean_ctor_get(v_l_1706_, 0);
v_k_1730_ = lean_ctor_get(v_l_1706_, 1);
v_v_1731_ = lean_ctor_get(v_l_1706_, 2);
v_l_1732_ = lean_ctor_get(v_l_1706_, 3);
v_r_1733_ = lean_ctor_get(v_l_1706_, 4);
v_size_1734_ = lean_ctor_get(v_r_1707_, 0);
v___x_1735_ = lean_unsigned_to_nat(2u);
v___x_1736_ = lean_nat_mul(v___x_1735_, v_size_1734_);
v___x_1737_ = lean_nat_dec_lt(v_size_1729_, v___x_1736_);
lean_dec(v___x_1736_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1765_; 
lean_inc(v_r_1733_);
lean_inc(v_l_1732_);
lean_inc(v_v_1731_);
lean_inc(v_k_1730_);
v_isSharedCheck_1765_ = !lean_is_exclusive(v_l_1706_);
if (v_isSharedCheck_1765_ == 0)
{
lean_object* v_unused_1766_; lean_object* v_unused_1767_; lean_object* v_unused_1768_; lean_object* v_unused_1769_; lean_object* v_unused_1770_; 
v_unused_1766_ = lean_ctor_get(v_l_1706_, 4);
lean_dec(v_unused_1766_);
v_unused_1767_ = lean_ctor_get(v_l_1706_, 3);
lean_dec(v_unused_1767_);
v_unused_1768_ = lean_ctor_get(v_l_1706_, 2);
lean_dec(v_unused_1768_);
v_unused_1769_ = lean_ctor_get(v_l_1706_, 1);
lean_dec(v_unused_1769_);
v_unused_1770_ = lean_ctor_get(v_l_1706_, 0);
lean_dec(v_unused_1770_);
v___x_1739_ = v_l_1706_;
v_isShared_1740_ = v_isSharedCheck_1765_;
goto v_resetjp_1738_;
}
else
{
lean_dec(v_l_1706_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1765_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1755_; 
v___x_1741_ = lean_nat_add(v___x_1708_, v_size_1717_);
v___x_1742_ = lean_nat_add(v___x_1741_, v_size_1703_);
lean_dec(v_size_1703_);
if (lean_obj_tag(v_l_1732_) == 0)
{
lean_object* v_size_1763_; 
v_size_1763_ = lean_ctor_get(v_l_1732_, 0);
lean_inc(v_size_1763_);
v___y_1755_ = v_size_1763_;
goto v___jp_1754_;
}
else
{
lean_object* v___x_1764_; 
v___x_1764_ = lean_unsigned_to_nat(0u);
v___y_1755_ = v___x_1764_;
goto v___jp_1754_;
}
v___jp_1743_:
{
lean_object* v___x_1747_; lean_object* v___x_1749_; 
v___x_1747_ = lean_nat_add(v___y_1744_, v___y_1746_);
lean_dec(v___y_1746_);
lean_dec(v___y_1744_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 4, v_r_1707_);
lean_ctor_set(v___x_1739_, 3, v_r_1733_);
lean_ctor_set(v___x_1739_, 2, v_v_1705_);
lean_ctor_set(v___x_1739_, 1, v_k_1704_);
lean_ctor_set(v___x_1739_, 0, v___x_1747_);
v___x_1749_ = v___x_1739_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1747_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v_k_1704_);
lean_ctor_set(v_reuseFailAlloc_1753_, 2, v_v_1705_);
lean_ctor_set(v_reuseFailAlloc_1753_, 3, v_r_1733_);
lean_ctor_set(v_reuseFailAlloc_1753_, 4, v_r_1707_);
v___x_1749_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
lean_object* v___x_1751_; 
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 4, v___x_1749_);
lean_ctor_set(v___x_1727_, 3, v___y_1745_);
lean_ctor_set(v___x_1727_, 2, v_v_1731_);
lean_ctor_set(v___x_1727_, 1, v_k_1730_);
lean_ctor_set(v___x_1727_, 0, v___x_1742_);
v___x_1751_ = v___x_1727_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1742_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_k_1730_);
lean_ctor_set(v_reuseFailAlloc_1752_, 2, v_v_1731_);
lean_ctor_set(v_reuseFailAlloc_1752_, 3, v___y_1745_);
lean_ctor_set(v_reuseFailAlloc_1752_, 4, v___x_1749_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
v___jp_1754_:
{
lean_object* v___x_1756_; lean_object* v___x_1758_; 
v___x_1756_ = lean_nat_add(v___x_1741_, v___y_1755_);
lean_dec(v___y_1755_);
lean_dec(v___x_1741_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 4, v_l_1732_);
lean_ctor_set(v___x_1711_, 3, v_tree_1714_);
lean_ctor_set(v___x_1711_, 2, v_v_1716_);
lean_ctor_set(v___x_1711_, 1, v_k_1715_);
lean_ctor_set(v___x_1711_, 0, v___x_1756_);
v___x_1758_ = v___x_1711_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1756_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_k_1715_);
lean_ctor_set(v_reuseFailAlloc_1762_, 2, v_v_1716_);
lean_ctor_set(v_reuseFailAlloc_1762_, 3, v_tree_1714_);
lean_ctor_set(v_reuseFailAlloc_1762_, 4, v_l_1732_);
v___x_1758_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v___x_1759_; 
v___x_1759_ = lean_nat_add(v___x_1708_, v_size_1734_);
if (lean_obj_tag(v_r_1733_) == 0)
{
lean_object* v_size_1760_; 
v_size_1760_ = lean_ctor_get(v_r_1733_, 0);
lean_inc(v_size_1760_);
v___y_1744_ = v___x_1759_;
v___y_1745_ = v___x_1758_;
v___y_1746_ = v_size_1760_;
goto v___jp_1743_;
}
else
{
lean_object* v___x_1761_; 
v___x_1761_ = lean_unsigned_to_nat(0u);
v___y_1744_ = v___x_1759_;
v___y_1745_ = v___x_1758_;
v___y_1746_ = v___x_1761_;
goto v___jp_1743_;
}
}
}
}
}
else
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1775_; 
v___x_1771_ = lean_nat_add(v___x_1708_, v_size_1717_);
v___x_1772_ = lean_nat_add(v___x_1771_, v_size_1703_);
lean_dec(v_size_1703_);
v___x_1773_ = lean_nat_add(v___x_1771_, v_size_1729_);
lean_dec(v___x_1771_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 4, v_l_1706_);
lean_ctor_set(v___x_1727_, 3, v_tree_1714_);
lean_ctor_set(v___x_1727_, 2, v_v_1716_);
lean_ctor_set(v___x_1727_, 1, v_k_1715_);
lean_ctor_set(v___x_1727_, 0, v___x_1773_);
v___x_1775_ = v___x_1727_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1773_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_k_1715_);
lean_ctor_set(v_reuseFailAlloc_1779_, 2, v_v_1716_);
lean_ctor_set(v_reuseFailAlloc_1779_, 3, v_tree_1714_);
lean_ctor_set(v_reuseFailAlloc_1779_, 4, v_l_1706_);
v___x_1775_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v___x_1777_; 
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 4, v_r_1707_);
lean_ctor_set(v___x_1711_, 3, v___x_1775_);
lean_ctor_set(v___x_1711_, 2, v_v_1705_);
lean_ctor_set(v___x_1711_, 1, v_k_1704_);
lean_ctor_set(v___x_1711_, 0, v___x_1772_);
v___x_1777_ = v___x_1711_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1772_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v_k_1704_);
lean_ctor_set(v_reuseFailAlloc_1778_, 2, v_v_1705_);
lean_ctor_set(v_reuseFailAlloc_1778_, 3, v___x_1775_);
lean_ctor_set(v_reuseFailAlloc_1778_, 4, v_r_1707_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
}
}
else
{
lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1839_; 
lean_inc(v_r_1707_);
lean_inc(v_v_1705_);
lean_inc(v_k_1704_);
lean_inc(v_size_1703_);
v_isSharedCheck_1839_ = !lean_is_exclusive(v_r_1519_);
if (v_isSharedCheck_1839_ == 0)
{
lean_object* v_unused_1840_; lean_object* v_unused_1841_; lean_object* v_unused_1842_; lean_object* v_unused_1843_; lean_object* v_unused_1844_; 
v_unused_1840_ = lean_ctor_get(v_r_1519_, 4);
lean_dec(v_unused_1840_);
v_unused_1841_ = lean_ctor_get(v_r_1519_, 3);
lean_dec(v_unused_1841_);
v_unused_1842_ = lean_ctor_get(v_r_1519_, 2);
lean_dec(v_unused_1842_);
v_unused_1843_ = lean_ctor_get(v_r_1519_, 1);
lean_dec(v_unused_1843_);
v_unused_1844_ = lean_ctor_get(v_r_1519_, 0);
lean_dec(v_unused_1844_);
v___x_1787_ = v_r_1519_;
v_isShared_1788_ = v_isSharedCheck_1839_;
goto v_resetjp_1786_;
}
else
{
lean_dec(v_r_1519_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1839_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
if (lean_obj_tag(v_l_1706_) == 0)
{
if (lean_obj_tag(v_r_1707_) == 0)
{
lean_object* v_k_1789_; lean_object* v_v_1790_; lean_object* v_size_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1795_; 
lean_inc(v_tree_1714_);
v_k_1789_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_k_1789_);
v_v_1790_ = lean_ctor_get(v___x_1713_, 1);
lean_inc(v_v_1790_);
lean_dec_ref(v___x_1713_);
v_size_1791_ = lean_ctor_get(v_l_1706_, 0);
v___x_1792_ = lean_nat_add(v___x_1708_, v_size_1703_);
lean_dec(v_size_1703_);
v___x_1793_ = lean_nat_add(v___x_1708_, v_size_1791_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 4, v_l_1706_);
lean_ctor_set(v___x_1787_, 3, v_tree_1714_);
lean_ctor_set(v___x_1787_, 2, v_v_1790_);
lean_ctor_set(v___x_1787_, 1, v_k_1789_);
lean_ctor_set(v___x_1787_, 0, v___x_1793_);
v___x_1795_ = v___x_1787_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1793_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v_k_1789_);
lean_ctor_set(v_reuseFailAlloc_1799_, 2, v_v_1790_);
lean_ctor_set(v_reuseFailAlloc_1799_, 3, v_tree_1714_);
lean_ctor_set(v_reuseFailAlloc_1799_, 4, v_l_1706_);
v___x_1795_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
lean_object* v___x_1797_; 
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 4, v_r_1707_);
lean_ctor_set(v___x_1711_, 3, v___x_1795_);
lean_ctor_set(v___x_1711_, 2, v_v_1705_);
lean_ctor_set(v___x_1711_, 1, v_k_1704_);
lean_ctor_set(v___x_1711_, 0, v___x_1792_);
v___x_1797_ = v___x_1711_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1792_);
lean_ctor_set(v_reuseFailAlloc_1798_, 1, v_k_1704_);
lean_ctor_set(v_reuseFailAlloc_1798_, 2, v_v_1705_);
lean_ctor_set(v_reuseFailAlloc_1798_, 3, v___x_1795_);
lean_ctor_set(v_reuseFailAlloc_1798_, 4, v_r_1707_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
else
{
lean_object* v_k_1800_; lean_object* v_v_1801_; lean_object* v_k_1802_; lean_object* v_v_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1817_; 
lean_dec(v_size_1703_);
v_k_1800_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_k_1800_);
v_v_1801_ = lean_ctor_get(v___x_1713_, 1);
lean_inc(v_v_1801_);
lean_dec_ref(v___x_1713_);
v_k_1802_ = lean_ctor_get(v_l_1706_, 1);
v_v_1803_ = lean_ctor_get(v_l_1706_, 2);
v_isSharedCheck_1817_ = !lean_is_exclusive(v_l_1706_);
if (v_isSharedCheck_1817_ == 0)
{
lean_object* v_unused_1818_; lean_object* v_unused_1819_; lean_object* v_unused_1820_; 
v_unused_1818_ = lean_ctor_get(v_l_1706_, 4);
lean_dec(v_unused_1818_);
v_unused_1819_ = lean_ctor_get(v_l_1706_, 3);
lean_dec(v_unused_1819_);
v_unused_1820_ = lean_ctor_get(v_l_1706_, 0);
lean_dec(v_unused_1820_);
v___x_1805_ = v_l_1706_;
v_isShared_1806_ = v_isSharedCheck_1817_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_v_1803_);
lean_inc(v_k_1802_);
lean_dec(v_l_1706_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1817_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1807_; lean_object* v___x_1809_; 
v___x_1807_ = lean_unsigned_to_nat(3u);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 4, v_r_1707_);
lean_ctor_set(v___x_1805_, 3, v_r_1707_);
lean_ctor_set(v___x_1805_, 2, v_v_1801_);
lean_ctor_set(v___x_1805_, 1, v_k_1800_);
lean_ctor_set(v___x_1805_, 0, v___x_1708_);
v___x_1809_ = v___x_1805_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1708_);
lean_ctor_set(v_reuseFailAlloc_1816_, 1, v_k_1800_);
lean_ctor_set(v_reuseFailAlloc_1816_, 2, v_v_1801_);
lean_ctor_set(v_reuseFailAlloc_1816_, 3, v_r_1707_);
lean_ctor_set(v_reuseFailAlloc_1816_, 4, v_r_1707_);
v___x_1809_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
lean_object* v___x_1811_; 
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 3, v_r_1707_);
lean_ctor_set(v___x_1787_, 0, v___x_1708_);
v___x_1811_ = v___x_1787_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1708_);
lean_ctor_set(v_reuseFailAlloc_1815_, 1, v_k_1704_);
lean_ctor_set(v_reuseFailAlloc_1815_, 2, v_v_1705_);
lean_ctor_set(v_reuseFailAlloc_1815_, 3, v_r_1707_);
lean_ctor_set(v_reuseFailAlloc_1815_, 4, v_r_1707_);
v___x_1811_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
lean_object* v___x_1813_; 
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 4, v___x_1811_);
lean_ctor_set(v___x_1711_, 3, v___x_1809_);
lean_ctor_set(v___x_1711_, 2, v_v_1803_);
lean_ctor_set(v___x_1711_, 1, v_k_1802_);
lean_ctor_set(v___x_1711_, 0, v___x_1807_);
v___x_1813_ = v___x_1711_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1807_);
lean_ctor_set(v_reuseFailAlloc_1814_, 1, v_k_1802_);
lean_ctor_set(v_reuseFailAlloc_1814_, 2, v_v_1803_);
lean_ctor_set(v_reuseFailAlloc_1814_, 3, v___x_1809_);
lean_ctor_set(v_reuseFailAlloc_1814_, 4, v___x_1811_);
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
}
}
else
{
if (lean_obj_tag(v_r_1707_) == 0)
{
lean_object* v_k_1821_; lean_object* v_v_1822_; lean_object* v___x_1823_; lean_object* v___x_1825_; 
lean_dec(v_size_1703_);
v_k_1821_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_k_1821_);
v_v_1822_ = lean_ctor_get(v___x_1713_, 1);
lean_inc(v_v_1822_);
lean_dec_ref(v___x_1713_);
v___x_1823_ = lean_unsigned_to_nat(3u);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 4, v_l_1706_);
lean_ctor_set(v___x_1787_, 2, v_v_1822_);
lean_ctor_set(v___x_1787_, 1, v_k_1821_);
lean_ctor_set(v___x_1787_, 0, v___x_1708_);
v___x_1825_ = v___x_1787_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1708_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_k_1821_);
lean_ctor_set(v_reuseFailAlloc_1829_, 2, v_v_1822_);
lean_ctor_set(v_reuseFailAlloc_1829_, 3, v_l_1706_);
lean_ctor_set(v_reuseFailAlloc_1829_, 4, v_l_1706_);
v___x_1825_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
lean_object* v___x_1827_; 
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 4, v_r_1707_);
lean_ctor_set(v___x_1711_, 3, v___x_1825_);
lean_ctor_set(v___x_1711_, 2, v_v_1705_);
lean_ctor_set(v___x_1711_, 1, v_k_1704_);
lean_ctor_set(v___x_1711_, 0, v___x_1823_);
v___x_1827_ = v___x_1711_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1823_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v_k_1704_);
lean_ctor_set(v_reuseFailAlloc_1828_, 2, v_v_1705_);
lean_ctor_set(v_reuseFailAlloc_1828_, 3, v___x_1825_);
lean_ctor_set(v_reuseFailAlloc_1828_, 4, v_r_1707_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
else
{
lean_object* v_k_1830_; lean_object* v_v_1831_; lean_object* v___x_1833_; 
v_k_1830_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_k_1830_);
v_v_1831_ = lean_ctor_get(v___x_1713_, 1);
lean_inc(v_v_1831_);
lean_dec_ref(v___x_1713_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 3, v_r_1707_);
v___x_1833_ = v___x_1787_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_size_1703_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v_k_1704_);
lean_ctor_set(v_reuseFailAlloc_1838_, 2, v_v_1705_);
lean_ctor_set(v_reuseFailAlloc_1838_, 3, v_r_1707_);
lean_ctor_set(v_reuseFailAlloc_1838_, 4, v_r_1707_);
v___x_1833_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
lean_object* v___x_1834_; lean_object* v___x_1836_; 
v___x_1834_ = lean_unsigned_to_nat(2u);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 4, v___x_1833_);
lean_ctor_set(v___x_1711_, 3, v_r_1707_);
lean_ctor_set(v___x_1711_, 2, v_v_1831_);
lean_ctor_set(v___x_1711_, 1, v_k_1830_);
lean_ctor_set(v___x_1711_, 0, v___x_1834_);
v___x_1836_ = v___x_1711_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1834_);
lean_ctor_set(v_reuseFailAlloc_1837_, 1, v_k_1830_);
lean_ctor_set(v_reuseFailAlloc_1837_, 2, v_v_1831_);
lean_ctor_set(v_reuseFailAlloc_1837_, 3, v_r_1707_);
lean_ctor_set(v_reuseFailAlloc_1837_, 4, v___x_1833_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_2003_; 
lean_inc(v_r_1707_);
lean_inc(v_v_1705_);
lean_inc(v_k_1704_);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_r_1519_);
if (v_isSharedCheck_2003_ == 0)
{
lean_object* v_unused_2004_; lean_object* v_unused_2005_; lean_object* v_unused_2006_; lean_object* v_unused_2007_; lean_object* v_unused_2008_; 
v_unused_2004_ = lean_ctor_get(v_r_1519_, 4);
lean_dec(v_unused_2004_);
v_unused_2005_ = lean_ctor_get(v_r_1519_, 3);
lean_dec(v_unused_2005_);
v_unused_2006_ = lean_ctor_get(v_r_1519_, 2);
lean_dec(v_unused_2006_);
v_unused_2007_ = lean_ctor_get(v_r_1519_, 1);
lean_dec(v_unused_2007_);
v_unused_2008_ = lean_ctor_get(v_r_1519_, 0);
lean_dec(v_unused_2008_);
v___x_1852_ = v_r_1519_;
v_isShared_1853_ = v_isSharedCheck_2003_;
goto v_resetjp_1851_;
}
else
{
lean_dec(v_r_1519_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_2003_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1854_; lean_object* v_tree_1855_; 
v___x_1854_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1704_, v_v_1705_, v_l_1706_, v_r_1707_);
v_tree_1855_ = lean_ctor_get(v___x_1854_, 2);
lean_inc(v_tree_1855_);
if (lean_obj_tag(v_tree_1855_) == 0)
{
lean_object* v_k_1856_; lean_object* v_v_1857_; lean_object* v_size_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; uint8_t v___x_1861_; 
v_k_1856_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_k_1856_);
v_v_1857_ = lean_ctor_get(v___x_1854_, 1);
lean_inc(v_v_1857_);
lean_dec_ref(v___x_1854_);
v_size_1858_ = lean_ctor_get(v_tree_1855_, 0);
v___x_1859_ = lean_unsigned_to_nat(3u);
v___x_1860_ = lean_nat_mul(v___x_1859_, v_size_1858_);
v___x_1861_ = lean_nat_dec_lt(v___x_1860_, v_size_1698_);
lean_dec(v___x_1860_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1865_; 
lean_dec(v_r_1702_);
v___x_1862_ = lean_nat_add(v___x_1708_, v_size_1698_);
v___x_1863_ = lean_nat_add(v___x_1862_, v_size_1858_);
lean_dec(v___x_1862_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 4, v_tree_1855_);
lean_ctor_set(v___x_1852_, 3, v_l_1518_);
lean_ctor_set(v___x_1852_, 2, v_v_1857_);
lean_ctor_set(v___x_1852_, 1, v_k_1856_);
lean_ctor_set(v___x_1852_, 0, v___x_1863_);
v___x_1865_ = v___x_1852_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1863_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_k_1856_);
lean_ctor_set(v_reuseFailAlloc_1866_, 2, v_v_1857_);
lean_ctor_set(v_reuseFailAlloc_1866_, 3, v_l_1518_);
lean_ctor_set(v_reuseFailAlloc_1866_, 4, v_tree_1855_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
else
{
lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1932_; 
lean_inc(v_l_1701_);
lean_inc(v_v_1700_);
lean_inc(v_k_1699_);
lean_inc(v_size_1698_);
v_isSharedCheck_1932_ = !lean_is_exclusive(v_l_1518_);
if (v_isSharedCheck_1932_ == 0)
{
lean_object* v_unused_1933_; lean_object* v_unused_1934_; lean_object* v_unused_1935_; lean_object* v_unused_1936_; lean_object* v_unused_1937_; 
v_unused_1933_ = lean_ctor_get(v_l_1518_, 4);
lean_dec(v_unused_1933_);
v_unused_1934_ = lean_ctor_get(v_l_1518_, 3);
lean_dec(v_unused_1934_);
v_unused_1935_ = lean_ctor_get(v_l_1518_, 2);
lean_dec(v_unused_1935_);
v_unused_1936_ = lean_ctor_get(v_l_1518_, 1);
lean_dec(v_unused_1936_);
v_unused_1937_ = lean_ctor_get(v_l_1518_, 0);
lean_dec(v_unused_1937_);
v___x_1868_ = v_l_1518_;
v_isShared_1869_ = v_isSharedCheck_1932_;
goto v_resetjp_1867_;
}
else
{
lean_dec(v_l_1518_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1932_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v_size_1870_; lean_object* v_size_1871_; lean_object* v_k_1872_; lean_object* v_v_1873_; lean_object* v_l_1874_; lean_object* v_r_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; uint8_t v___x_1878_; 
v_size_1870_ = lean_ctor_get(v_l_1701_, 0);
v_size_1871_ = lean_ctor_get(v_r_1702_, 0);
v_k_1872_ = lean_ctor_get(v_r_1702_, 1);
v_v_1873_ = lean_ctor_get(v_r_1702_, 2);
v_l_1874_ = lean_ctor_get(v_r_1702_, 3);
v_r_1875_ = lean_ctor_get(v_r_1702_, 4);
v___x_1876_ = lean_unsigned_to_nat(2u);
v___x_1877_ = lean_nat_mul(v___x_1876_, v_size_1870_);
v___x_1878_ = lean_nat_dec_lt(v_size_1871_, v___x_1877_);
lean_dec(v___x_1877_);
if (v___x_1878_ == 0)
{
lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1916_; 
lean_inc(v_r_1875_);
lean_inc(v_l_1874_);
lean_inc(v_v_1873_);
lean_inc(v_k_1872_);
lean_del_object(v___x_1868_);
v_isSharedCheck_1916_ = !lean_is_exclusive(v_r_1702_);
if (v_isSharedCheck_1916_ == 0)
{
lean_object* v_unused_1917_; lean_object* v_unused_1918_; lean_object* v_unused_1919_; lean_object* v_unused_1920_; lean_object* v_unused_1921_; 
v_unused_1917_ = lean_ctor_get(v_r_1702_, 4);
lean_dec(v_unused_1917_);
v_unused_1918_ = lean_ctor_get(v_r_1702_, 3);
lean_dec(v_unused_1918_);
v_unused_1919_ = lean_ctor_get(v_r_1702_, 2);
lean_dec(v_unused_1919_);
v_unused_1920_ = lean_ctor_get(v_r_1702_, 1);
lean_dec(v_unused_1920_);
v_unused_1921_ = lean_ctor_get(v_r_1702_, 0);
lean_dec(v_unused_1921_);
v___x_1880_ = v_r_1702_;
v_isShared_1881_ = v_isSharedCheck_1916_;
goto v_resetjp_1879_;
}
else
{
lean_dec(v_r_1702_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1916_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___x_1904_; lean_object* v___y_1906_; 
v___x_1882_ = lean_nat_add(v___x_1708_, v_size_1698_);
lean_dec(v_size_1698_);
v___x_1883_ = lean_nat_add(v___x_1882_, v_size_1858_);
lean_dec(v___x_1882_);
v___x_1904_ = lean_nat_add(v___x_1708_, v_size_1870_);
if (lean_obj_tag(v_l_1874_) == 0)
{
lean_object* v_size_1914_; 
v_size_1914_ = lean_ctor_get(v_l_1874_, 0);
lean_inc(v_size_1914_);
v___y_1906_ = v_size_1914_;
goto v___jp_1905_;
}
else
{
lean_object* v___x_1915_; 
v___x_1915_ = lean_unsigned_to_nat(0u);
v___y_1906_ = v___x_1915_;
goto v___jp_1905_;
}
v___jp_1884_:
{
lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1888_ = lean_nat_add(v___y_1886_, v___y_1887_);
lean_dec(v___y_1887_);
lean_dec(v___y_1886_);
lean_inc_ref(v_tree_1855_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 4, v_tree_1855_);
lean_ctor_set(v___x_1880_, 3, v_r_1875_);
lean_ctor_set(v___x_1880_, 2, v_v_1857_);
lean_ctor_set(v___x_1880_, 1, v_k_1856_);
lean_ctor_set(v___x_1880_, 0, v___x_1888_);
v___x_1890_ = v___x_1880_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_k_1856_);
lean_ctor_set(v_reuseFailAlloc_1903_, 2, v_v_1857_);
lean_ctor_set(v_reuseFailAlloc_1903_, 3, v_r_1875_);
lean_ctor_set(v_reuseFailAlloc_1903_, 4, v_tree_1855_);
v___x_1890_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
v_isSharedCheck_1897_ = !lean_is_exclusive(v_tree_1855_);
if (v_isSharedCheck_1897_ == 0)
{
lean_object* v_unused_1898_; lean_object* v_unused_1899_; lean_object* v_unused_1900_; lean_object* v_unused_1901_; lean_object* v_unused_1902_; 
v_unused_1898_ = lean_ctor_get(v_tree_1855_, 4);
lean_dec(v_unused_1898_);
v_unused_1899_ = lean_ctor_get(v_tree_1855_, 3);
lean_dec(v_unused_1899_);
v_unused_1900_ = lean_ctor_get(v_tree_1855_, 2);
lean_dec(v_unused_1900_);
v_unused_1901_ = lean_ctor_get(v_tree_1855_, 1);
lean_dec(v_unused_1901_);
v_unused_1902_ = lean_ctor_get(v_tree_1855_, 0);
lean_dec(v_unused_1902_);
v___x_1892_ = v_tree_1855_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_dec(v_tree_1855_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 4, v___x_1890_);
lean_ctor_set(v___x_1892_, 3, v___y_1885_);
lean_ctor_set(v___x_1892_, 2, v_v_1873_);
lean_ctor_set(v___x_1892_, 1, v_k_1872_);
lean_ctor_set(v___x_1892_, 0, v___x_1883_);
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1883_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_k_1872_);
lean_ctor_set(v_reuseFailAlloc_1896_, 2, v_v_1873_);
lean_ctor_set(v_reuseFailAlloc_1896_, 3, v___y_1885_);
lean_ctor_set(v_reuseFailAlloc_1896_, 4, v___x_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
v___jp_1905_:
{
lean_object* v___x_1907_; lean_object* v___x_1909_; 
v___x_1907_ = lean_nat_add(v___x_1904_, v___y_1906_);
lean_dec(v___y_1906_);
lean_dec(v___x_1904_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 4, v_l_1874_);
lean_ctor_set(v___x_1852_, 3, v_l_1701_);
lean_ctor_set(v___x_1852_, 2, v_v_1700_);
lean_ctor_set(v___x_1852_, 1, v_k_1699_);
lean_ctor_set(v___x_1852_, 0, v___x_1907_);
v___x_1909_ = v___x_1852_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1907_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_k_1699_);
lean_ctor_set(v_reuseFailAlloc_1913_, 2, v_v_1700_);
lean_ctor_set(v_reuseFailAlloc_1913_, 3, v_l_1701_);
lean_ctor_set(v_reuseFailAlloc_1913_, 4, v_l_1874_);
v___x_1909_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
lean_object* v___x_1910_; 
v___x_1910_ = lean_nat_add(v___x_1708_, v_size_1858_);
if (lean_obj_tag(v_r_1875_) == 0)
{
lean_object* v_size_1911_; 
v_size_1911_ = lean_ctor_get(v_r_1875_, 0);
lean_inc(v_size_1911_);
v___y_1885_ = v___x_1909_;
v___y_1886_ = v___x_1910_;
v___y_1887_ = v_size_1911_;
goto v___jp_1884_;
}
else
{
lean_object* v___x_1912_; 
v___x_1912_ = lean_unsigned_to_nat(0u);
v___y_1885_ = v___x_1909_;
v___y_1886_ = v___x_1910_;
v___y_1887_ = v___x_1912_;
goto v___jp_1884_;
}
}
}
}
}
else
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1922_ = lean_nat_add(v___x_1708_, v_size_1698_);
lean_dec(v_size_1698_);
v___x_1923_ = lean_nat_add(v___x_1922_, v_size_1858_);
lean_dec(v___x_1922_);
v___x_1924_ = lean_nat_add(v___x_1708_, v_size_1858_);
v___x_1925_ = lean_nat_add(v___x_1924_, v_size_1871_);
lean_dec(v___x_1924_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 4, v_tree_1855_);
lean_ctor_set(v___x_1852_, 3, v_r_1702_);
lean_ctor_set(v___x_1852_, 2, v_v_1857_);
lean_ctor_set(v___x_1852_, 1, v_k_1856_);
lean_ctor_set(v___x_1852_, 0, v___x_1925_);
v___x_1927_ = v___x_1852_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1925_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_k_1856_);
lean_ctor_set(v_reuseFailAlloc_1931_, 2, v_v_1857_);
lean_ctor_set(v_reuseFailAlloc_1931_, 3, v_r_1702_);
lean_ctor_set(v_reuseFailAlloc_1931_, 4, v_tree_1855_);
v___x_1927_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
lean_object* v___x_1929_; 
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 4, v___x_1927_);
lean_ctor_set(v___x_1868_, 0, v___x_1923_);
v___x_1929_ = v___x_1868_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1923_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_k_1699_);
lean_ctor_set(v_reuseFailAlloc_1930_, 2, v_v_1700_);
lean_ctor_set(v_reuseFailAlloc_1930_, 3, v_l_1701_);
lean_ctor_set(v_reuseFailAlloc_1930_, 4, v___x_1927_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1701_) == 0)
{
lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1961_; 
lean_inc_ref(v_l_1701_);
lean_inc(v_v_1700_);
lean_inc(v_k_1699_);
lean_inc(v_size_1698_);
v_isSharedCheck_1961_ = !lean_is_exclusive(v_l_1518_);
if (v_isSharedCheck_1961_ == 0)
{
lean_object* v_unused_1962_; lean_object* v_unused_1963_; lean_object* v_unused_1964_; lean_object* v_unused_1965_; lean_object* v_unused_1966_; 
v_unused_1962_ = lean_ctor_get(v_l_1518_, 4);
lean_dec(v_unused_1962_);
v_unused_1963_ = lean_ctor_get(v_l_1518_, 3);
lean_dec(v_unused_1963_);
v_unused_1964_ = lean_ctor_get(v_l_1518_, 2);
lean_dec(v_unused_1964_);
v_unused_1965_ = lean_ctor_get(v_l_1518_, 1);
lean_dec(v_unused_1965_);
v_unused_1966_ = lean_ctor_get(v_l_1518_, 0);
lean_dec(v_unused_1966_);
v___x_1939_ = v_l_1518_;
v_isShared_1940_ = v_isSharedCheck_1961_;
goto v_resetjp_1938_;
}
else
{
lean_dec(v_l_1518_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1961_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
if (lean_obj_tag(v_r_1702_) == 0)
{
lean_object* v_k_1941_; lean_object* v_v_1942_; lean_object* v_size_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1947_; 
v_k_1941_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_k_1941_);
v_v_1942_ = lean_ctor_get(v___x_1854_, 1);
lean_inc(v_v_1942_);
lean_dec_ref(v___x_1854_);
v_size_1943_ = lean_ctor_get(v_r_1702_, 0);
v___x_1944_ = lean_nat_add(v___x_1708_, v_size_1698_);
lean_dec(v_size_1698_);
v___x_1945_ = lean_nat_add(v___x_1708_, v_size_1943_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 4, v_tree_1855_);
lean_ctor_set(v___x_1852_, 3, v_r_1702_);
lean_ctor_set(v___x_1852_, 2, v_v_1942_);
lean_ctor_set(v___x_1852_, 1, v_k_1941_);
lean_ctor_set(v___x_1852_, 0, v___x_1945_);
v___x_1947_ = v___x_1852_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v___x_1945_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_1951_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_1951_, 3, v_r_1702_);
lean_ctor_set(v_reuseFailAlloc_1951_, 4, v_tree_1855_);
v___x_1947_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
lean_object* v___x_1949_; 
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 4, v___x_1947_);
lean_ctor_set(v___x_1939_, 0, v___x_1944_);
v___x_1949_ = v___x_1939_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1944_);
lean_ctor_set(v_reuseFailAlloc_1950_, 1, v_k_1699_);
lean_ctor_set(v_reuseFailAlloc_1950_, 2, v_v_1700_);
lean_ctor_set(v_reuseFailAlloc_1950_, 3, v_l_1701_);
lean_ctor_set(v_reuseFailAlloc_1950_, 4, v___x_1947_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
else
{
lean_object* v_k_1952_; lean_object* v_v_1953_; lean_object* v___x_1954_; lean_object* v___x_1956_; 
lean_dec(v_size_1698_);
v_k_1952_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_k_1952_);
v_v_1953_ = lean_ctor_get(v___x_1854_, 1);
lean_inc(v_v_1953_);
lean_dec_ref(v___x_1854_);
v___x_1954_ = lean_unsigned_to_nat(3u);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 4, v_r_1702_);
lean_ctor_set(v___x_1852_, 3, v_r_1702_);
lean_ctor_set(v___x_1852_, 2, v_v_1953_);
lean_ctor_set(v___x_1852_, 1, v_k_1952_);
lean_ctor_set(v___x_1852_, 0, v___x_1708_);
v___x_1956_ = v___x_1852_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1708_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v_k_1952_);
lean_ctor_set(v_reuseFailAlloc_1960_, 2, v_v_1953_);
lean_ctor_set(v_reuseFailAlloc_1960_, 3, v_r_1702_);
lean_ctor_set(v_reuseFailAlloc_1960_, 4, v_r_1702_);
v___x_1956_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
lean_object* v___x_1958_; 
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 4, v___x_1956_);
lean_ctor_set(v___x_1939_, 0, v___x_1954_);
v___x_1958_ = v___x_1939_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1954_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v_k_1699_);
lean_ctor_set(v_reuseFailAlloc_1959_, 2, v_v_1700_);
lean_ctor_set(v_reuseFailAlloc_1959_, 3, v_l_1701_);
lean_ctor_set(v_reuseFailAlloc_1959_, 4, v___x_1956_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1702_) == 0)
{
lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1991_; 
lean_inc(v_l_1701_);
lean_inc(v_v_1700_);
lean_inc(v_k_1699_);
v_isSharedCheck_1991_ = !lean_is_exclusive(v_l_1518_);
if (v_isSharedCheck_1991_ == 0)
{
lean_object* v_unused_1992_; lean_object* v_unused_1993_; lean_object* v_unused_1994_; lean_object* v_unused_1995_; lean_object* v_unused_1996_; 
v_unused_1992_ = lean_ctor_get(v_l_1518_, 4);
lean_dec(v_unused_1992_);
v_unused_1993_ = lean_ctor_get(v_l_1518_, 3);
lean_dec(v_unused_1993_);
v_unused_1994_ = lean_ctor_get(v_l_1518_, 2);
lean_dec(v_unused_1994_);
v_unused_1995_ = lean_ctor_get(v_l_1518_, 1);
lean_dec(v_unused_1995_);
v_unused_1996_ = lean_ctor_get(v_l_1518_, 0);
lean_dec(v_unused_1996_);
v___x_1968_ = v_l_1518_;
v_isShared_1969_ = v_isSharedCheck_1991_;
goto v_resetjp_1967_;
}
else
{
lean_dec(v_l_1518_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1991_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v_k_1970_; lean_object* v_v_1971_; lean_object* v_k_1972_; lean_object* v_v_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1987_; 
v_k_1970_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_k_1970_);
v_v_1971_ = lean_ctor_get(v___x_1854_, 1);
lean_inc(v_v_1971_);
lean_dec_ref(v___x_1854_);
v_k_1972_ = lean_ctor_get(v_r_1702_, 1);
v_v_1973_ = lean_ctor_get(v_r_1702_, 2);
v_isSharedCheck_1987_ = !lean_is_exclusive(v_r_1702_);
if (v_isSharedCheck_1987_ == 0)
{
lean_object* v_unused_1988_; lean_object* v_unused_1989_; lean_object* v_unused_1990_; 
v_unused_1988_ = lean_ctor_get(v_r_1702_, 4);
lean_dec(v_unused_1988_);
v_unused_1989_ = lean_ctor_get(v_r_1702_, 3);
lean_dec(v_unused_1989_);
v_unused_1990_ = lean_ctor_get(v_r_1702_, 0);
lean_dec(v_unused_1990_);
v___x_1975_ = v_r_1702_;
v_isShared_1976_ = v_isSharedCheck_1987_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_v_1973_);
lean_inc(v_k_1972_);
lean_dec(v_r_1702_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1987_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1977_ = lean_unsigned_to_nat(3u);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 4, v_l_1701_);
lean_ctor_set(v___x_1975_, 3, v_l_1701_);
lean_ctor_set(v___x_1975_, 2, v_v_1700_);
lean_ctor_set(v___x_1975_, 1, v_k_1699_);
lean_ctor_set(v___x_1975_, 0, v___x_1708_);
v___x_1979_ = v___x_1975_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1708_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v_k_1699_);
lean_ctor_set(v_reuseFailAlloc_1986_, 2, v_v_1700_);
lean_ctor_set(v_reuseFailAlloc_1986_, 3, v_l_1701_);
lean_ctor_set(v_reuseFailAlloc_1986_, 4, v_l_1701_);
v___x_1979_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1981_; 
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 4, v_l_1701_);
lean_ctor_set(v___x_1852_, 3, v_l_1701_);
lean_ctor_set(v___x_1852_, 2, v_v_1971_);
lean_ctor_set(v___x_1852_, 1, v_k_1970_);
lean_ctor_set(v___x_1852_, 0, v___x_1708_);
v___x_1981_ = v___x_1852_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1708_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v_k_1970_);
lean_ctor_set(v_reuseFailAlloc_1985_, 2, v_v_1971_);
lean_ctor_set(v_reuseFailAlloc_1985_, 3, v_l_1701_);
lean_ctor_set(v_reuseFailAlloc_1985_, 4, v_l_1701_);
v___x_1981_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
lean_object* v___x_1983_; 
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 4, v___x_1981_);
lean_ctor_set(v___x_1968_, 3, v___x_1979_);
lean_ctor_set(v___x_1968_, 2, v_v_1973_);
lean_ctor_set(v___x_1968_, 1, v_k_1972_);
lean_ctor_set(v___x_1968_, 0, v___x_1977_);
v___x_1983_ = v___x_1968_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1977_);
lean_ctor_set(v_reuseFailAlloc_1984_, 1, v_k_1972_);
lean_ctor_set(v_reuseFailAlloc_1984_, 2, v_v_1973_);
lean_ctor_set(v_reuseFailAlloc_1984_, 3, v___x_1979_);
lean_ctor_set(v_reuseFailAlloc_1984_, 4, v___x_1981_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
}
}
else
{
lean_object* v_k_1997_; lean_object* v_v_1998_; lean_object* v___x_1999_; lean_object* v___x_2001_; 
v_k_1997_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_k_1997_);
v_v_1998_ = lean_ctor_get(v___x_1854_, 1);
lean_inc(v_v_1998_);
lean_dec_ref(v___x_1854_);
v___x_1999_ = lean_unsigned_to_nat(2u);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 4, v_r_1702_);
lean_ctor_set(v___x_1852_, 3, v_l_1518_);
lean_ctor_set(v___x_1852_, 2, v_v_1998_);
lean_ctor_set(v___x_1852_, 1, v_k_1997_);
lean_ctor_set(v___x_1852_, 0, v___x_1999_);
v___x_2001_ = v___x_1852_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1999_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v_k_1997_);
lean_ctor_set(v_reuseFailAlloc_2002_, 2, v_v_1998_);
lean_ctor_set(v_reuseFailAlloc_2002_, 3, v_l_1518_);
lean_ctor_set(v_reuseFailAlloc_2002_, 4, v_r_1702_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
}
}
}
else
{
return v_l_1518_;
}
}
else
{
return v_r_1519_;
}
}
default: 
{
lean_object* v_impl_2009_; lean_object* v___x_2010_; 
v_impl_2009_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1514_, v_r_1519_);
v___x_2010_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2009_) == 0)
{
if (lean_obj_tag(v_l_1518_) == 0)
{
lean_object* v_size_2011_; lean_object* v_size_2012_; lean_object* v_k_2013_; lean_object* v_v_2014_; lean_object* v_l_2015_; lean_object* v_r_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; uint8_t v___x_2019_; 
v_size_2011_ = lean_ctor_get(v_impl_2009_, 0);
v_size_2012_ = lean_ctor_get(v_l_1518_, 0);
v_k_2013_ = lean_ctor_get(v_l_1518_, 1);
v_v_2014_ = lean_ctor_get(v_l_1518_, 2);
v_l_2015_ = lean_ctor_get(v_l_1518_, 3);
v_r_2016_ = lean_ctor_get(v_l_1518_, 4);
lean_inc(v_r_2016_);
v___x_2017_ = lean_unsigned_to_nat(3u);
v___x_2018_ = lean_nat_mul(v___x_2017_, v_size_2011_);
v___x_2019_ = lean_nat_dec_lt(v___x_2018_, v_size_2012_);
lean_dec(v___x_2018_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2023_; 
lean_dec(v_r_2016_);
v___x_2020_ = lean_nat_add(v___x_2010_, v_size_2012_);
v___x_2021_ = lean_nat_add(v___x_2020_, v_size_2011_);
lean_dec(v___x_2020_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 4, v_impl_2009_);
lean_ctor_set(v___x_1521_, 0, v___x_2021_);
v___x_2023_ = v___x_1521_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2021_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_k_1516_);
lean_ctor_set(v_reuseFailAlloc_2024_, 2, v_v_1517_);
lean_ctor_set(v_reuseFailAlloc_2024_, 3, v_l_1518_);
lean_ctor_set(v_reuseFailAlloc_2024_, 4, v_impl_2009_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
else
{
lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2090_; 
lean_inc(v_l_2015_);
lean_inc(v_v_2014_);
lean_inc(v_k_2013_);
lean_inc(v_size_2012_);
v_isSharedCheck_2090_ = !lean_is_exclusive(v_l_1518_);
if (v_isSharedCheck_2090_ == 0)
{
lean_object* v_unused_2091_; lean_object* v_unused_2092_; lean_object* v_unused_2093_; lean_object* v_unused_2094_; lean_object* v_unused_2095_; 
v_unused_2091_ = lean_ctor_get(v_l_1518_, 4);
lean_dec(v_unused_2091_);
v_unused_2092_ = lean_ctor_get(v_l_1518_, 3);
lean_dec(v_unused_2092_);
v_unused_2093_ = lean_ctor_get(v_l_1518_, 2);
lean_dec(v_unused_2093_);
v_unused_2094_ = lean_ctor_get(v_l_1518_, 1);
lean_dec(v_unused_2094_);
v_unused_2095_ = lean_ctor_get(v_l_1518_, 0);
lean_dec(v_unused_2095_);
v___x_2026_ = v_l_1518_;
v_isShared_2027_ = v_isSharedCheck_2090_;
goto v_resetjp_2025_;
}
else
{
lean_dec(v_l_1518_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2090_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v_size_2028_; lean_object* v_size_2029_; lean_object* v_k_2030_; lean_object* v_v_2031_; lean_object* v_l_2032_; lean_object* v_r_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; uint8_t v___x_2036_; 
v_size_2028_ = lean_ctor_get(v_l_2015_, 0);
v_size_2029_ = lean_ctor_get(v_r_2016_, 0);
v_k_2030_ = lean_ctor_get(v_r_2016_, 1);
v_v_2031_ = lean_ctor_get(v_r_2016_, 2);
v_l_2032_ = lean_ctor_get(v_r_2016_, 3);
v_r_2033_ = lean_ctor_get(v_r_2016_, 4);
v___x_2034_ = lean_unsigned_to_nat(2u);
v___x_2035_ = lean_nat_mul(v___x_2034_, v_size_2028_);
v___x_2036_ = lean_nat_dec_lt(v_size_2029_, v___x_2035_);
lean_dec(v___x_2035_);
if (v___x_2036_ == 0)
{
lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2065_; 
lean_inc(v_r_2033_);
lean_inc(v_l_2032_);
lean_inc(v_v_2031_);
lean_inc(v_k_2030_);
v_isSharedCheck_2065_ = !lean_is_exclusive(v_r_2016_);
if (v_isSharedCheck_2065_ == 0)
{
lean_object* v_unused_2066_; lean_object* v_unused_2067_; lean_object* v_unused_2068_; lean_object* v_unused_2069_; lean_object* v_unused_2070_; 
v_unused_2066_ = lean_ctor_get(v_r_2016_, 4);
lean_dec(v_unused_2066_);
v_unused_2067_ = lean_ctor_get(v_r_2016_, 3);
lean_dec(v_unused_2067_);
v_unused_2068_ = lean_ctor_get(v_r_2016_, 2);
lean_dec(v_unused_2068_);
v_unused_2069_ = lean_ctor_get(v_r_2016_, 1);
lean_dec(v_unused_2069_);
v_unused_2070_ = lean_ctor_get(v_r_2016_, 0);
lean_dec(v_unused_2070_);
v___x_2038_ = v_r_2016_;
v_isShared_2039_ = v_isSharedCheck_2065_;
goto v_resetjp_2037_;
}
else
{
lean_dec(v_r_2016_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2065_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___x_2053_; lean_object* v___y_2055_; 
v___x_2040_ = lean_nat_add(v___x_2010_, v_size_2012_);
lean_dec(v_size_2012_);
v___x_2041_ = lean_nat_add(v___x_2040_, v_size_2011_);
lean_dec(v___x_2040_);
v___x_2053_ = lean_nat_add(v___x_2010_, v_size_2028_);
if (lean_obj_tag(v_l_2032_) == 0)
{
lean_object* v_size_2063_; 
v_size_2063_ = lean_ctor_get(v_l_2032_, 0);
lean_inc(v_size_2063_);
v___y_2055_ = v_size_2063_;
goto v___jp_2054_;
}
else
{
lean_object* v___x_2064_; 
v___x_2064_ = lean_unsigned_to_nat(0u);
v___y_2055_ = v___x_2064_;
goto v___jp_2054_;
}
v___jp_2042_:
{
lean_object* v___x_2046_; lean_object* v___x_2048_; 
v___x_2046_ = lean_nat_add(v___y_2044_, v___y_2045_);
lean_dec(v___y_2045_);
lean_dec(v___y_2044_);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 4, v_impl_2009_);
lean_ctor_set(v___x_2038_, 3, v_r_2033_);
lean_ctor_set(v___x_2038_, 2, v_v_1517_);
lean_ctor_set(v___x_2038_, 1, v_k_1516_);
lean_ctor_set(v___x_2038_, 0, v___x_2046_);
v___x_2048_ = v___x_2038_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2046_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_k_1516_);
lean_ctor_set(v_reuseFailAlloc_2052_, 2, v_v_1517_);
lean_ctor_set(v_reuseFailAlloc_2052_, 3, v_r_2033_);
lean_ctor_set(v_reuseFailAlloc_2052_, 4, v_impl_2009_);
v___x_2048_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_object* v___x_2050_; 
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 4, v___x_2048_);
lean_ctor_set(v___x_2026_, 3, v___y_2043_);
lean_ctor_set(v___x_2026_, 2, v_v_2031_);
lean_ctor_set(v___x_2026_, 1, v_k_2030_);
lean_ctor_set(v___x_2026_, 0, v___x_2041_);
v___x_2050_ = v___x_2026_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2041_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v_k_2030_);
lean_ctor_set(v_reuseFailAlloc_2051_, 2, v_v_2031_);
lean_ctor_set(v_reuseFailAlloc_2051_, 3, v___y_2043_);
lean_ctor_set(v_reuseFailAlloc_2051_, 4, v___x_2048_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
v___jp_2054_:
{
lean_object* v___x_2056_; lean_object* v___x_2058_; 
v___x_2056_ = lean_nat_add(v___x_2053_, v___y_2055_);
lean_dec(v___y_2055_);
lean_dec(v___x_2053_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 4, v_l_2032_);
lean_ctor_set(v___x_1521_, 3, v_l_2015_);
lean_ctor_set(v___x_1521_, 2, v_v_2014_);
lean_ctor_set(v___x_1521_, 1, v_k_2013_);
lean_ctor_set(v___x_1521_, 0, v___x_2056_);
v___x_2058_ = v___x_1521_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2056_);
lean_ctor_set(v_reuseFailAlloc_2062_, 1, v_k_2013_);
lean_ctor_set(v_reuseFailAlloc_2062_, 2, v_v_2014_);
lean_ctor_set(v_reuseFailAlloc_2062_, 3, v_l_2015_);
lean_ctor_set(v_reuseFailAlloc_2062_, 4, v_l_2032_);
v___x_2058_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
lean_object* v___x_2059_; 
v___x_2059_ = lean_nat_add(v___x_2010_, v_size_2011_);
if (lean_obj_tag(v_r_2033_) == 0)
{
lean_object* v_size_2060_; 
v_size_2060_ = lean_ctor_get(v_r_2033_, 0);
lean_inc(v_size_2060_);
v___y_2043_ = v___x_2058_;
v___y_2044_ = v___x_2059_;
v___y_2045_ = v_size_2060_;
goto v___jp_2042_;
}
else
{
lean_object* v___x_2061_; 
v___x_2061_ = lean_unsigned_to_nat(0u);
v___y_2043_ = v___x_2058_;
v___y_2044_ = v___x_2059_;
v___y_2045_ = v___x_2061_;
goto v___jp_2042_;
}
}
}
}
}
else
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2076_; 
lean_del_object(v___x_1521_);
v___x_2071_ = lean_nat_add(v___x_2010_, v_size_2012_);
lean_dec(v_size_2012_);
v___x_2072_ = lean_nat_add(v___x_2071_, v_size_2011_);
lean_dec(v___x_2071_);
v___x_2073_ = lean_nat_add(v___x_2010_, v_size_2011_);
v___x_2074_ = lean_nat_add(v___x_2073_, v_size_2029_);
lean_dec(v___x_2073_);
lean_inc_ref(v_impl_2009_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 4, v_impl_2009_);
lean_ctor_set(v___x_2026_, 3, v_r_2016_);
lean_ctor_set(v___x_2026_, 2, v_v_1517_);
lean_ctor_set(v___x_2026_, 1, v_k_1516_);
lean_ctor_set(v___x_2026_, 0, v___x_2074_);
v___x_2076_ = v___x_2026_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2074_);
lean_ctor_set(v_reuseFailAlloc_2089_, 1, v_k_1516_);
lean_ctor_set(v_reuseFailAlloc_2089_, 2, v_v_1517_);
lean_ctor_set(v_reuseFailAlloc_2089_, 3, v_r_2016_);
lean_ctor_set(v_reuseFailAlloc_2089_, 4, v_impl_2009_);
v___x_2076_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
v_isSharedCheck_2083_ = !lean_is_exclusive(v_impl_2009_);
if (v_isSharedCheck_2083_ == 0)
{
lean_object* v_unused_2084_; lean_object* v_unused_2085_; lean_object* v_unused_2086_; lean_object* v_unused_2087_; lean_object* v_unused_2088_; 
v_unused_2084_ = lean_ctor_get(v_impl_2009_, 4);
lean_dec(v_unused_2084_);
v_unused_2085_ = lean_ctor_get(v_impl_2009_, 3);
lean_dec(v_unused_2085_);
v_unused_2086_ = lean_ctor_get(v_impl_2009_, 2);
lean_dec(v_unused_2086_);
v_unused_2087_ = lean_ctor_get(v_impl_2009_, 1);
lean_dec(v_unused_2087_);
v_unused_2088_ = lean_ctor_get(v_impl_2009_, 0);
lean_dec(v_unused_2088_);
v___x_2078_ = v_impl_2009_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_dec(v_impl_2009_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 4, v___x_2076_);
lean_ctor_set(v___x_2078_, 3, v_l_2015_);
lean_ctor_set(v___x_2078_, 2, v_v_2014_);
lean_ctor_set(v___x_2078_, 1, v_k_2013_);
lean_ctor_set(v___x_2078_, 0, v___x_2072_);
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2072_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v_k_2013_);
lean_ctor_set(v_reuseFailAlloc_2082_, 2, v_v_2014_);
lean_ctor_set(v_reuseFailAlloc_2082_, 3, v_l_2015_);
lean_ctor_set(v_reuseFailAlloc_2082_, 4, v___x_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2096_; lean_object* v___x_2097_; lean_object* v___x_2099_; 
v_size_2096_ = lean_ctor_get(v_impl_2009_, 0);
v___x_2097_ = lean_nat_add(v___x_2010_, v_size_2096_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 4, v_impl_2009_);
lean_ctor_set(v___x_1521_, 0, v___x_2097_);
v___x_2099_ = v___x_1521_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2097_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v_k_1516_);
lean_ctor_set(v_reuseFailAlloc_2100_, 2, v_v_1517_);
lean_ctor_set(v_reuseFailAlloc_2100_, 3, v_l_1518_);
lean_ctor_set(v_reuseFailAlloc_2100_, 4, v_impl_2009_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
else
{
if (lean_obj_tag(v_l_1518_) == 0)
{
lean_object* v_l_2101_; 
v_l_2101_ = lean_ctor_get(v_l_1518_, 3);
if (lean_obj_tag(v_l_2101_) == 0)
{
lean_object* v_r_2102_; 
lean_inc_ref(v_l_2101_);
v_r_2102_ = lean_ctor_get(v_l_1518_, 4);
lean_inc(v_r_2102_);
if (lean_obj_tag(v_r_2102_) == 0)
{
lean_object* v_size_2103_; lean_object* v_k_2104_; lean_object* v_v_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2118_; 
v_size_2103_ = lean_ctor_get(v_l_1518_, 0);
v_k_2104_ = lean_ctor_get(v_l_1518_, 1);
v_v_2105_ = lean_ctor_get(v_l_1518_, 2);
v_isSharedCheck_2118_ = !lean_is_exclusive(v_l_1518_);
if (v_isSharedCheck_2118_ == 0)
{
lean_object* v_unused_2119_; lean_object* v_unused_2120_; 
v_unused_2119_ = lean_ctor_get(v_l_1518_, 4);
lean_dec(v_unused_2119_);
v_unused_2120_ = lean_ctor_get(v_l_1518_, 3);
lean_dec(v_unused_2120_);
v___x_2107_ = v_l_1518_;
v_isShared_2108_ = v_isSharedCheck_2118_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_v_2105_);
lean_inc(v_k_2104_);
lean_inc(v_size_2103_);
lean_dec(v_l_1518_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2118_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v_size_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2113_; 
v_size_2109_ = lean_ctor_get(v_r_2102_, 0);
v___x_2110_ = lean_nat_add(v___x_2010_, v_size_2103_);
lean_dec(v_size_2103_);
v___x_2111_ = lean_nat_add(v___x_2010_, v_size_2109_);
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 4, v_impl_2009_);
lean_ctor_set(v___x_2107_, 3, v_r_2102_);
lean_ctor_set(v___x_2107_, 2, v_v_1517_);
lean_ctor_set(v___x_2107_, 1, v_k_1516_);
lean_ctor_set(v___x_2107_, 0, v___x_2111_);
v___x_2113_ = v___x_2107_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2111_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_k_1516_);
lean_ctor_set(v_reuseFailAlloc_2117_, 2, v_v_1517_);
lean_ctor_set(v_reuseFailAlloc_2117_, 3, v_r_2102_);
lean_ctor_set(v_reuseFailAlloc_2117_, 4, v_impl_2009_);
v___x_2113_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v___x_2115_; 
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 4, v___x_2113_);
lean_ctor_set(v___x_1521_, 3, v_l_2101_);
lean_ctor_set(v___x_1521_, 2, v_v_2105_);
lean_ctor_set(v___x_1521_, 1, v_k_2104_);
lean_ctor_set(v___x_1521_, 0, v___x_2110_);
v___x_2115_ = v___x_1521_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2110_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_k_2104_);
lean_ctor_set(v_reuseFailAlloc_2116_, 2, v_v_2105_);
lean_ctor_set(v_reuseFailAlloc_2116_, 3, v_l_2101_);
lean_ctor_set(v_reuseFailAlloc_2116_, 4, v___x_2113_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
else
{
lean_object* v_k_2121_; lean_object* v_v_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2133_; 
v_k_2121_ = lean_ctor_get(v_l_1518_, 1);
v_v_2122_ = lean_ctor_get(v_l_1518_, 2);
v_isSharedCheck_2133_ = !lean_is_exclusive(v_l_1518_);
if (v_isSharedCheck_2133_ == 0)
{
lean_object* v_unused_2134_; lean_object* v_unused_2135_; lean_object* v_unused_2136_; 
v_unused_2134_ = lean_ctor_get(v_l_1518_, 4);
lean_dec(v_unused_2134_);
v_unused_2135_ = lean_ctor_get(v_l_1518_, 3);
lean_dec(v_unused_2135_);
v_unused_2136_ = lean_ctor_get(v_l_1518_, 0);
lean_dec(v_unused_2136_);
v___x_2124_ = v_l_1518_;
v_isShared_2125_ = v_isSharedCheck_2133_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_v_2122_);
lean_inc(v_k_2121_);
lean_dec(v_l_1518_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2133_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; lean_object* v___x_2128_; 
v___x_2126_ = lean_unsigned_to_nat(3u);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 3, v_r_2102_);
lean_ctor_set(v___x_2124_, 2, v_v_1517_);
lean_ctor_set(v___x_2124_, 1, v_k_1516_);
lean_ctor_set(v___x_2124_, 0, v___x_2010_);
v___x_2128_ = v___x_2124_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2010_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v_k_1516_);
lean_ctor_set(v_reuseFailAlloc_2132_, 2, v_v_1517_);
lean_ctor_set(v_reuseFailAlloc_2132_, 3, v_r_2102_);
lean_ctor_set(v_reuseFailAlloc_2132_, 4, v_r_2102_);
v___x_2128_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
lean_object* v___x_2130_; 
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 4, v___x_2128_);
lean_ctor_set(v___x_1521_, 3, v_l_2101_);
lean_ctor_set(v___x_1521_, 2, v_v_2122_);
lean_ctor_set(v___x_1521_, 1, v_k_2121_);
lean_ctor_set(v___x_1521_, 0, v___x_2126_);
v___x_2130_ = v___x_1521_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2126_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_k_2121_);
lean_ctor_set(v_reuseFailAlloc_2131_, 2, v_v_2122_);
lean_ctor_set(v_reuseFailAlloc_2131_, 3, v_l_2101_);
lean_ctor_set(v_reuseFailAlloc_2131_, 4, v___x_2128_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
}
else
{
lean_object* v_r_2137_; 
v_r_2137_ = lean_ctor_get(v_l_1518_, 4);
lean_inc(v_r_2137_);
if (lean_obj_tag(v_r_2137_) == 0)
{
lean_object* v_k_2138_; lean_object* v_v_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2162_; 
lean_inc(v_l_2101_);
v_k_2138_ = lean_ctor_get(v_l_1518_, 1);
v_v_2139_ = lean_ctor_get(v_l_1518_, 2);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_l_1518_);
if (v_isSharedCheck_2162_ == 0)
{
lean_object* v_unused_2163_; lean_object* v_unused_2164_; lean_object* v_unused_2165_; 
v_unused_2163_ = lean_ctor_get(v_l_1518_, 4);
lean_dec(v_unused_2163_);
v_unused_2164_ = lean_ctor_get(v_l_1518_, 3);
lean_dec(v_unused_2164_);
v_unused_2165_ = lean_ctor_get(v_l_1518_, 0);
lean_dec(v_unused_2165_);
v___x_2141_ = v_l_1518_;
v_isShared_2142_ = v_isSharedCheck_2162_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_v_2139_);
lean_inc(v_k_2138_);
lean_dec(v_l_1518_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2162_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v_k_2143_; lean_object* v_v_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2158_; 
v_k_2143_ = lean_ctor_get(v_r_2137_, 1);
v_v_2144_ = lean_ctor_get(v_r_2137_, 2);
v_isSharedCheck_2158_ = !lean_is_exclusive(v_r_2137_);
if (v_isSharedCheck_2158_ == 0)
{
lean_object* v_unused_2159_; lean_object* v_unused_2160_; lean_object* v_unused_2161_; 
v_unused_2159_ = lean_ctor_get(v_r_2137_, 4);
lean_dec(v_unused_2159_);
v_unused_2160_ = lean_ctor_get(v_r_2137_, 3);
lean_dec(v_unused_2160_);
v_unused_2161_ = lean_ctor_get(v_r_2137_, 0);
lean_dec(v_unused_2161_);
v___x_2146_ = v_r_2137_;
v_isShared_2147_ = v_isSharedCheck_2158_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_v_2144_);
lean_inc(v_k_2143_);
lean_dec(v_r_2137_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2158_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
v___x_2148_ = lean_unsigned_to_nat(3u);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 4, v_l_2101_);
lean_ctor_set(v___x_2146_, 3, v_l_2101_);
lean_ctor_set(v___x_2146_, 2, v_v_2139_);
lean_ctor_set(v___x_2146_, 1, v_k_2138_);
lean_ctor_set(v___x_2146_, 0, v___x_2010_);
v___x_2150_ = v___x_2146_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2010_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v_k_2138_);
lean_ctor_set(v_reuseFailAlloc_2157_, 2, v_v_2139_);
lean_ctor_set(v_reuseFailAlloc_2157_, 3, v_l_2101_);
lean_ctor_set(v_reuseFailAlloc_2157_, 4, v_l_2101_);
v___x_2150_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
lean_object* v___x_2152_; 
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 4, v_l_2101_);
lean_ctor_set(v___x_2141_, 2, v_v_1517_);
lean_ctor_set(v___x_2141_, 1, v_k_1516_);
lean_ctor_set(v___x_2141_, 0, v___x_2010_);
v___x_2152_ = v___x_2141_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2010_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_k_1516_);
lean_ctor_set(v_reuseFailAlloc_2156_, 2, v_v_1517_);
lean_ctor_set(v_reuseFailAlloc_2156_, 3, v_l_2101_);
lean_ctor_set(v_reuseFailAlloc_2156_, 4, v_l_2101_);
v___x_2152_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2154_; 
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 4, v___x_2152_);
lean_ctor_set(v___x_1521_, 3, v___x_2150_);
lean_ctor_set(v___x_1521_, 2, v_v_2144_);
lean_ctor_set(v___x_1521_, 1, v_k_2143_);
lean_ctor_set(v___x_1521_, 0, v___x_2148_);
v___x_2154_ = v___x_1521_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2148_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_k_2143_);
lean_ctor_set(v_reuseFailAlloc_2155_, 2, v_v_2144_);
lean_ctor_set(v_reuseFailAlloc_2155_, 3, v___x_2150_);
lean_ctor_set(v_reuseFailAlloc_2155_, 4, v___x_2152_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
}
}
else
{
lean_object* v___x_2166_; lean_object* v___x_2168_; 
v___x_2166_ = lean_unsigned_to_nat(2u);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 4, v_r_2137_);
lean_ctor_set(v___x_1521_, 0, v___x_2166_);
v___x_2168_ = v___x_1521_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2166_);
lean_ctor_set(v_reuseFailAlloc_2169_, 1, v_k_1516_);
lean_ctor_set(v_reuseFailAlloc_2169_, 2, v_v_1517_);
lean_ctor_set(v_reuseFailAlloc_2169_, 3, v_l_1518_);
lean_ctor_set(v_reuseFailAlloc_2169_, 4, v_r_2137_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
else
{
lean_object* v___x_2171_; 
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 4, v_l_1518_);
lean_ctor_set(v___x_1521_, 0, v___x_2010_);
v___x_2171_ = v___x_1521_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2010_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_k_1516_);
lean_ctor_set(v_reuseFailAlloc_2172_, 2, v_v_1517_);
lean_ctor_set(v_reuseFailAlloc_2172_, 3, v_l_1518_);
lean_ctor_set(v_reuseFailAlloc_2172_, 4, v_l_1518_);
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
}
}
}
else
{
return v_t_1515_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg___boxed(lean_object* v_k_2175_, lean_object* v_t_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_2175_, v_t_2176_);
lean_dec_ref(v_k_2175_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___lam__0(lean_object* v_val_2178_, lean_object* v_s_2179_){
_start:
{
lean_object* v_toRingState_2180_; lean_object* v_denoteEntries_2181_; lean_object* v_nextId_2182_; lean_object* v_steps_2183_; lean_object* v_queue_2184_; lean_object* v_basis_2185_; lean_object* v_diseqs_2186_; uint8_t v_recheck_2187_; lean_object* v_invSet_2188_; lean_object* v_powIdentityVarCount_2189_; lean_object* v_numEq0_x3f_2190_; uint8_t v_numEq0Updated_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2199_; 
v_toRingState_2180_ = lean_ctor_get(v_s_2179_, 0);
v_denoteEntries_2181_ = lean_ctor_get(v_s_2179_, 1);
v_nextId_2182_ = lean_ctor_get(v_s_2179_, 2);
v_steps_2183_ = lean_ctor_get(v_s_2179_, 3);
v_queue_2184_ = lean_ctor_get(v_s_2179_, 4);
v_basis_2185_ = lean_ctor_get(v_s_2179_, 5);
v_diseqs_2186_ = lean_ctor_get(v_s_2179_, 6);
v_recheck_2187_ = lean_ctor_get_uint8(v_s_2179_, sizeof(void*)*10);
v_invSet_2188_ = lean_ctor_get(v_s_2179_, 7);
v_powIdentityVarCount_2189_ = lean_ctor_get(v_s_2179_, 8);
v_numEq0_x3f_2190_ = lean_ctor_get(v_s_2179_, 9);
v_numEq0Updated_2191_ = lean_ctor_get_uint8(v_s_2179_, sizeof(void*)*10 + 1);
v_isSharedCheck_2199_ = !lean_is_exclusive(v_s_2179_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2193_ = v_s_2179_;
v_isShared_2194_ = v_isSharedCheck_2199_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_numEq0_x3f_2190_);
lean_inc(v_powIdentityVarCount_2189_);
lean_inc(v_invSet_2188_);
lean_inc(v_diseqs_2186_);
lean_inc(v_basis_2185_);
lean_inc(v_queue_2184_);
lean_inc(v_steps_2183_);
lean_inc(v_nextId_2182_);
lean_inc(v_denoteEntries_2181_);
lean_inc(v_toRingState_2180_);
lean_dec(v_s_2179_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2199_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2195_; lean_object* v___x_2197_; 
v___x_2195_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_val_2178_, v_queue_2184_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 4, v___x_2195_);
v___x_2197_ = v___x_2193_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_toRingState_2180_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_denoteEntries_2181_);
lean_ctor_set(v_reuseFailAlloc_2198_, 2, v_nextId_2182_);
lean_ctor_set(v_reuseFailAlloc_2198_, 3, v_steps_2183_);
lean_ctor_set(v_reuseFailAlloc_2198_, 4, v___x_2195_);
lean_ctor_set(v_reuseFailAlloc_2198_, 5, v_basis_2185_);
lean_ctor_set(v_reuseFailAlloc_2198_, 6, v_diseqs_2186_);
lean_ctor_set(v_reuseFailAlloc_2198_, 7, v_invSet_2188_);
lean_ctor_set(v_reuseFailAlloc_2198_, 8, v_powIdentityVarCount_2189_);
lean_ctor_set(v_reuseFailAlloc_2198_, 9, v_numEq0_x3f_2190_);
lean_ctor_set_uint8(v_reuseFailAlloc_2198_, sizeof(void*)*10, v_recheck_2187_);
lean_ctor_set_uint8(v_reuseFailAlloc_2198_, sizeof(void*)*10 + 1, v_numEq0Updated_2191_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___lam__0___boxed(lean_object* v_val_2200_, lean_object* v_s_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___lam__0(v_val_2200_, v_s_2201_);
lean_dec_ref(v_val_2200_);
return v_res_2202_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg(lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_2203_, v_a_2204_, v_a_2205_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2247_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2210_ = v___x_2207_;
v_isShared_2211_ = v_isSharedCheck_2247_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2207_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2247_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v_queue_2212_; lean_object* v___x_2213_; 
v_queue_2212_ = lean_ctor_get(v_a_2208_, 4);
lean_inc(v_queue_2212_);
lean_dec(v_a_2208_);
v___x_2213_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_queue_2212_);
lean_dec(v_queue_2212_);
if (lean_obj_tag(v___x_2213_) == 1)
{
lean_object* v_val_2214_; lean_object* v___f_2215_; lean_object* v___x_2216_; 
lean_del_object(v___x_2210_);
v_val_2214_ = lean_ctor_get(v___x_2213_, 0);
lean_inc(v_val_2214_);
v___f_2215_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2215_, 0, v_val_2214_);
v___x_2216_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(v___f_2215_, v_a_2203_, v_a_2204_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
lean_dec_ref_known(v___x_2216_, 1);
v___x_2217_ = lean_unsigned_to_nat(1u);
v___x_2218_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v___x_2217_, v_a_2204_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2225_ == 0)
{
lean_object* v_unused_2226_; 
v_unused_2226_ = lean_ctor_get(v___x_2218_, 0);
lean_dec(v_unused_2226_);
v___x_2220_ = v___x_2218_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_dec(v___x_2218_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 0, v___x_2213_);
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2213_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
lean_dec_ref_known(v___x_2213_, 1);
v_a_2227_ = lean_ctor_get(v___x_2218_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2218_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2218_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2227_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
else
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
lean_dec_ref_known(v___x_2213_, 1);
v_a_2235_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v___x_2216_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2216_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
else
{
lean_object* v___x_2243_; lean_object* v___x_2245_; 
lean_dec(v___x_2213_);
v___x_2243_ = lean_box(0);
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 0, v___x_2243_);
v___x_2245_ = v___x_2210_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2243_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
else
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
v_a_2248_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2207_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2207_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_a_2248_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2203_ = stack[0].m_obj;
lean_object* v_a_2204_ = stack[1].m_obj;
lean_object* v_a_2205_ = stack[2].m_obj;
lean_object* v_res_2256_;
v_res_2256_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg(v_a_2203_, v_a_2204_, v_a_2205_);
stack->m_obj
 = v_res_2256_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___boxed(lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg(v_a_2257_, v_a_2258_, v_a_2259_);
lean_dec_ref(v_a_2259_);
lean_dec(v_a_2258_);
lean_dec_ref(v_a_2257_);
return v_res_2261_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v___x_2274_; 
v___x_2274_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg(v_a_2262_, v_a_2263_, v_a_2271_);
return v___x_2274_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2262_ = stack[0].m_obj;
lean_object* v_a_2263_ = stack[1].m_obj;
lean_object* v_a_2264_ = stack[2].m_obj;
lean_object* v_a_2265_ = stack[3].m_obj;
lean_object* v_a_2266_ = stack[4].m_obj;
lean_object* v_a_2267_ = stack[5].m_obj;
lean_object* v_a_2268_ = stack[6].m_obj;
lean_object* v_a_2269_ = stack[7].m_obj;
lean_object* v_a_2270_ = stack[8].m_obj;
lean_object* v_a_2271_ = stack[9].m_obj;
lean_object* v_a_2272_ = stack[10].m_obj;
lean_object* v_res_2275_;
v_res_2275_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
stack->m_obj
 = v_res_2275_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___boxed(lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_);
lean_dec(v_a_2286_);
lean_dec_ref(v_a_2285_);
lean_dec(v_a_2284_);
lean_dec_ref(v_a_2283_);
lean_dec(v_a_2282_);
lean_dec_ref(v_a_2281_);
lean_dec(v_a_2280_);
lean_dec_ref(v_a_2279_);
lean_dec(v_a_2278_);
lean_dec(v_a_2277_);
lean_dec_ref(v_a_2276_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(lean_object* v_00_u03b2_2289_, lean_object* v_k_2290_, lean_object* v_t_2291_, lean_object* v_h_2292_){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_2290_, v_t_2291_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___boxed(lean_object* v_00_u03b2_2294_, lean_object* v_k_2295_, lean_object* v_t_2296_, lean_object* v_h_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(v_00_u03b2_2294_, v_k_2295_, v_t_2296_, v_h_2297_);
lean_dec_ref(v_k_2295_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2299_, lean_object* v_x_2300_, lean_object* v_x_2301_, lean_object* v_x_2302_){
_start:
{
lean_object* v_ks_2303_; lean_object* v_vs_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2330_; 
v_ks_2303_ = lean_ctor_get(v_x_2299_, 0);
v_vs_2304_ = lean_ctor_get(v_x_2299_, 1);
v_isSharedCheck_2330_ = !lean_is_exclusive(v_x_2299_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2306_ = v_x_2299_;
v_isShared_2307_ = v_isSharedCheck_2330_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_vs_2304_);
lean_inc(v_ks_2303_);
lean_dec(v_x_2299_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2330_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2308_; uint8_t v___x_2309_; 
v___x_2308_ = lean_array_get_size(v_ks_2303_);
v___x_2309_ = lean_nat_dec_lt(v_x_2300_, v___x_2308_);
if (v___x_2309_ == 0)
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2313_; 
lean_dec(v_x_2300_);
v___x_2310_ = lean_array_push(v_ks_2303_, v_x_2301_);
v___x_2311_ = lean_array_push(v_vs_2304_, v_x_2302_);
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 1, v___x_2311_);
lean_ctor_set(v___x_2306_, 0, v___x_2310_);
v___x_2313_ = v___x_2306_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2310_);
lean_ctor_set(v_reuseFailAlloc_2314_, 1, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
else
{
lean_object* v_k_x27_2315_; size_t v___x_2316_; size_t v___x_2317_; uint8_t v___x_2318_; 
v_k_x27_2315_ = lean_array_fget_borrowed(v_ks_2303_, v_x_2300_);
v___x_2316_ = lean_ptr_addr(v_x_2301_);
v___x_2317_ = lean_ptr_addr(v_k_x27_2315_);
v___x_2318_ = lean_usize_dec_eq(v___x_2316_, v___x_2317_);
if (v___x_2318_ == 0)
{
lean_object* v___x_2320_; 
if (v_isShared_2307_ == 0)
{
v___x_2320_ = v___x_2306_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_ks_2303_);
lean_ctor_set(v_reuseFailAlloc_2324_, 1, v_vs_2304_);
v___x_2320_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = lean_unsigned_to_nat(1u);
v___x_2322_ = lean_nat_add(v_x_2300_, v___x_2321_);
lean_dec(v_x_2300_);
v_x_2299_ = v___x_2320_;
v_x_2300_ = v___x_2322_;
goto _start;
}
}
else
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2328_; 
v___x_2325_ = lean_array_fset(v_ks_2303_, v_x_2300_, v_x_2301_);
v___x_2326_ = lean_array_fset(v_vs_2304_, v_x_2300_, v_x_2302_);
lean_dec(v_x_2300_);
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 1, v___x_2326_);
lean_ctor_set(v___x_2306_, 0, v___x_2325_);
v___x_2328_ = v___x_2306_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2325_);
lean_ctor_set(v_reuseFailAlloc_2329_, 1, v___x_2326_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2331_, lean_object* v_k_2332_, lean_object* v_v_2333_){
_start:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2334_ = lean_unsigned_to_nat(0u);
v___x_2335_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2331_, v___x_2334_, v_k_2332_, v_v_2333_);
return v___x_2335_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2336_; 
v___x_2336_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2336_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(lean_object* v_x_2337_, size_t v_x_2338_, size_t v_x_2339_, lean_object* v_x_2340_, lean_object* v_x_2341_){
_start:
{
if (lean_obj_tag(v_x_2337_) == 0)
{
lean_object* v_es_2342_; size_t v___x_2343_; size_t v___x_2344_; lean_object* v_j_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; 
v_es_2342_ = lean_ctor_get(v_x_2337_, 0);
v___x_2343_ = ((size_t)31ULL);
v___x_2344_ = lean_usize_land(v_x_2338_, v___x_2343_);
v_j_2345_ = lean_usize_to_nat(v___x_2344_);
v___x_2346_ = lean_array_get_size(v_es_2342_);
v___x_2347_ = lean_nat_dec_lt(v_j_2345_, v___x_2346_);
if (v___x_2347_ == 0)
{
lean_dec(v_j_2345_);
lean_dec(v_x_2341_);
lean_dec_ref(v_x_2340_);
return v_x_2337_;
}
else
{
lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2388_; 
lean_inc_ref(v_es_2342_);
v_isSharedCheck_2388_ = !lean_is_exclusive(v_x_2337_);
if (v_isSharedCheck_2388_ == 0)
{
lean_object* v_unused_2389_; 
v_unused_2389_ = lean_ctor_get(v_x_2337_, 0);
lean_dec(v_unused_2389_);
v___x_2349_ = v_x_2337_;
v_isShared_2350_ = v_isSharedCheck_2388_;
goto v_resetjp_2348_;
}
else
{
lean_dec(v_x_2337_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2388_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v_v_2351_; lean_object* v___x_2352_; lean_object* v_xs_x27_2353_; lean_object* v___y_2355_; 
v_v_2351_ = lean_array_fget(v_es_2342_, v_j_2345_);
v___x_2352_ = lean_box(0);
v_xs_x27_2353_ = lean_array_fset(v_es_2342_, v_j_2345_, v___x_2352_);
switch(lean_obj_tag(v_v_2351_))
{
case 0:
{
lean_object* v_key_2360_; lean_object* v_val_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2373_; 
v_key_2360_ = lean_ctor_get(v_v_2351_, 0);
v_val_2361_ = lean_ctor_get(v_v_2351_, 1);
v_isSharedCheck_2373_ = !lean_is_exclusive(v_v_2351_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2363_ = v_v_2351_;
v_isShared_2364_ = v_isSharedCheck_2373_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_val_2361_);
lean_inc(v_key_2360_);
lean_dec(v_v_2351_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2373_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
size_t v___x_2365_; size_t v___x_2366_; uint8_t v___x_2367_; 
v___x_2365_ = lean_ptr_addr(v_x_2340_);
v___x_2366_ = lean_ptr_addr(v_key_2360_);
v___x_2367_ = lean_usize_dec_eq(v___x_2365_, v___x_2366_);
if (v___x_2367_ == 0)
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
lean_del_object(v___x_2363_);
v___x_2368_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2360_, v_val_2361_, v_x_2340_, v_x_2341_);
v___x_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2368_);
v___y_2355_ = v___x_2369_;
goto v___jp_2354_;
}
else
{
lean_object* v___x_2371_; 
lean_dec(v_val_2361_);
lean_dec(v_key_2360_);
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 1, v_x_2341_);
lean_ctor_set(v___x_2363_, 0, v_x_2340_);
v___x_2371_ = v___x_2363_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_x_2340_);
lean_ctor_set(v_reuseFailAlloc_2372_, 1, v_x_2341_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
v___y_2355_ = v___x_2371_;
goto v___jp_2354_;
}
}
}
}
case 1:
{
lean_object* v_node_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2386_; 
v_node_2374_ = lean_ctor_get(v_v_2351_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v_v_2351_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2376_ = v_v_2351_;
v_isShared_2377_ = v_isSharedCheck_2386_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_node_2374_);
lean_dec(v_v_2351_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2386_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
size_t v___x_2378_; size_t v___x_2379_; size_t v___x_2380_; size_t v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2384_; 
v___x_2378_ = ((size_t)5ULL);
v___x_2379_ = lean_usize_shift_right(v_x_2338_, v___x_2378_);
v___x_2380_ = ((size_t)1ULL);
v___x_2381_ = lean_usize_add(v_x_2339_, v___x_2380_);
v___x_2382_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_node_2374_, v___x_2379_, v___x_2381_, v_x_2340_, v_x_2341_);
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 0, v___x_2382_);
v___x_2384_ = v___x_2376_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2382_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
v___y_2355_ = v___x_2384_;
goto v___jp_2354_;
}
}
}
default: 
{
lean_object* v___x_2387_; 
v___x_2387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2387_, 0, v_x_2340_);
lean_ctor_set(v___x_2387_, 1, v_x_2341_);
v___y_2355_ = v___x_2387_;
goto v___jp_2354_;
}
}
v___jp_2354_:
{
lean_object* v___x_2356_; lean_object* v___x_2358_; 
v___x_2356_ = lean_array_fset(v_xs_x27_2353_, v_j_2345_, v___y_2355_);
lean_dec(v_j_2345_);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 0, v___x_2356_);
v___x_2358_ = v___x_2349_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2356_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
}
else
{
lean_object* v_ks_2390_; lean_object* v_vs_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2409_; 
v_ks_2390_ = lean_ctor_get(v_x_2337_, 0);
v_vs_2391_ = lean_ctor_get(v_x_2337_, 1);
v_isSharedCheck_2409_ = !lean_is_exclusive(v_x_2337_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2393_ = v_x_2337_;
v_isShared_2394_ = v_isSharedCheck_2409_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_vs_2391_);
lean_inc(v_ks_2390_);
lean_dec(v_x_2337_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2409_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_ks_2390_);
lean_ctor_set(v_reuseFailAlloc_2408_, 1, v_vs_2391_);
v___x_2396_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
lean_object* v_newNode_2397_; size_t v___x_2398_; uint8_t v___x_2399_; 
v_newNode_2397_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v___x_2396_, v_x_2340_, v_x_2341_);
v___x_2398_ = ((size_t)7ULL);
v___x_2399_ = lean_usize_dec_le(v___x_2398_, v_x_2339_);
if (v___x_2399_ == 0)
{
lean_object* v___x_2400_; lean_object* v___x_2401_; uint8_t v___x_2402_; 
v___x_2400_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2397_);
v___x_2401_ = lean_unsigned_to_nat(4u);
v___x_2402_ = lean_nat_dec_lt(v___x_2400_, v___x_2401_);
lean_dec(v___x_2400_);
if (v___x_2402_ == 0)
{
lean_object* v_ks_2403_; lean_object* v_vs_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v_ks_2403_ = lean_ctor_get(v_newNode_2397_, 0);
lean_inc_ref(v_ks_2403_);
v_vs_2404_ = lean_ctor_get(v_newNode_2397_, 1);
lean_inc_ref(v_vs_2404_);
lean_dec_ref(v_newNode_2397_);
v___x_2405_ = lean_unsigned_to_nat(0u);
v___x_2406_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0);
v___x_2407_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_x_2339_, v_ks_2403_, v_vs_2404_, v___x_2405_, v___x_2406_);
lean_dec_ref(v_vs_2404_);
lean_dec_ref(v_ks_2403_);
return v___x_2407_;
}
else
{
return v_newNode_2397_;
}
}
else
{
return v_newNode_2397_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2337_ = stack[0].m_obj;
size_t v_x_2338_ = stack[1].m_num;
size_t v_x_2339_ = stack[2].m_num;
lean_object* v_x_2340_ = stack[3].m_obj;
lean_object* v_x_2341_ = stack[4].m_obj;
lean_object* v_res_2410_;
v_res_2410_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2337_, v_x_2338_, v_x_2339_, v_x_2340_, v_x_2341_);
stack->m_obj
 = v_res_2410_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(size_t v_depth_2411_, lean_object* v_keys_2412_, lean_object* v_vals_2413_, lean_object* v_i_2414_, lean_object* v_entries_2415_){
_start:
{
lean_object* v___x_2416_; uint8_t v___x_2417_; 
v___x_2416_ = lean_array_get_size(v_keys_2412_);
v___x_2417_ = lean_nat_dec_lt(v_i_2414_, v___x_2416_);
if (v___x_2417_ == 0)
{
lean_dec(v_i_2414_);
return v_entries_2415_;
}
else
{
lean_object* v_k_2418_; lean_object* v_v_2419_; size_t v___x_2420_; size_t v___x_2421_; size_t v___x_2422_; uint64_t v___x_2423_; size_t v_h_2424_; size_t v___x_2425_; lean_object* v___x_2426_; size_t v___x_2427_; size_t v___x_2428_; size_t v___x_2429_; size_t v_h_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v_k_2418_ = lean_array_fget_borrowed(v_keys_2412_, v_i_2414_);
v_v_2419_ = lean_array_fget_borrowed(v_vals_2413_, v_i_2414_);
v___x_2420_ = lean_ptr_addr(v_k_2418_);
v___x_2421_ = ((size_t)3ULL);
v___x_2422_ = lean_usize_shift_right(v___x_2420_, v___x_2421_);
v___x_2423_ = lean_usize_to_uint64(v___x_2422_);
v_h_2424_ = lean_uint64_to_usize(v___x_2423_);
v___x_2425_ = ((size_t)5ULL);
v___x_2426_ = lean_unsigned_to_nat(1u);
v___x_2427_ = ((size_t)1ULL);
v___x_2428_ = lean_usize_sub(v_depth_2411_, v___x_2427_);
v___x_2429_ = lean_usize_mul(v___x_2425_, v___x_2428_);
v_h_2430_ = lean_usize_shift_right(v_h_2424_, v___x_2429_);
v___x_2431_ = lean_nat_add(v_i_2414_, v___x_2426_);
lean_dec(v_i_2414_);
lean_inc(v_v_2419_);
lean_inc(v_k_2418_);
v___x_2432_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_entries_2415_, v_h_2430_, v_depth_2411_, v_k_2418_, v_v_2419_);
v_i_2414_ = v___x_2431_;
v_entries_2415_ = v___x_2432_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2411_ = stack[0].m_num;
lean_object* v_keys_2412_ = stack[1].m_obj;
lean_object* v_vals_2413_ = stack[2].m_obj;
lean_object* v_i_2414_ = stack[3].m_obj;
lean_object* v_entries_2415_ = stack[4].m_obj;
lean_object* v_res_2434_;
v_res_2434_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_2411_, v_keys_2412_, v_vals_2413_, v_i_2414_, v_entries_2415_);
stack->m_obj
 = v_res_2434_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2435_, lean_object* v_keys_2436_, lean_object* v_vals_2437_, lean_object* v_i_2438_, lean_object* v_entries_2439_){
_start:
{
size_t v_depth_boxed_2440_; lean_object* v_res_2441_; 
v_depth_boxed_2440_ = lean_unbox_usize(v_depth_2435_);
lean_dec(v_depth_2435_);
v_res_2441_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2440_, v_keys_2436_, v_vals_2437_, v_i_2438_, v_entries_2439_);
lean_dec_ref(v_vals_2437_);
lean_dec_ref(v_keys_2436_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___boxed(lean_object* v_x_2442_, lean_object* v_x_2443_, lean_object* v_x_2444_, lean_object* v_x_2445_, lean_object* v_x_2446_){
_start:
{
size_t v_x_6498__boxed_2447_; size_t v_x_6499__boxed_2448_; lean_object* v_res_2449_; 
v_x_6498__boxed_2447_ = lean_unbox_usize(v_x_2443_);
lean_dec(v_x_2443_);
v_x_6499__boxed_2448_ = lean_unbox_usize(v_x_2444_);
lean_dec(v_x_2444_);
v_res_2449_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2442_, v_x_6498__boxed_2447_, v_x_6499__boxed_2448_, v_x_2445_, v_x_2446_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(lean_object* v_x_2450_, lean_object* v_x_2451_, lean_object* v_x_2452_){
_start:
{
size_t v___x_2453_; size_t v___x_2454_; size_t v___x_2455_; uint64_t v___x_2456_; size_t v___x_2457_; size_t v___x_2458_; lean_object* v___x_2459_; 
v___x_2453_ = lean_ptr_addr(v_x_2451_);
v___x_2454_ = ((size_t)3ULL);
v___x_2455_ = lean_usize_shift_right(v___x_2453_, v___x_2454_);
v___x_2456_ = lean_usize_to_uint64(v___x_2455_);
v___x_2457_ = lean_uint64_to_usize(v___x_2456_);
v___x_2458_ = ((size_t)1ULL);
v___x_2459_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2450_, v___x_2457_, v___x_2458_, v_x_2451_, v_x_2452_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0(lean_object* v_e_2460_, lean_object* v_ringId_2461_, lean_object* v_s_2462_){
_start:
{
lean_object* v_rings_2463_; lean_object* v_exprToRingId_2464_; lean_object* v_semirings_2465_; lean_object* v_exprToSemiringId_2466_; lean_object* v_ncRings_2467_; lean_object* v_exprToNCRingId_2468_; lean_object* v_ncSemirings_2469_; lean_object* v_exprToNCSemiringId_2470_; lean_object* v_steps_2471_; uint8_t v_reportedMaxDegreeIssue_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2480_; 
v_rings_2463_ = lean_ctor_get(v_s_2462_, 0);
v_exprToRingId_2464_ = lean_ctor_get(v_s_2462_, 1);
v_semirings_2465_ = lean_ctor_get(v_s_2462_, 2);
v_exprToSemiringId_2466_ = lean_ctor_get(v_s_2462_, 3);
v_ncRings_2467_ = lean_ctor_get(v_s_2462_, 4);
v_exprToNCRingId_2468_ = lean_ctor_get(v_s_2462_, 5);
v_ncSemirings_2469_ = lean_ctor_get(v_s_2462_, 6);
v_exprToNCSemiringId_2470_ = lean_ctor_get(v_s_2462_, 7);
v_steps_2471_ = lean_ctor_get(v_s_2462_, 8);
v_reportedMaxDegreeIssue_2472_ = lean_ctor_get_uint8(v_s_2462_, sizeof(void*)*9);
v_isSharedCheck_2480_ = !lean_is_exclusive(v_s_2462_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2474_ = v_s_2462_;
v_isShared_2475_ = v_isSharedCheck_2480_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_steps_2471_);
lean_inc(v_exprToNCSemiringId_2470_);
lean_inc(v_ncSemirings_2469_);
lean_inc(v_exprToNCRingId_2468_);
lean_inc(v_ncRings_2467_);
lean_inc(v_exprToSemiringId_2466_);
lean_inc(v_semirings_2465_);
lean_inc(v_exprToRingId_2464_);
lean_inc(v_rings_2463_);
lean_dec(v_s_2462_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2480_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2476_; lean_object* v___x_2478_; 
v___x_2476_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_exprToRingId_2464_, v_e_2460_, v_ringId_2461_);
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 1, v___x_2476_);
v___x_2478_ = v___x_2474_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_rings_2463_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v___x_2476_);
lean_ctor_set(v_reuseFailAlloc_2479_, 2, v_semirings_2465_);
lean_ctor_set(v_reuseFailAlloc_2479_, 3, v_exprToSemiringId_2466_);
lean_ctor_set(v_reuseFailAlloc_2479_, 4, v_ncRings_2467_);
lean_ctor_set(v_reuseFailAlloc_2479_, 5, v_exprToNCRingId_2468_);
lean_ctor_set(v_reuseFailAlloc_2479_, 6, v_ncSemirings_2469_);
lean_ctor_set(v_reuseFailAlloc_2479_, 7, v_exprToNCSemiringId_2470_);
lean_ctor_set(v_reuseFailAlloc_2479_, 8, v_steps_2471_);
lean_ctor_set_uint8(v_reuseFailAlloc_2479_, sizeof(void*)*9, v_reportedMaxDegreeIssue_2472_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1(void){
_start:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2482_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__0));
v___x_2483_ = l_Lean_stringToMessageData(v___x_2482_);
return v___x_2483_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(lean_object* v_e_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_){
_start:
{
lean_object* v_ringId_2497_; lean_object* v___f_2498_; lean_object* v___x_2499_; 
v_ringId_2497_ = lean_ctor_get(v_a_2485_, 0);
lean_inc(v_ringId_2497_);
lean_inc_ref(v_e_2484_);
v___f_2498_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2498_, 0, v_e_2484_);
lean_closure_set(v___f_2498_, 1, v_ringId_2497_);
v___x_2499_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_2484_, v_a_2486_, v_a_2491_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_a_2500_);
lean_dec_ref_known(v___x_2499_, 1);
if (lean_obj_tag(v_a_2500_) == 1)
{
lean_object* v_val_2501_; uint8_t v___x_2502_; 
lean_dec_ref(v___f_2498_);
v_val_2501_ = lean_ctor_get(v_a_2500_, 0);
lean_inc(v_val_2501_);
lean_dec_ref_known(v_a_2500_, 1);
v___x_2502_ = lean_nat_dec_eq(v_val_2501_, v_ringId_2497_);
lean_dec(v_val_2501_);
if (v___x_2502_ == 0)
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2503_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1);
v___x_2504_ = l_Lean_indentExpr(v_e_2484_);
v___x_2505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2503_);
lean_ctor_set(v___x_2505_, 1, v___x_2504_);
v___x_2506_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2487_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v_a_2507_; uint8_t v_verbose_2508_; 
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
lean_inc(v_a_2507_);
lean_dec_ref_known(v___x_2506_, 1);
v_verbose_2508_ = lean_ctor_get_uint8(v_a_2507_, 0);
lean_dec(v_a_2507_);
if (v_verbose_2508_ == 0)
{
lean_dec_ref_known(v___x_2505_, 2);
goto v___jp_2494_;
}
else
{
lean_object* v___x_2509_; 
v___x_2509_ = l_Lean_Meta_Sym_reportIssue(v___x_2505_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_dec_ref_known(v___x_2509_, 1);
goto v___jp_2494_;
}
else
{
return v___x_2509_;
}
}
}
else
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2517_; 
lean_dec_ref_known(v___x_2505_, 2);
v_a_2510_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2512_ = v___x_2506_;
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2506_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2515_; 
if (v_isShared_2513_ == 0)
{
v___x_2515_ = v___x_2512_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_a_2510_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
}
else
{
lean_dec_ref(v_e_2484_);
goto v___jp_2494_;
}
}
else
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
lean_dec(v_a_2500_);
lean_dec_ref(v_e_2484_);
v___x_2518_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2519_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2518_, v___f_2498_, v_a_2486_);
return v___x_2519_;
}
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
lean_dec_ref(v___f_2498_);
lean_dec_ref(v_e_2484_);
v_a_2520_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2499_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2499_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2520_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
v___jp_2494_:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2495_ = lean_box(0);
v___x_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2495_);
return v___x_2496_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2484_ = stack[0].m_obj;
lean_object* v_a_2485_ = stack[1].m_obj;
lean_object* v_a_2486_ = stack[2].m_obj;
lean_object* v_a_2487_ = stack[3].m_obj;
lean_object* v_a_2488_ = stack[4].m_obj;
lean_object* v_a_2489_ = stack[5].m_obj;
lean_object* v_a_2490_ = stack[6].m_obj;
lean_object* v_a_2491_ = stack[7].m_obj;
lean_object* v_a_2492_ = stack[8].m_obj;
lean_object* v_res_2528_;
v_res_2528_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_);
stack->m_obj
 = v_res_2528_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___boxed(lean_object* v_e_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_);
lean_dec(v_a_2537_);
lean_dec_ref(v_a_2536_);
lean_dec(v_a_2535_);
lean_dec_ref(v_a_2534_);
lean_dec(v_a_2533_);
lean_dec_ref(v_a_2532_);
lean_dec(v_a_2531_);
lean_dec_ref(v_a_2530_);
return v_res_2539_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(lean_object* v_e_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_){
_start:
{
lean_object* v___x_2553_; 
v___x_2553_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2540_, v_a_2541_, v_a_2542_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_);
return v___x_2553_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_setTermRingId_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2540_ = stack[0].m_obj;
lean_object* v_a_2541_ = stack[1].m_obj;
lean_object* v_a_2542_ = stack[2].m_obj;
lean_object* v_a_2543_ = stack[3].m_obj;
lean_object* v_a_2544_ = stack[4].m_obj;
lean_object* v_a_2545_ = stack[5].m_obj;
lean_object* v_a_2546_ = stack[6].m_obj;
lean_object* v_a_2547_ = stack[7].m_obj;
lean_object* v_a_2548_ = stack[8].m_obj;
lean_object* v_a_2549_ = stack[9].m_obj;
lean_object* v_a_2550_ = stack[10].m_obj;
lean_object* v_a_2551_ = stack[11].m_obj;
lean_object* v_res_2554_;
v_res_2554_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(v_e_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_);
stack->m_obj
 = v_res_2554_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___boxed(lean_object* v_e_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(v_e_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_);
lean_dec(v_a_2566_);
lean_dec_ref(v_a_2565_);
lean_dec(v_a_2564_);
lean_dec_ref(v_a_2563_);
lean_dec(v_a_2562_);
lean_dec_ref(v_a_2561_);
lean_dec(v_a_2560_);
lean_dec_ref(v_a_2559_);
lean_dec(v_a_2558_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0(lean_object* v_00_u03b2_2569_, lean_object* v_x_2570_, lean_object* v_x_2571_, lean_object* v_x_2572_){
_start:
{
lean_object* v___x_2573_; 
v___x_2573_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_x_2570_, v_x_2571_, v_x_2572_);
return v___x_2573_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(lean_object* v_00_u03b2_2574_, lean_object* v_x_2575_, size_t v_x_2576_, size_t v_x_2577_, lean_object* v_x_2578_, lean_object* v_x_2579_){
_start:
{
lean_object* v___x_2580_; 
v___x_2580_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2575_, v_x_2576_, v_x_2577_, v_x_2578_, v_x_2579_);
return v___x_2580_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2575_ = stack[1].m_obj;
size_t v_x_2576_ = stack[2].m_num;
size_t v_x_2577_ = stack[3].m_num;
lean_object* v_x_2578_ = stack[4].m_obj;
lean_object* v_x_2579_ = stack[5].m_obj;
lean_object* v_res_2581_;
v_res_2581_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(lean_box(0), v_x_2575_, v_x_2576_, v_x_2577_, v_x_2578_, v_x_2579_);
stack->m_obj
 = v_res_2581_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2582_, lean_object* v_x_2583_, lean_object* v_x_2584_, lean_object* v_x_2585_, lean_object* v_x_2586_, lean_object* v_x_2587_){
_start:
{
size_t v_x_6935__boxed_2588_; size_t v_x_6936__boxed_2589_; lean_object* v_res_2590_; 
v_x_6935__boxed_2588_ = lean_unbox_usize(v_x_2584_);
lean_dec(v_x_2584_);
v_x_6936__boxed_2589_ = lean_unbox_usize(v_x_2585_);
lean_dec(v_x_2585_);
v_res_2590_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(v_00_u03b2_2582_, v_x_2583_, v_x_6935__boxed_2588_, v_x_6936__boxed_2589_, v_x_2586_, v_x_2587_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2591_, lean_object* v_n_2592_, lean_object* v_k_2593_, lean_object* v_v_2594_){
_start:
{
lean_object* v___x_2595_; 
v___x_2595_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v_n_2592_, v_k_2593_, v_v_2594_);
return v___x_2595_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2596_, size_t v_depth_2597_, lean_object* v_keys_2598_, lean_object* v_vals_2599_, lean_object* v_heq_2600_, lean_object* v_i_2601_, lean_object* v_entries_2602_){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_2597_, v_keys_2598_, v_vals_2599_, v_i_2601_, v_entries_2602_);
return v___x_2603_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2597_ = stack[1].m_num;
lean_object* v_keys_2598_ = stack[2].m_obj;
lean_object* v_vals_2599_ = stack[3].m_obj;
lean_object* v_i_2601_ = stack[5].m_obj;
lean_object* v_entries_2602_ = stack[6].m_obj;
lean_object* v_res_2604_;
v_res_2604_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(lean_box(0), v_depth_2597_, v_keys_2598_, v_vals_2599_, lean_box(0), v_i_2601_, v_entries_2602_);
stack->m_obj
 = v_res_2604_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2605_, lean_object* v_depth_2606_, lean_object* v_keys_2607_, lean_object* v_vals_2608_, lean_object* v_heq_2609_, lean_object* v_i_2610_, lean_object* v_entries_2611_){
_start:
{
size_t v_depth_boxed_2612_; lean_object* v_res_2613_; 
v_depth_boxed_2612_ = lean_unbox_usize(v_depth_2606_);
lean_dec(v_depth_2606_);
v_res_2613_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(v_00_u03b2_2605_, v_depth_boxed_2612_, v_keys_2607_, v_vals_2608_, v_heq_2609_, v_i_2610_, v_entries_2611_);
lean_dec_ref(v_vals_2608_);
lean_dec_ref(v_keys_2607_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2614_, lean_object* v_x_2615_, lean_object* v_x_2616_, lean_object* v_x_2617_, lean_object* v_x_2618_){
_start:
{
lean_object* v___x_2619_; 
v___x_2619_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2615_, v_x_2616_, v_x_2617_, v_x_2618_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0(lean_object* v_e_2620_, lean_object* v___f_2621_, lean_object* v___f_2622_, lean_object* v_size_2623_, lean_object* v_s_2624_){
_start:
{
lean_object* v_vars_2625_; lean_object* v_varMap_2626_; lean_object* v_denote_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2636_; 
v_vars_2625_ = lean_ctor_get(v_s_2624_, 0);
v_varMap_2626_ = lean_ctor_get(v_s_2624_, 1);
v_denote_2627_ = lean_ctor_get(v_s_2624_, 2);
v_isSharedCheck_2636_ = !lean_is_exclusive(v_s_2624_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2629_ = v_s_2624_;
v_isShared_2630_ = v_isSharedCheck_2636_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_denote_2627_);
lean_inc(v_varMap_2626_);
lean_inc(v_vars_2625_);
lean_dec(v_s_2624_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2636_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2634_; 
lean_inc_ref(v_e_2620_);
v___x_2631_ = l_Lean_PersistentArray_push___redArg(v_vars_2625_, v_e_2620_);
v___x_2632_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2621_, v___f_2622_, v_varMap_2626_, v_e_2620_, v_size_2623_);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 1, v___x_2632_);
lean_ctor_set(v___x_2629_, 0, v___x_2631_);
v___x_2634_ = v___x_2629_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2631_);
lean_ctor_set(v_reuseFailAlloc_2635_, 1, v___x_2632_);
lean_ctor_set(v_reuseFailAlloc_2635_, 2, v_denote_2627_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1(lean_object* v_toPure_2637_, lean_object* v_size_2638_, lean_object* v_____r_2639_){
_start:
{
lean_object* v___x_2640_; 
v___x_2640_ = lean_apply_2(v_toPure_2637_, lean_box(0), v_size_2638_);
return v___x_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2(lean_object* v_e_2641_, lean_object* v_inst_2642_, lean_object* v_toBind_2643_, lean_object* v___f_2644_, lean_object* v_____r_2645_){
_start:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2646_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2647_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SolverExtension_markTerm___boxed), 14, 3);
lean_closure_set(v___x_2647_, 0, lean_box(0));
lean_closure_set(v___x_2647_, 1, v___x_2646_);
lean_closure_set(v___x_2647_, 2, v_e_2641_);
v___x_2648_ = lean_apply_2(v_inst_2642_, lean_box(0), v___x_2647_);
v___x_2649_ = lean_apply_4(v_toBind_2643_, lean_box(0), lean_box(0), v___x_2648_, v___f_2644_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3(lean_object* v_inst_2650_, lean_object* v_e_2651_, lean_object* v_toBind_2652_, lean_object* v___f_2653_, lean_object* v_____r_2654_){
_start:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2655_ = lean_apply_1(v_inst_2650_, v_e_2651_);
v___x_2656_ = lean_apply_4(v_toBind_2652_, lean_box(0), lean_box(0), v___x_2655_, v___f_2653_);
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4(lean_object* v___f_2657_, lean_object* v___f_2658_, lean_object* v_e_2659_, lean_object* v_toPure_2660_, lean_object* v_inst_2661_, lean_object* v_toBind_2662_, lean_object* v_inst_2663_, lean_object* v_modifyRingState_2664_, lean_object* v_s_2665_){
_start:
{
lean_object* v_vars_2666_; lean_object* v_varMap_2667_; lean_object* v___x_2668_; 
v_vars_2666_ = lean_ctor_get(v_s_2665_, 0);
lean_inc_ref(v_vars_2666_);
v_varMap_2667_ = lean_ctor_get(v_s_2665_, 1);
lean_inc_ref(v_varMap_2667_);
lean_dec_ref(v_s_2665_);
lean_inc_ref(v_e_2659_);
lean_inc_ref(v___f_2658_);
lean_inc_ref(v___f_2657_);
v___x_2668_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2657_, v___f_2658_, v_varMap_2667_, v_e_2659_);
lean_dec_ref(v_varMap_2667_);
if (lean_obj_tag(v___x_2668_) == 1)
{
lean_object* v_val_2669_; lean_object* v___x_2670_; 
lean_dec_ref(v_vars_2666_);
lean_dec(v_modifyRingState_2664_);
lean_dec(v_inst_2663_);
lean_dec(v_toBind_2662_);
lean_dec(v_inst_2661_);
lean_dec_ref(v_e_2659_);
lean_dec_ref(v___f_2658_);
lean_dec_ref(v___f_2657_);
v_val_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_val_2669_);
lean_dec_ref_known(v___x_2668_, 1);
v___x_2670_ = lean_apply_2(v_toPure_2660_, lean_box(0), v_val_2669_);
return v___x_2670_;
}
else
{
lean_object* v_size_2671_; lean_object* v___f_2672_; lean_object* v___f_2673_; lean_object* v___f_2674_; lean_object* v___f_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
lean_dec(v___x_2668_);
v_size_2671_ = lean_ctor_get(v_vars_2666_, 2);
lean_inc_n(v_size_2671_, 2);
lean_dec_ref(v_vars_2666_);
lean_inc_ref_n(v_e_2659_, 2);
v___f_2672_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2672_, 0, v_e_2659_);
lean_closure_set(v___f_2672_, 1, v___f_2657_);
lean_closure_set(v___f_2672_, 2, v___f_2658_);
lean_closure_set(v___f_2672_, 3, v_size_2671_);
v___f_2673_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2673_, 0, v_toPure_2660_);
lean_closure_set(v___f_2673_, 1, v_size_2671_);
lean_inc_n(v_toBind_2662_, 2);
v___f_2674_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2674_, 0, v_e_2659_);
lean_closure_set(v___f_2674_, 1, v_inst_2661_);
lean_closure_set(v___f_2674_, 2, v_toBind_2662_);
lean_closure_set(v___f_2674_, 3, v___f_2673_);
v___f_2675_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2675_, 0, v_inst_2663_);
lean_closure_set(v___f_2675_, 1, v_e_2659_);
lean_closure_set(v___f_2675_, 2, v_toBind_2662_);
lean_closure_set(v___f_2675_, 3, v___f_2674_);
v___x_2676_ = lean_apply_1(v_modifyRingState_2664_, v___f_2672_);
v___x_2677_ = lean_apply_4(v_toBind_2662_, lean_box(0), lean_box(0), v___x_2676_, v___f_2675_);
return v___x_2677_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(lean_object* v_inst_2680_, lean_object* v_inst_2681_, lean_object* v_inst_2682_, lean_object* v_inst_2683_, lean_object* v_e_2684_){
_start:
{
lean_object* v_toApplicative_2685_; lean_object* v_toBind_2686_; lean_object* v_getRingState_2687_; lean_object* v_modifyRingState_2688_; lean_object* v_toPure_2689_; lean_object* v___f_2690_; lean_object* v___f_2691_; lean_object* v___f_2692_; lean_object* v___x_2693_; 
v_toApplicative_2685_ = lean_ctor_get(v_inst_2681_, 0);
lean_inc_ref(v_toApplicative_2685_);
v_toBind_2686_ = lean_ctor_get(v_inst_2681_, 1);
lean_inc_n(v_toBind_2686_, 2);
lean_dec_ref(v_inst_2681_);
v_getRingState_2687_ = lean_ctor_get(v_inst_2682_, 0);
lean_inc(v_getRingState_2687_);
v_modifyRingState_2688_ = lean_ctor_get(v_inst_2682_, 1);
lean_inc(v_modifyRingState_2688_);
lean_dec_ref(v_inst_2682_);
v_toPure_2689_ = lean_ctor_get(v_toApplicative_2685_, 1);
lean_inc(v_toPure_2689_);
lean_dec_ref(v_toApplicative_2685_);
v___f_2690_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0));
v___f_2691_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1));
v___f_2692_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2692_, 0, v___f_2690_);
lean_closure_set(v___f_2692_, 1, v___f_2691_);
lean_closure_set(v___f_2692_, 2, v_e_2684_);
lean_closure_set(v___f_2692_, 3, v_toPure_2689_);
lean_closure_set(v___f_2692_, 4, v_inst_2680_);
lean_closure_set(v___f_2692_, 5, v_toBind_2686_);
lean_closure_set(v___f_2692_, 6, v_inst_2683_);
lean_closure_set(v___f_2692_, 7, v_modifyRingState_2688_);
v___x_2693_ = lean_apply_4(v_toBind_2686_, lean_box(0), lean_box(0), v_getRingState_2687_, v___f_2692_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore(lean_object* v_m_2694_, lean_object* v_inst_2695_, lean_object* v_inst_2696_, lean_object* v_inst_2697_, lean_object* v_inst_2698_, lean_object* v_e_2699_){
_start:
{
lean_object* v___x_2700_; 
v___x_2700_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v_inst_2695_, v_inst_2696_, v_inst_2697_, v_inst_2698_, v_e_2699_);
return v___x_2700_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0(lean_object* v_e_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2701_, v___y_2702_, v___y_2703_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
return v___x_2714_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2701_ = stack[0].m_obj;
lean_object* v___y_2702_ = stack[1].m_obj;
lean_object* v___y_2703_ = stack[2].m_obj;
lean_object* v___y_2704_ = stack[3].m_obj;
lean_object* v___y_2705_ = stack[4].m_obj;
lean_object* v___y_2706_ = stack[5].m_obj;
lean_object* v___y_2707_ = stack[6].m_obj;
lean_object* v___y_2708_ = stack[7].m_obj;
lean_object* v___y_2709_ = stack[8].m_obj;
lean_object* v___y_2710_ = stack[9].m_obj;
lean_object* v___y_2711_ = stack[10].m_obj;
lean_object* v___y_2712_ = stack[11].m_obj;
lean_object* v_res_2715_;
v_res_2715_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0(v_e_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
stack->m_obj
 = v_res_2715_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0___boxed(lean_object* v_e_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0(v_e_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
return v_res_2729_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2733_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___closed__0));
v___x_2734_ = l_Lean_stringToMessageData(v___x_2733_);
return v___x_2734_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0(lean_object* v___x_2735_, lean_object* v___x_2736_, lean_object* v___f_2737_, lean_object* v___x_2738_, lean_object* v___f_2739_, lean_object* v_e_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v___x_2753_; 
v___x_2753_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_2740_, v___y_2742_);
if (lean_obj_tag(v___x_2753_) == 0)
{
lean_object* v_a_2754_; uint8_t v___x_2755_; 
v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
lean_inc(v_a_2754_);
lean_dec_ref_known(v___x_2753_, 1);
v___x_2755_ = lean_unbox(v_a_2754_);
lean_dec(v_a_2754_);
if (v___x_2755_ == 0)
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_1454__overap_2759_; lean_object* v___x_2760_; 
v___x_2756_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___closed__1);
lean_inc_ref(v_e_2740_);
v___x_2757_ = l_Lean_indentExpr(v_e_2740_);
v___x_2758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2756_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
lean_inc_ref(v___x_2735_);
v___x_1454__overap_2759_ = l_Lean_throwError___redArg(v___x_2735_, v___x_2736_, v___x_2758_);
lean_inc(v___y_2751_);
lean_inc_ref(v___y_2750_);
lean_inc(v___y_2749_);
lean_inc_ref(v___y_2748_);
lean_inc(v___y_2747_);
lean_inc_ref(v___y_2746_);
lean_inc(v___y_2745_);
lean_inc_ref(v___y_2744_);
lean_inc(v___y_2743_);
lean_inc(v___y_2742_);
lean_inc_ref(v___y_2741_);
v___x_2760_ = lean_apply_12(v___x_1454__overap_2759_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, lean_box(0));
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v___x_1457__overap_2761_; lean_object* v___x_2762_; 
lean_dec_ref_known(v___x_2760_, 1);
v___x_1457__overap_2761_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v___f_2737_, v___x_2735_, v___x_2738_, v___f_2739_, v_e_2740_);
lean_inc(v___y_2751_);
lean_inc_ref(v___y_2750_);
lean_inc(v___y_2749_);
lean_inc_ref(v___y_2748_);
lean_inc(v___y_2747_);
lean_inc_ref(v___y_2746_);
lean_inc(v___y_2745_);
lean_inc_ref(v___y_2744_);
lean_inc(v___y_2743_);
lean_inc(v___y_2742_);
lean_inc_ref(v___y_2741_);
v___x_2762_ = lean_apply_12(v___x_1457__overap_2761_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, lean_box(0));
return v___x_2762_;
}
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
lean_dec_ref(v_e_2740_);
lean_dec_ref(v___f_2739_);
lean_dec_ref(v___x_2738_);
lean_dec(v___f_2737_);
lean_dec_ref(v___x_2735_);
v_a_2763_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2760_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2760_);
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
lean_object* v___x_1461__overap_2771_; lean_object* v___x_2772_; 
lean_dec_ref(v___x_2736_);
v___x_1461__overap_2771_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v___f_2737_, v___x_2735_, v___x_2738_, v___f_2739_, v_e_2740_);
lean_inc(v___y_2751_);
lean_inc_ref(v___y_2750_);
lean_inc(v___y_2749_);
lean_inc_ref(v___y_2748_);
lean_inc(v___y_2747_);
lean_inc_ref(v___y_2746_);
lean_inc(v___y_2745_);
lean_inc_ref(v___y_2744_);
lean_inc(v___y_2743_);
lean_inc(v___y_2742_);
lean_inc_ref(v___y_2741_);
v___x_2772_ = lean_apply_12(v___x_1461__overap_2771_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, lean_box(0));
return v___x_2772_;
}
}
else
{
lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2780_; 
lean_dec_ref(v_e_2740_);
lean_dec_ref(v___f_2739_);
lean_dec_ref(v___x_2738_);
lean_dec(v___f_2737_);
lean_dec_ref(v___x_2736_);
lean_dec_ref(v___x_2735_);
v_a_2773_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2775_ = v___x_2753_;
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v___x_2753_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2778_; 
if (v_isShared_2776_ == 0)
{
v___x_2778_ = v___x_2775_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_a_2773_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2735_ = stack[0].m_obj;
lean_object* v___x_2736_ = stack[1].m_obj;
lean_object* v___f_2737_ = stack[2].m_obj;
lean_object* v___x_2738_ = stack[3].m_obj;
lean_object* v___f_2739_ = stack[4].m_obj;
lean_object* v_e_2740_ = stack[5].m_obj;
lean_object* v___y_2741_ = stack[6].m_obj;
lean_object* v___y_2742_ = stack[7].m_obj;
lean_object* v___y_2743_ = stack[8].m_obj;
lean_object* v___y_2744_ = stack[9].m_obj;
lean_object* v___y_2745_ = stack[10].m_obj;
lean_object* v___y_2746_ = stack[11].m_obj;
lean_object* v___y_2747_ = stack[12].m_obj;
lean_object* v___y_2748_ = stack[13].m_obj;
lean_object* v___y_2749_ = stack[14].m_obj;
lean_object* v___y_2750_ = stack[15].m_obj;
lean_object* v___y_2751_ = stack[16].m_obj;
lean_object* v_res_2781_;
v_res_2781_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0(v___x_2735_, v___x_2736_, v___f_2737_, v___x_2738_, v___f_2739_, v_e_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
stack->m_obj
 = v_res_2781_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___boxed(lean_object** _args){
lean_object* v___x_2782_ = _args[0];
lean_object* v___x_2783_ = _args[1];
lean_object* v___f_2784_ = _args[2];
lean_object* v___x_2785_ = _args[3];
lean_object* v___f_2786_ = _args[4];
lean_object* v_e_2787_ = _args[5];
lean_object* v___y_2788_ = _args[6];
lean_object* v___y_2789_ = _args[7];
lean_object* v___y_2790_ = _args[8];
lean_object* v___y_2791_ = _args[9];
lean_object* v___y_2792_ = _args[10];
lean_object* v___y_2793_ = _args[11];
lean_object* v___y_2794_ = _args[12];
lean_object* v___y_2795_ = _args[13];
lean_object* v___y_2796_ = _args[14];
lean_object* v___y_2797_ = _args[15];
lean_object* v___y_2798_ = _args[16];
lean_object* v___y_2799_ = _args[17];
_start:
{
lean_object* v_res_2800_; 
v_res_2800_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0(v___x_2782_, v___x_2783_, v___f_2784_, v___x_2785_, v___f_2786_, v_e_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
lean_dec(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
return v_res_2800_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__0(void){
_start:
{
lean_object* v___x_2801_; 
v___x_2801_ = l_instMonadEIO___redArg();
return v___x_2801_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__1(void){
_start:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2802_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__0);
v___x_2803_ = l_StateRefT_x27_instMonad___redArg(v___x_2802_);
return v___x_2803_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__7(void){
_start:
{
lean_object* v___x_2809_; lean_object* v___f_2810_; 
v___x_2809_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_2810_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2810_, 0, v___x_2809_);
return v___f_2810_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__8(void){
_start:
{
lean_object* v___x_2811_; lean_object* v___f_2812_; 
v___x_2811_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_2812_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2812_, 0, v___x_2811_);
return v___f_2812_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__9(void){
_start:
{
lean_object* v___f_2813_; lean_object* v___f_2814_; lean_object* v___x_2815_; 
v___f_2813_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__8, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__8_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__8);
v___f_2814_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__7, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__7_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__7);
v___x_2815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___f_2814_);
lean_ctor_set(v___x_2815_, 1, v___f_2813_);
return v___x_2815_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__10(void){
_start:
{
lean_object* v___x_2816_; lean_object* v___f_2817_; 
v___x_2816_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__9, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__9_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__9);
v___f_2817_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2817_, 0, v___x_2816_);
return v___f_2817_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__11(void){
_start:
{
lean_object* v___x_2818_; lean_object* v___f_2819_; 
v___x_2818_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__9, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__9_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__9);
v___f_2819_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2819_, 0, v___x_2818_);
return v___f_2819_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__12(void){
_start:
{
lean_object* v___f_2820_; lean_object* v___f_2821_; lean_object* v___x_2822_; 
v___f_2820_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__11, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__11_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__11);
v___f_2821_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__10, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__10_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__10);
v___x_2822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2822_, 0, v___f_2821_);
lean_ctor_set(v___x_2822_, 1, v___f_2820_);
return v___x_2822_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__13(void){
_start:
{
lean_object* v___x_2823_; lean_object* v___f_2824_; 
v___x_2823_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__12);
v___f_2824_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2824_, 0, v___x_2823_);
return v___f_2824_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__14(void){
_start:
{
lean_object* v___x_2825_; lean_object* v___f_2826_; 
v___x_2825_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__12);
v___f_2826_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2826_, 0, v___x_2825_);
return v___f_2826_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__15(void){
_start:
{
lean_object* v___f_2827_; lean_object* v___f_2828_; lean_object* v___x_2829_; 
v___f_2827_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__14, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__14_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__14);
v___f_2828_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__13, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__13_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__13);
v___x_2829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___f_2828_);
lean_ctor_set(v___x_2829_, 1, v___f_2827_);
return v___x_2829_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__16(void){
_start:
{
lean_object* v___x_2830_; lean_object* v___f_2831_; 
v___x_2830_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__15, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__15_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__15);
v___f_2831_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2831_, 0, v___x_2830_);
return v___f_2831_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__17(void){
_start:
{
lean_object* v___x_2832_; lean_object* v___f_2833_; 
v___x_2832_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__15, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__15_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__15);
v___f_2833_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2833_, 0, v___x_2832_);
return v___f_2833_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__18(void){
_start:
{
lean_object* v___f_2834_; lean_object* v___f_2835_; lean_object* v___x_2836_; 
v___f_2834_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__17, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__17_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__17);
v___f_2835_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__16, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__16_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__16);
v___x_2836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2836_, 0, v___f_2835_);
lean_ctor_set(v___x_2836_, 1, v___f_2834_);
return v___x_2836_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__19(void){
_start:
{
lean_object* v___x_2837_; lean_object* v___f_2838_; 
v___x_2837_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__18, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__18_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__18);
v___f_2838_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2838_, 0, v___x_2837_);
return v___f_2838_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__20(void){
_start:
{
lean_object* v___x_2839_; lean_object* v___f_2840_; 
v___x_2839_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__18, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__18_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__18);
v___f_2840_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2840_, 0, v___x_2839_);
return v___f_2840_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__21(void){
_start:
{
lean_object* v___f_2841_; lean_object* v___f_2842_; lean_object* v___x_2843_; 
v___f_2841_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__20, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__20_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__20);
v___f_2842_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__19, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__19_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__19);
v___x_2843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2843_, 0, v___f_2842_);
lean_ctor_set(v___x_2843_, 1, v___f_2841_);
return v___x_2843_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__22(void){
_start:
{
lean_object* v___x_2844_; lean_object* v___f_2845_; 
v___x_2844_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__21, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__21_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__21);
v___f_2845_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2845_, 0, v___x_2844_);
return v___f_2845_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__23(void){
_start:
{
lean_object* v___x_2846_; lean_object* v___f_2847_; 
v___x_2846_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__21, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__21_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__21);
v___f_2847_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2847_, 0, v___x_2846_);
return v___f_2847_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__24(void){
_start:
{
lean_object* v___f_2848_; lean_object* v___f_2849_; lean_object* v___x_2850_; 
v___f_2848_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__23, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__23_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__23);
v___f_2849_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__22, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__22_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__22);
v___x_2850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2850_, 0, v___f_2849_);
lean_ctor_set(v___x_2850_, 1, v___f_2848_);
return v___x_2850_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__25(void){
_start:
{
lean_object* v___x_2851_; lean_object* v___f_2852_; 
v___x_2851_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__24, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__24_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__24);
v___f_2852_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2852_, 0, v___x_2851_);
return v___f_2852_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__26(void){
_start:
{
lean_object* v___x_2853_; lean_object* v___f_2854_; 
v___x_2853_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__24, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__24_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__24);
v___f_2854_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2854_, 0, v___x_2853_);
return v___f_2854_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__27(void){
_start:
{
lean_object* v___f_2855_; lean_object* v___f_2856_; lean_object* v___x_2857_; 
v___f_2855_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__26, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__26_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__26);
v___f_2856_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__25, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__25_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__25);
v___x_2857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2857_, 0, v___f_2856_);
lean_ctor_set(v___x_2857_, 1, v___f_2855_);
return v___x_2857_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__28(void){
_start:
{
lean_object* v___x_2858_; lean_object* v___f_2859_; 
v___x_2858_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__27, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__27_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__27);
v___f_2859_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2859_, 0, v___x_2858_);
return v___f_2859_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__29(void){
_start:
{
lean_object* v___x_2860_; lean_object* v___f_2861_; 
v___x_2860_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__27, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__27_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__27);
v___f_2861_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2861_, 0, v___x_2860_);
return v___f_2861_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__30(void){
_start:
{
lean_object* v___f_2862_; lean_object* v___f_2863_; lean_object* v___x_2864_; 
v___f_2862_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__29, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__29_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__29);
v___f_2863_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__28, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__28_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__28);
v___x_2864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___f_2863_);
lean_ctor_set(v___x_2864_, 1, v___f_2862_);
return v___x_2864_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__31(void){
_start:
{
lean_object* v___x_2865_; lean_object* v___f_2866_; 
v___x_2865_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__30, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__30_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__30);
v___f_2866_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2866_, 0, v___x_2865_);
return v___f_2866_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__32(void){
_start:
{
lean_object* v___x_2867_; lean_object* v___f_2868_; 
v___x_2867_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__30, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__30_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__30);
v___f_2868_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2868_, 0, v___x_2867_);
return v___f_2868_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__33(void){
_start:
{
lean_object* v___f_2869_; lean_object* v___f_2870_; lean_object* v___x_2871_; 
v___f_2869_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__32, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__32_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__32);
v___f_2870_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__31, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__31_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__31);
v___x_2871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___f_2870_);
lean_ctor_set(v___x_2871_, 1, v___f_2869_);
return v___x_2871_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__37(void){
_start:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2875_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2876_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__36));
v___x_2877_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__35));
v___x_2878_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2877_, v___x_2876_, v___x_2875_);
return v___x_2878_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__38(void){
_start:
{
lean_object* v___x_2879_; lean_object* v___f_2880_; lean_object* v___f_2881_; lean_object* v___x_2882_; 
v___x_2879_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__37, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__37_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__37);
v___f_2880_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6));
v___f_2881_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__34));
v___x_2882_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2881_, v___f_2880_, v___x_2879_);
return v___x_2882_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__39(void){
_start:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2883_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__38, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__38_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__38);
v___x_2884_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__36));
v___x_2885_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__35));
v___x_2886_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2885_, v___x_2884_, v___x_2883_);
return v___x_2886_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__40(void){
_start:
{
lean_object* v___x_2887_; lean_object* v___f_2888_; lean_object* v___f_2889_; lean_object* v___x_2890_; 
v___x_2887_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__39, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__39_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__39);
v___f_2888_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6));
v___f_2889_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__34));
v___x_2890_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2889_, v___f_2888_, v___x_2887_);
return v___x_2890_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__41(void){
_start:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2891_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__40, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__40_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__40);
v___x_2892_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__36));
v___x_2893_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__35));
v___x_2894_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2893_, v___x_2892_, v___x_2891_);
return v___x_2894_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__42(void){
_start:
{
lean_object* v___x_2895_; lean_object* v___f_2896_; lean_object* v___f_2897_; lean_object* v___x_2898_; 
v___x_2895_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__41, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__41_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__41);
v___f_2896_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6));
v___f_2897_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__34));
v___x_2898_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2897_, v___f_2896_, v___x_2895_);
return v___x_2898_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__43(void){
_start:
{
lean_object* v___x_2899_; lean_object* v___f_2900_; lean_object* v___f_2901_; lean_object* v___x_2902_; 
v___x_2899_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__42, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__42_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__42);
v___f_2900_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6));
v___f_2901_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__34));
v___x_2902_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2901_, v___f_2900_, v___x_2899_);
return v___x_2902_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__44(void){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2903_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__43, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__43_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__43);
v___x_2904_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__36));
v___x_2905_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__35));
v___x_2906_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2905_, v___x_2904_, v___x_2903_);
return v___x_2906_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__45(void){
_start:
{
lean_object* v___x_2907_; lean_object* v___f_2908_; lean_object* v___f_2909_; lean_object* v___x_2910_; 
v___x_2907_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__44, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__44_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__44);
v___f_2908_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6));
v___f_2909_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__34));
v___x_2910_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2909_, v___f_2908_, v___x_2907_);
return v___x_2910_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__48(void){
_start:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___f_2917_; 
v___x_2915_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__36));
v___x_2916_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_2917_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2917_, 0, v___x_2916_);
lean_closure_set(v___f_2917_, 1, v___x_2915_);
return v___f_2917_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__49(void){
_start:
{
lean_object* v___f_2918_; lean_object* v___f_2919_; lean_object* v___f_2920_; 
v___f_2918_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6));
v___f_2919_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__48, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__48_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__48);
v___f_2920_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2920_, 0, v___f_2919_);
lean_closure_set(v___f_2920_, 1, v___f_2918_);
return v___f_2920_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__50(void){
_start:
{
lean_object* v___x_2921_; lean_object* v___f_2922_; lean_object* v___f_2923_; 
v___x_2921_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__36));
v___f_2922_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__49, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__49_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__49);
v___f_2923_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2923_, 0, v___f_2922_);
lean_closure_set(v___f_2923_, 1, v___x_2921_);
return v___f_2923_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__51(void){
_start:
{
lean_object* v___f_2924_; lean_object* v___f_2925_; lean_object* v___f_2926_; 
v___f_2924_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6));
v___f_2925_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__50, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__50_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__50);
v___f_2926_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2926_, 0, v___f_2925_);
lean_closure_set(v___f_2926_, 1, v___f_2924_);
return v___f_2926_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__52(void){
_start:
{
lean_object* v___f_2927_; lean_object* v___f_2928_; lean_object* v___f_2929_; 
v___f_2927_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6));
v___f_2928_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__51, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__51_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__51);
v___f_2929_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2929_, 0, v___f_2928_);
lean_closure_set(v___f_2929_, 1, v___f_2927_);
return v___f_2929_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__53(void){
_start:
{
lean_object* v___x_2930_; lean_object* v___f_2931_; lean_object* v___f_2932_; 
v___x_2930_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__36));
v___f_2931_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__52, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__52_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__52);
v___f_2932_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2932_, 0, v___f_2931_);
lean_closure_set(v___f_2932_, 1, v___x_2930_);
return v___f_2932_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__54(void){
_start:
{
lean_object* v___f_2933_; lean_object* v___f_2934_; lean_object* v___f_2935_; 
v___f_2933_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6));
v___f_2934_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__53, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__53_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__53);
v___f_2935_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2935_, 0, v___f_2934_);
lean_closure_set(v___f_2935_, 1, v___f_2933_);
return v___f_2935_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM(void){
_start:
{
lean_object* v___x_2936_; lean_object* v_toApplicative_2937_; lean_object* v_toFunctor_2938_; lean_object* v_toSeq_2939_; lean_object* v_toSeqLeft_2940_; lean_object* v_toSeqRight_2941_; lean_object* v___f_2942_; lean_object* v___f_2943_; lean_object* v___f_2944_; lean_object* v___f_2945_; lean_object* v___x_2946_; lean_object* v___f_2947_; lean_object* v___f_2948_; lean_object* v___f_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v_toApplicative_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_3006_; 
v___x_2936_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__1);
v_toApplicative_2937_ = lean_ctor_get(v___x_2936_, 0);
v_toFunctor_2938_ = lean_ctor_get(v_toApplicative_2937_, 0);
v_toSeq_2939_ = lean_ctor_get(v_toApplicative_2937_, 2);
v_toSeqLeft_2940_ = lean_ctor_get(v_toApplicative_2937_, 3);
v_toSeqRight_2941_ = lean_ctor_get(v_toApplicative_2937_, 4);
v___f_2942_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__2));
v___f_2943_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__3));
lean_inc_ref_n(v_toFunctor_2938_, 2);
v___f_2944_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2944_, 0, v_toFunctor_2938_);
v___f_2945_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2945_, 0, v_toFunctor_2938_);
v___x_2946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2946_, 0, v___f_2944_);
lean_ctor_set(v___x_2946_, 1, v___f_2945_);
lean_inc(v_toSeqRight_2941_);
v___f_2947_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2947_, 0, v_toSeqRight_2941_);
lean_inc(v_toSeqLeft_2940_);
v___f_2948_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2948_, 0, v_toSeqLeft_2940_);
lean_inc(v_toSeq_2939_);
v___f_2949_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2949_, 0, v_toSeq_2939_);
v___x_2950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2946_);
lean_ctor_set(v___x_2950_, 1, v___f_2942_);
lean_ctor_set(v___x_2950_, 2, v___f_2949_);
lean_ctor_set(v___x_2950_, 3, v___f_2948_);
lean_ctor_set(v___x_2950_, 4, v___f_2947_);
v___x_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
lean_ctor_set(v___x_2951_, 1, v___f_2943_);
v___x_2952_ = l_StateRefT_x27_instMonad___redArg(v___x_2951_);
v_toApplicative_2953_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_3006_ == 0)
{
lean_object* v_unused_3007_; 
v_unused_3007_ = lean_ctor_get(v___x_2952_, 1);
lean_dec(v_unused_3007_);
v___x_2955_ = v___x_2952_;
v_isShared_2956_ = v_isSharedCheck_3006_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_toApplicative_2953_);
lean_dec(v___x_2952_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_3006_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v_toFunctor_2957_; lean_object* v_toSeq_2958_; lean_object* v_toSeqLeft_2959_; lean_object* v_toSeqRight_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_3004_; 
v_toFunctor_2957_ = lean_ctor_get(v_toApplicative_2953_, 0);
v_toSeq_2958_ = lean_ctor_get(v_toApplicative_2953_, 2);
v_toSeqLeft_2959_ = lean_ctor_get(v_toApplicative_2953_, 3);
v_toSeqRight_2960_ = lean_ctor_get(v_toApplicative_2953_, 4);
v_isSharedCheck_3004_ = !lean_is_exclusive(v_toApplicative_2953_);
if (v_isSharedCheck_3004_ == 0)
{
lean_object* v_unused_3005_; 
v_unused_3005_ = lean_ctor_get(v_toApplicative_2953_, 1);
lean_dec(v_unused_3005_);
v___x_2962_ = v_toApplicative_2953_;
v_isShared_2963_ = v_isSharedCheck_3004_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_toSeqRight_2960_);
lean_inc(v_toSeqLeft_2959_);
lean_inc(v_toSeq_2958_);
lean_inc(v_toFunctor_2957_);
lean_dec(v_toApplicative_2953_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_3004_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___f_2964_; lean_object* v___f_2965_; lean_object* v___f_2966_; lean_object* v___f_2967_; lean_object* v___x_2968_; lean_object* v___f_2969_; lean_object* v___f_2970_; lean_object* v___f_2971_; lean_object* v___x_2973_; 
v___f_2964_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__4));
v___f_2965_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__5));
lean_inc_ref(v_toFunctor_2957_);
v___f_2966_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2966_, 0, v_toFunctor_2957_);
v___f_2967_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2967_, 0, v_toFunctor_2957_);
v___x_2968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2968_, 0, v___f_2966_);
lean_ctor_set(v___x_2968_, 1, v___f_2967_);
v___f_2969_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2969_, 0, v_toSeqRight_2960_);
v___f_2970_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2970_, 0, v_toSeqLeft_2959_);
v___f_2971_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2971_, 0, v_toSeq_2958_);
if (v_isShared_2963_ == 0)
{
lean_ctor_set(v___x_2962_, 4, v___f_2969_);
lean_ctor_set(v___x_2962_, 3, v___f_2970_);
lean_ctor_set(v___x_2962_, 2, v___f_2971_);
lean_ctor_set(v___x_2962_, 1, v___f_2964_);
lean_ctor_set(v___x_2962_, 0, v___x_2968_);
v___x_2973_ = v___x_2962_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v___x_2968_);
lean_ctor_set(v_reuseFailAlloc_3003_, 1, v___f_2964_);
lean_ctor_set(v_reuseFailAlloc_3003_, 2, v___f_2971_);
lean_ctor_set(v_reuseFailAlloc_3003_, 3, v___f_2970_);
lean_ctor_set(v_reuseFailAlloc_3003_, 4, v___f_2969_);
v___x_2973_ = v_reuseFailAlloc_3003_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
lean_object* v___x_2975_; 
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 1, v___f_2965_);
lean_ctor_set(v___x_2955_, 0, v___x_2973_);
v___x_2975_ = v___x_2955_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v___x_2973_);
lean_ctor_set(v_reuseFailAlloc_3002_, 1, v___f_2965_);
v___x_2975_ = v_reuseFailAlloc_3002_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v_toApplicative_2984_; lean_object* v_toBind_2985_; lean_object* v_getCommRingState_2986_; lean_object* v_modifyCommRingState_2987_; lean_object* v_toPure_2988_; lean_object* v___f_2989_; lean_object* v___f_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v_toMonadRef_2995_; lean_object* v___f_2996_; lean_object* v___f_2997_; lean_object* v___f_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___f_3001_; 
v___x_2976_ = l_StateRefT_x27_instMonad___redArg(v___x_2975_);
v___x_2977_ = l_ReaderT_instMonad___redArg(v___x_2976_);
v___x_2978_ = l_StateRefT_x27_instMonad___redArg(v___x_2977_);
v___x_2979_ = l_ReaderT_instMonad___redArg(v___x_2978_);
v___x_2980_ = l_ReaderT_instMonad___redArg(v___x_2979_);
v___x_2981_ = l_StateRefT_x27_instMonad___redArg(v___x_2980_);
v___x_2982_ = l_ReaderT_instMonad___redArg(v___x_2981_);
v___x_2983_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM;
v_toApplicative_2984_ = lean_ctor_get(v___x_2982_, 0);
v_toBind_2985_ = lean_ctor_get(v___x_2982_, 1);
v_getCommRingState_2986_ = lean_ctor_get(v___x_2983_, 0);
v_modifyCommRingState_2987_ = lean_ctor_get(v___x_2983_, 1);
v_toPure_2988_ = lean_ctor_get(v_toApplicative_2984_, 1);
lean_inc(v_modifyCommRingState_2987_);
v___f_2989_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2989_, 0, v_modifyCommRingState_2987_);
lean_inc(v_toPure_2988_);
v___f_2990_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2990_, 0, v_toPure_2988_);
lean_inc(v_toBind_2985_);
lean_inc(v_getCommRingState_2986_);
v___x_2991_ = lean_apply_4(v_toBind_2985_, lean_box(0), lean_box(0), v_getCommRingState_2986_, v___f_2990_);
v___x_2992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2991_);
lean_ctor_set(v___x_2992_, 1, v___f_2989_);
v___x_2993_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__33, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__33_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__33);
v___x_2994_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__45, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__45_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__45);
v_toMonadRef_2995_ = lean_ctor_get(v___x_2994_, 0);
v___f_2996_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__47));
v___f_2997_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___closed__0));
v___f_2998_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__54, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__54_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__54);
lean_inc_ref(v___x_2982_);
v___x_2999_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_2998_, v___x_2982_);
lean_inc_ref(v_toMonadRef_2995_);
v___x_3000_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2993_);
lean_ctor_set(v___x_3000_, 1, v_toMonadRef_2995_);
lean_ctor_set(v___x_3000_, 2, v___x_2999_);
v___f_3001_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___boxed), 18, 5);
lean_closure_set(v___f_3001_, 0, v___x_2982_);
lean_closure_set(v___f_3001_, 1, v___x_3000_);
lean_closure_set(v___f_3001_, 2, v___f_2996_);
lean_closure_set(v___f_3001_, 3, v___x_2992_);
lean_closure_set(v___f_3001_, 4, v___f_2997_);
return v___f_3001_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0(void){
_start:
{
lean_object* v___x_3008_; lean_object* v_n_3009_; 
v___x_3008_ = lean_unsigned_to_nat(1u);
v_n_3009_ = l_Lean_mkRawNatLit(v___x_3008_);
return v_n_3009_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(lean_object* v_u_3023_, lean_object* v_type_3024_, lean_object* v_semiringInst_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_){
_start:
{
lean_object* v_n_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v_ofNatInst_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v_n_3033_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0);
v___x_3034_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__5));
v___x_3035_ = lean_box(0);
v___x_3036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3036_, 0, v_u_3023_);
lean_ctor_set(v___x_3036_, 1, v___x_3035_);
lean_inc_ref(v___x_3036_);
v___x_3037_ = l_Lean_mkConst(v___x_3034_, v___x_3036_);
lean_inc_ref(v_type_3024_);
v_ofNatInst_3038_ = l_Lean_mkApp3(v___x_3037_, v_type_3024_, v_semiringInst_3025_, v_n_3033_);
v___x_3039_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__7));
v___x_3040_ = l_Lean_mkConst(v___x_3039_, v___x_3036_);
v___x_3041_ = l_Lean_mkApp3(v___x_3040_, v_type_3024_, v_n_3033_, v_ofNatInst_3038_);
v___x_3042_ = l_Lean_Meta_Sym_canon(v___x_3041_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; lean_object* v___x_3044_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3043_);
lean_dec_ref_known(v___x_3042_, 1);
v___x_3044_ = l_Lean_Meta_Sym_shareCommon(v_a_3043_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_);
return v___x_3044_;
}
else
{
return v___x_3042_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_3023_ = stack[0].m_obj;
lean_object* v_type_3024_ = stack[1].m_obj;
lean_object* v_semiringInst_3025_ = stack[2].m_obj;
lean_object* v_a_3026_ = stack[3].m_obj;
lean_object* v_a_3027_ = stack[4].m_obj;
lean_object* v_a_3028_ = stack[5].m_obj;
lean_object* v_a_3029_ = stack[6].m_obj;
lean_object* v_a_3030_ = stack[7].m_obj;
lean_object* v_a_3031_ = stack[8].m_obj;
lean_object* v_res_3045_;
v_res_3045_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(v_u_3023_, v_type_3024_, v_semiringInst_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_);
stack->m_obj
 = v_res_3045_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___boxed(lean_object* v_u_3046_, lean_object* v_type_3047_, lean_object* v_semiringInst_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_){
_start:
{
lean_object* v_res_3056_; 
v_res_3056_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(v_u_3046_, v_type_3047_, v_semiringInst_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_);
lean_dec(v_a_3054_);
lean_dec_ref(v_a_3053_);
lean_dec(v_a_3052_);
lean_dec_ref(v_a_3051_);
lean_dec(v_a_3050_);
lean_dec_ref(v_a_3049_);
return v_res_3056_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne(lean_object* v_u_3057_, lean_object* v_type_3058_, lean_object* v_semiringInst_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_){
_start:
{
lean_object* v___x_3072_; 
v___x_3072_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(v_u_3057_, v_type_3058_, v_semiringInst_3059_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_);
return v___x_3072_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_3057_ = stack[0].m_obj;
lean_object* v_type_3058_ = stack[1].m_obj;
lean_object* v_semiringInst_3059_ = stack[2].m_obj;
lean_object* v_a_3060_ = stack[3].m_obj;
lean_object* v_a_3061_ = stack[4].m_obj;
lean_object* v_a_3062_ = stack[5].m_obj;
lean_object* v_a_3063_ = stack[6].m_obj;
lean_object* v_a_3064_ = stack[7].m_obj;
lean_object* v_a_3065_ = stack[8].m_obj;
lean_object* v_a_3066_ = stack[9].m_obj;
lean_object* v_a_3067_ = stack[10].m_obj;
lean_object* v_a_3068_ = stack[11].m_obj;
lean_object* v_a_3069_ = stack[12].m_obj;
lean_object* v_a_3070_ = stack[13].m_obj;
lean_object* v_res_3073_;
v_res_3073_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne(v_u_3057_, v_type_3058_, v_semiringInst_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_);
stack->m_obj
 = v_res_3073_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___boxed(lean_object* v_u_3074_, lean_object* v_type_3075_, lean_object* v_semiringInst_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne(v_u_3074_, v_type_3075_, v_semiringInst_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_);
lean_dec(v_a_3087_);
lean_dec_ref(v_a_3086_);
lean_dec(v_a_3085_);
lean_dec_ref(v_a_3084_);
lean_dec(v_a_3083_);
lean_dec_ref(v_a_3082_);
lean_dec(v_a_3081_);
lean_dec_ref(v_a_3080_);
lean_dec(v_a_3079_);
lean_dec(v_a_3078_);
lean_dec_ref(v_a_3077_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___lam__0(lean_object* v_a_3090_, lean_object* v_s_3091_){
_start:
{
lean_object* v_toRing_3092_; lean_object* v_invFn_x3f_3093_; lean_object* v_divFn_x3f_3094_; lean_object* v_semiringId_x3f_3095_; lean_object* v_commSemiringInst_3096_; lean_object* v_commRingInst_3097_; lean_object* v_noZeroDivInst_x3f_3098_; lean_object* v_fieldInst_x3f_3099_; lean_object* v_powIdentityInst_x3f_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3131_; 
v_toRing_3092_ = lean_ctor_get(v_s_3091_, 0);
v_invFn_x3f_3093_ = lean_ctor_get(v_s_3091_, 1);
v_divFn_x3f_3094_ = lean_ctor_get(v_s_3091_, 2);
v_semiringId_x3f_3095_ = lean_ctor_get(v_s_3091_, 3);
v_commSemiringInst_3096_ = lean_ctor_get(v_s_3091_, 4);
v_commRingInst_3097_ = lean_ctor_get(v_s_3091_, 5);
v_noZeroDivInst_x3f_3098_ = lean_ctor_get(v_s_3091_, 6);
v_fieldInst_x3f_3099_ = lean_ctor_get(v_s_3091_, 7);
v_powIdentityInst_x3f_3100_ = lean_ctor_get(v_s_3091_, 8);
v_isSharedCheck_3131_ = !lean_is_exclusive(v_s_3091_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3102_ = v_s_3091_;
v_isShared_3103_ = v_isSharedCheck_3131_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_powIdentityInst_x3f_3100_);
lean_inc(v_fieldInst_x3f_3099_);
lean_inc(v_noZeroDivInst_x3f_3098_);
lean_inc(v_commRingInst_3097_);
lean_inc(v_commSemiringInst_3096_);
lean_inc(v_semiringId_x3f_3095_);
lean_inc(v_divFn_x3f_3094_);
lean_inc(v_invFn_x3f_3093_);
lean_inc(v_toRing_3092_);
lean_dec(v_s_3091_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3131_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v_id_3104_; lean_object* v_type_3105_; lean_object* v_u_3106_; lean_object* v_ringInst_3107_; lean_object* v_semiringInst_3108_; lean_object* v_charInst_x3f_3109_; lean_object* v_addFn_x3f_3110_; lean_object* v_mulFn_x3f_3111_; lean_object* v_subFn_x3f_3112_; lean_object* v_negFn_x3f_3113_; lean_object* v_powFn_x3f_3114_; lean_object* v_intCastFn_x3f_3115_; lean_object* v_natCastFn_x3f_3116_; lean_object* v_natSMulFn_x3f_3117_; lean_object* v_intSMulFn_x3f_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3129_; 
v_id_3104_ = lean_ctor_get(v_toRing_3092_, 0);
v_type_3105_ = lean_ctor_get(v_toRing_3092_, 1);
v_u_3106_ = lean_ctor_get(v_toRing_3092_, 2);
v_ringInst_3107_ = lean_ctor_get(v_toRing_3092_, 3);
v_semiringInst_3108_ = lean_ctor_get(v_toRing_3092_, 4);
v_charInst_x3f_3109_ = lean_ctor_get(v_toRing_3092_, 5);
v_addFn_x3f_3110_ = lean_ctor_get(v_toRing_3092_, 6);
v_mulFn_x3f_3111_ = lean_ctor_get(v_toRing_3092_, 7);
v_subFn_x3f_3112_ = lean_ctor_get(v_toRing_3092_, 8);
v_negFn_x3f_3113_ = lean_ctor_get(v_toRing_3092_, 9);
v_powFn_x3f_3114_ = lean_ctor_get(v_toRing_3092_, 10);
v_intCastFn_x3f_3115_ = lean_ctor_get(v_toRing_3092_, 11);
v_natCastFn_x3f_3116_ = lean_ctor_get(v_toRing_3092_, 12);
v_natSMulFn_x3f_3117_ = lean_ctor_get(v_toRing_3092_, 13);
v_intSMulFn_x3f_3118_ = lean_ctor_get(v_toRing_3092_, 14);
v_isSharedCheck_3129_ = !lean_is_exclusive(v_toRing_3092_);
if (v_isSharedCheck_3129_ == 0)
{
lean_object* v_unused_3130_; 
v_unused_3130_ = lean_ctor_get(v_toRing_3092_, 15);
lean_dec(v_unused_3130_);
v___x_3120_ = v_toRing_3092_;
v_isShared_3121_ = v_isSharedCheck_3129_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_intSMulFn_x3f_3118_);
lean_inc(v_natSMulFn_x3f_3117_);
lean_inc(v_natCastFn_x3f_3116_);
lean_inc(v_intCastFn_x3f_3115_);
lean_inc(v_powFn_x3f_3114_);
lean_inc(v_negFn_x3f_3113_);
lean_inc(v_subFn_x3f_3112_);
lean_inc(v_mulFn_x3f_3111_);
lean_inc(v_addFn_x3f_3110_);
lean_inc(v_charInst_x3f_3109_);
lean_inc(v_semiringInst_3108_);
lean_inc(v_ringInst_3107_);
lean_inc(v_u_3106_);
lean_inc(v_type_3105_);
lean_inc(v_id_3104_);
lean_dec(v_toRing_3092_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3129_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3122_; lean_object* v___x_3124_; 
v___x_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3122_, 0, v_a_3090_);
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 15, v___x_3122_);
v___x_3124_ = v___x_3120_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_id_3104_);
lean_ctor_set(v_reuseFailAlloc_3128_, 1, v_type_3105_);
lean_ctor_set(v_reuseFailAlloc_3128_, 2, v_u_3106_);
lean_ctor_set(v_reuseFailAlloc_3128_, 3, v_ringInst_3107_);
lean_ctor_set(v_reuseFailAlloc_3128_, 4, v_semiringInst_3108_);
lean_ctor_set(v_reuseFailAlloc_3128_, 5, v_charInst_x3f_3109_);
lean_ctor_set(v_reuseFailAlloc_3128_, 6, v_addFn_x3f_3110_);
lean_ctor_set(v_reuseFailAlloc_3128_, 7, v_mulFn_x3f_3111_);
lean_ctor_set(v_reuseFailAlloc_3128_, 8, v_subFn_x3f_3112_);
lean_ctor_set(v_reuseFailAlloc_3128_, 9, v_negFn_x3f_3113_);
lean_ctor_set(v_reuseFailAlloc_3128_, 10, v_powFn_x3f_3114_);
lean_ctor_set(v_reuseFailAlloc_3128_, 11, v_intCastFn_x3f_3115_);
lean_ctor_set(v_reuseFailAlloc_3128_, 12, v_natCastFn_x3f_3116_);
lean_ctor_set(v_reuseFailAlloc_3128_, 13, v_natSMulFn_x3f_3117_);
lean_ctor_set(v_reuseFailAlloc_3128_, 14, v_intSMulFn_x3f_3118_);
lean_ctor_set(v_reuseFailAlloc_3128_, 15, v___x_3122_);
v___x_3124_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
lean_object* v___x_3126_; 
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 0, v___x_3124_);
v___x_3126_ = v___x_3102_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3124_);
lean_ctor_set(v_reuseFailAlloc_3127_, 1, v_invFn_x3f_3093_);
lean_ctor_set(v_reuseFailAlloc_3127_, 2, v_divFn_x3f_3094_);
lean_ctor_set(v_reuseFailAlloc_3127_, 3, v_semiringId_x3f_3095_);
lean_ctor_set(v_reuseFailAlloc_3127_, 4, v_commSemiringInst_3096_);
lean_ctor_set(v_reuseFailAlloc_3127_, 5, v_commRingInst_3097_);
lean_ctor_set(v_reuseFailAlloc_3127_, 6, v_noZeroDivInst_x3f_3098_);
lean_ctor_set(v_reuseFailAlloc_3127_, 7, v_fieldInst_x3f_3099_);
lean_ctor_set(v_reuseFailAlloc_3127_, 8, v_powIdentityInst_x3f_3100_);
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
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3132_, lean_object* v_i_3133_, lean_object* v_k_3134_){
_start:
{
lean_object* v___x_3135_; uint8_t v___x_3136_; 
v___x_3135_ = lean_array_get_size(v_keys_3132_);
v___x_3136_ = lean_nat_dec_lt(v_i_3133_, v___x_3135_);
if (v___x_3136_ == 0)
{
lean_dec(v_i_3133_);
return v___x_3136_;
}
else
{
lean_object* v_k_x27_3137_; size_t v___x_3138_; size_t v___x_3139_; uint8_t v___x_3140_; 
v_k_x27_3137_ = lean_array_fget_borrowed(v_keys_3132_, v_i_3133_);
v___x_3138_ = lean_ptr_addr(v_k_3134_);
v___x_3139_ = lean_ptr_addr(v_k_x27_3137_);
v___x_3140_ = lean_usize_dec_eq(v___x_3138_, v___x_3139_);
if (v___x_3140_ == 0)
{
lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3141_ = lean_unsigned_to_nat(1u);
v___x_3142_ = lean_nat_add(v_i_3133_, v___x_3141_);
lean_dec(v_i_3133_);
v_i_3133_ = v___x_3142_;
goto _start;
}
else
{
lean_dec(v_i_3133_);
return v___x_3136_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_3132_ = stack[0].m_obj;
lean_object* v_i_3133_ = stack[1].m_obj;
lean_object* v_k_3134_ = stack[2].m_obj;
uint8_t v_res_3144_;
v_res_3144_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg(v_keys_3132_, v_i_3133_, v_k_3134_);
stack->m_num = v_res_3144_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3145_, lean_object* v_i_3146_, lean_object* v_k_3147_){
_start:
{
uint8_t v_res_3148_; lean_object* v_r_3149_; 
v_res_3148_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg(v_keys_3145_, v_i_3146_, v_k_3147_);
lean_dec_ref(v_k_3147_);
lean_dec_ref(v_keys_3145_);
v_r_3149_ = lean_box(v_res_3148_);
return v_r_3149_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg(lean_object* v_x_3150_, size_t v_x_3151_, lean_object* v_x_3152_){
_start:
{
if (lean_obj_tag(v_x_3150_) == 0)
{
lean_object* v_es_3153_; lean_object* v___x_3154_; size_t v___x_3155_; size_t v___x_3156_; lean_object* v_j_3157_; lean_object* v___x_3158_; 
v_es_3153_ = lean_ctor_get(v_x_3150_, 0);
v___x_3154_ = lean_box(2);
v___x_3155_ = ((size_t)31ULL);
v___x_3156_ = lean_usize_land(v_x_3151_, v___x_3155_);
v_j_3157_ = lean_usize_to_nat(v___x_3156_);
v___x_3158_ = lean_array_get_borrowed(v___x_3154_, v_es_3153_, v_j_3157_);
lean_dec(v_j_3157_);
switch(lean_obj_tag(v___x_3158_))
{
case 0:
{
lean_object* v_key_3159_; size_t v___x_3160_; size_t v___x_3161_; uint8_t v___x_3162_; 
v_key_3159_ = lean_ctor_get(v___x_3158_, 0);
v___x_3160_ = lean_ptr_addr(v_x_3152_);
v___x_3161_ = lean_ptr_addr(v_key_3159_);
v___x_3162_ = lean_usize_dec_eq(v___x_3160_, v___x_3161_);
return v___x_3162_;
}
case 1:
{
lean_object* v_node_3163_; size_t v___x_3164_; size_t v___x_3165_; 
v_node_3163_ = lean_ctor_get(v___x_3158_, 0);
v___x_3164_ = ((size_t)5ULL);
v___x_3165_ = lean_usize_shift_right(v_x_3151_, v___x_3164_);
v_x_3150_ = v_node_3163_;
v_x_3151_ = v___x_3165_;
goto _start;
}
default: 
{
uint8_t v___x_3167_; 
v___x_3167_ = 0;
return v___x_3167_;
}
}
}
else
{
lean_object* v_ks_3168_; lean_object* v___x_3169_; uint8_t v___x_3170_; 
v_ks_3168_ = lean_ctor_get(v_x_3150_, 0);
v___x_3169_ = lean_unsigned_to_nat(0u);
v___x_3170_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg(v_ks_3168_, v___x_3169_, v_x_3152_);
return v___x_3170_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3150_ = stack[0].m_obj;
size_t v_x_3151_ = stack[1].m_num;
lean_object* v_x_3152_ = stack[2].m_obj;
uint8_t v_res_3171_;
v_res_3171_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg(v_x_3150_, v_x_3151_, v_x_3152_);
stack->m_num = v_res_3171_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg___boxed(lean_object* v_x_3172_, lean_object* v_x_3173_, lean_object* v_x_3174_){
_start:
{
size_t v_x_9679__boxed_3175_; uint8_t v_res_3176_; lean_object* v_r_3177_; 
v_x_9679__boxed_3175_ = lean_unbox_usize(v_x_3173_);
lean_dec(v_x_3173_);
v_res_3176_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg(v_x_3172_, v_x_9679__boxed_3175_, v_x_3174_);
lean_dec_ref(v_x_3174_);
lean_dec_ref(v_x_3172_);
v_r_3177_ = lean_box(v_res_3176_);
return v_r_3177_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg(lean_object* v_x_3178_, lean_object* v_x_3179_){
_start:
{
size_t v___x_3180_; size_t v___x_3181_; size_t v___x_3182_; uint64_t v___x_3183_; size_t v___x_3184_; uint8_t v___x_3185_; 
v___x_3180_ = lean_ptr_addr(v_x_3179_);
v___x_3181_ = ((size_t)3ULL);
v___x_3182_ = lean_usize_shift_right(v___x_3180_, v___x_3181_);
v___x_3183_ = lean_usize_to_uint64(v___x_3182_);
v___x_3184_ = lean_uint64_to_usize(v___x_3183_);
v___x_3185_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg(v_x_3178_, v___x_3184_, v_x_3179_);
return v___x_3185_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3178_ = stack[0].m_obj;
lean_object* v_x_3179_ = stack[1].m_obj;
uint8_t v_res_3186_;
v_res_3186_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg(v_x_3178_, v_x_3179_);
stack->m_num = v_res_3186_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg___boxed(lean_object* v_x_3187_, lean_object* v_x_3188_){
_start:
{
uint8_t v_res_3189_; lean_object* v_r_3190_; 
v_res_3189_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg(v_x_3187_, v_x_3188_);
lean_dec_ref(v_x_3188_);
lean_dec_ref(v_x_3187_);
v_r_3190_ = lean_box(v_res_3189_);
return v_r_3190_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne(lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_){
_start:
{
lean_object* v_one_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___x_3255_; 
v___x_3255_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_object* v_a_3256_; lean_object* v_toRing_3257_; lean_object* v_one_x3f_3258_; 
v_a_3256_ = lean_ctor_get(v___x_3255_, 0);
lean_inc(v_a_3256_);
lean_dec_ref_known(v___x_3255_, 1);
v_toRing_3257_ = lean_ctor_get(v_a_3256_, 0);
lean_inc_ref(v_toRing_3257_);
lean_dec(v_a_3256_);
v_one_x3f_3258_ = lean_ctor_get(v_toRing_3257_, 15);
if (lean_obj_tag(v_one_x3f_3258_) == 1)
{
lean_object* v_val_3259_; 
lean_inc_ref(v_one_x3f_3258_);
lean_dec_ref(v_toRing_3257_);
v_val_3259_ = lean_ctor_get(v_one_x3f_3258_, 0);
lean_inc(v_val_3259_);
lean_dec_ref_known(v_one_x3f_3258_, 1);
v_one_3204_ = v_val_3259_;
v___y_3205_ = v_a_3191_;
v___y_3206_ = v_a_3192_;
v___y_3207_ = v_a_3193_;
v___y_3208_ = v_a_3194_;
v___y_3209_ = v_a_3195_;
v___y_3210_ = v_a_3196_;
v___y_3211_ = v_a_3197_;
v___y_3212_ = v_a_3198_;
v___y_3213_ = v_a_3199_;
v___y_3214_ = v_a_3200_;
v___y_3215_ = v_a_3201_;
goto v___jp_3203_;
}
else
{
lean_object* v_type_3260_; lean_object* v_u_3261_; lean_object* v_semiringInst_3262_; lean_object* v___x_3263_; 
v_type_3260_ = lean_ctor_get(v_toRing_3257_, 1);
lean_inc_ref(v_type_3260_);
v_u_3261_ = lean_ctor_get(v_toRing_3257_, 2);
lean_inc(v_u_3261_);
v_semiringInst_3262_ = lean_ctor_get(v_toRing_3257_, 4);
lean_inc_ref(v_semiringInst_3262_);
lean_dec_ref(v_toRing_3257_);
v___x_3263_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(v_u_3261_, v_type_3260_, v_semiringInst_3262_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
if (lean_obj_tag(v___x_3263_) == 0)
{
lean_object* v_a_3264_; lean_object* v___f_3265_; lean_object* v___x_3266_; 
v_a_3264_ = lean_ctor_get(v___x_3263_, 0);
lean_inc_n(v_a_3264_, 2);
lean_dec_ref_known(v___x_3263_, 1);
v___f_3265_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getOne___lam__0), 2, 1);
lean_closure_set(v___f_3265_, 0, v_a_3264_);
v___x_3266_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_3265_, v_a_3191_, v_a_3197_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_dec_ref_known(v___x_3266_, 1);
v_one_3204_ = v_a_3264_;
v___y_3205_ = v_a_3191_;
v___y_3206_ = v_a_3192_;
v___y_3207_ = v_a_3193_;
v___y_3208_ = v_a_3194_;
v___y_3209_ = v_a_3195_;
v___y_3210_ = v_a_3196_;
v___y_3211_ = v_a_3197_;
v___y_3212_ = v_a_3198_;
v___y_3213_ = v_a_3199_;
v___y_3214_ = v_a_3200_;
v___y_3215_ = v_a_3201_;
goto v___jp_3203_;
}
else
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3274_; 
lean_dec(v_a_3264_);
v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3269_ = v___x_3266_;
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v___x_3266_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3272_; 
if (v_isShared_3270_ == 0)
{
v___x_3272_ = v___x_3269_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_a_3267_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
}
else
{
return v___x_3263_;
}
}
}
else
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3282_; 
v_a_3275_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3277_ = v___x_3255_;
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3255_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3280_; 
if (v_isShared_3278_ == 0)
{
v___x_3280_ = v___x_3277_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_a_3275_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
}
v___jp_3203_:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v___y_3205_, v___y_3206_, v___y_3214_);
if (lean_obj_tag(v___x_3216_) == 0)
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3246_; 
v_a_3217_ = lean_ctor_get(v___x_3216_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3219_ = v___x_3216_;
v_isShared_3220_ = v_isSharedCheck_3246_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3216_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3246_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v_toRingState_3221_; lean_object* v_denote_3222_; uint8_t v___x_3223_; 
v_toRingState_3221_ = lean_ctor_get(v_a_3217_, 0);
lean_inc_ref(v_toRingState_3221_);
lean_dec(v_a_3217_);
v_denote_3222_ = lean_ctor_get(v_toRingState_3221_, 2);
lean_inc_ref(v_denote_3222_);
lean_dec_ref(v_toRingState_3221_);
v___x_3223_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg(v_denote_3222_, v_one_3204_);
lean_dec_ref(v_denote_3222_);
if (v___x_3223_ == 0)
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
lean_del_object(v___x_3219_);
v___x_3224_ = lean_unsigned_to_nat(0u);
v___x_3225_ = lean_box(0);
lean_inc(v___y_3215_);
lean_inc_ref(v___y_3214_);
lean_inc(v___y_3213_);
lean_inc_ref(v___y_3212_);
lean_inc(v___y_3211_);
lean_inc_ref(v___y_3210_);
lean_inc(v___y_3209_);
lean_inc_ref(v___y_3208_);
lean_inc(v___y_3207_);
lean_inc(v___y_3206_);
lean_inc_ref(v_one_3204_);
v___x_3226_ = lean_grind_internalize(v_one_3204_, v___x_3224_, v___x_3225_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3233_ == 0)
{
lean_object* v_unused_3234_; 
v_unused_3234_ = lean_ctor_get(v___x_3226_, 0);
lean_dec(v_unused_3234_);
v___x_3228_ = v___x_3226_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_dec(v___x_3226_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v_one_3204_);
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_one_3204_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
else
{
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3242_; 
lean_dec_ref(v_one_3204_);
v_a_3235_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3237_ = v___x_3226_;
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3226_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3240_; 
if (v_isShared_3238_ == 0)
{
v___x_3240_ = v___x_3237_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3235_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
else
{
lean_object* v___x_3244_; 
if (v_isShared_3220_ == 0)
{
lean_ctor_set(v___x_3219_, 0, v_one_3204_);
v___x_3244_ = v___x_3219_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_one_3204_);
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
else
{
lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3254_; 
lean_dec_ref(v_one_3204_);
v_a_3247_ = lean_ctor_get(v___x_3216_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3249_ = v___x_3216_;
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_dec(v___x_3216_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3252_; 
if (v_isShared_3250_ == 0)
{
v___x_3252_ = v___x_3249_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_a_3247_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_getOne_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3191_ = stack[0].m_obj;
lean_object* v_a_3192_ = stack[1].m_obj;
lean_object* v_a_3193_ = stack[2].m_obj;
lean_object* v_a_3194_ = stack[3].m_obj;
lean_object* v_a_3195_ = stack[4].m_obj;
lean_object* v_a_3196_ = stack[5].m_obj;
lean_object* v_a_3197_ = stack[6].m_obj;
lean_object* v_a_3198_ = stack[7].m_obj;
lean_object* v_a_3199_ = stack[8].m_obj;
lean_object* v_a_3200_ = stack[9].m_obj;
lean_object* v_a_3201_ = stack[10].m_obj;
lean_object* v_res_3283_;
v_res_3283_ = l_Lean_Meta_Grind_Arith_CommRing_getOne(v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
stack->m_obj
 = v_res_3283_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___boxed(lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l_Lean_Meta_Grind_Arith_CommRing_getOne(v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_);
lean_dec(v_a_3294_);
lean_dec_ref(v_a_3293_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec(v_a_3285_);
lean_dec_ref(v_a_3284_);
return v_res_3296_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0(lean_object* v_00_u03b2_3297_, lean_object* v_x_3298_, lean_object* v_x_3299_){
_start:
{
uint8_t v___x_3300_; 
v___x_3300_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg(v_x_3298_, v_x_3299_);
return v___x_3300_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3298_ = stack[1].m_obj;
lean_object* v_x_3299_ = stack[2].m_obj;
uint8_t v_res_3301_;
v_res_3301_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0(lean_box(0), v_x_3298_, v_x_3299_);
stack->m_num = v_res_3301_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___boxed(lean_object* v_00_u03b2_3302_, lean_object* v_x_3303_, lean_object* v_x_3304_){
_start:
{
uint8_t v_res_3305_; lean_object* v_r_3306_; 
v_res_3305_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0(v_00_u03b2_3302_, v_x_3303_, v_x_3304_);
lean_dec_ref(v_x_3304_);
lean_dec_ref(v_x_3303_);
v_r_3306_ = lean_box(v_res_3305_);
return v_r_3306_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0(lean_object* v_00_u03b2_3307_, lean_object* v_x_3308_, size_t v_x_3309_, lean_object* v_x_3310_){
_start:
{
uint8_t v___x_3311_; 
v___x_3311_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg(v_x_3308_, v_x_3309_, v_x_3310_);
return v___x_3311_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3308_ = stack[1].m_obj;
size_t v_x_3309_ = stack[2].m_num;
lean_object* v_x_3310_ = stack[3].m_obj;
uint8_t v_res_3312_;
v_res_3312_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0(lean_box(0), v_x_3308_, v_x_3309_, v_x_3310_);
stack->m_num = v_res_3312_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3313_, lean_object* v_x_3314_, lean_object* v_x_3315_, lean_object* v_x_3316_){
_start:
{
size_t v_x_10012__boxed_3317_; uint8_t v_res_3318_; lean_object* v_r_3319_; 
v_x_10012__boxed_3317_ = lean_unbox_usize(v_x_3315_);
lean_dec(v_x_3315_);
v_res_3318_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0(v_00_u03b2_3313_, v_x_3314_, v_x_10012__boxed_3317_, v_x_3316_);
lean_dec_ref(v_x_3316_);
lean_dec_ref(v_x_3314_);
v_r_3319_ = lean_box(v_res_3318_);
return v_r_3319_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3320_, lean_object* v_keys_3321_, lean_object* v_vals_3322_, lean_object* v_heq_3323_, lean_object* v_i_3324_, lean_object* v_k_3325_){
_start:
{
uint8_t v___x_3326_; 
v___x_3326_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg(v_keys_3321_, v_i_3324_, v_k_3325_);
return v___x_3326_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_3321_ = stack[1].m_obj;
lean_object* v_vals_3322_ = stack[2].m_obj;
lean_object* v_i_3324_ = stack[4].m_obj;
lean_object* v_k_3325_ = stack[5].m_obj;
uint8_t v_res_3327_;
v_res_3327_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1(lean_box(0), v_keys_3321_, v_vals_3322_, lean_box(0), v_i_3324_, v_k_3325_);
stack->m_num = v_res_3327_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3328_, lean_object* v_keys_3329_, lean_object* v_vals_3330_, lean_object* v_heq_3331_, lean_object* v_i_3332_, lean_object* v_k_3333_){
_start:
{
uint8_t v_res_3334_; lean_object* v_r_3335_; 
v_res_3334_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1(v_00_u03b2_3328_, v_keys_3329_, v_vals_3330_, v_heq_3331_, v_i_3332_, v_k_3333_);
lean_dec_ref(v_k_3333_);
lean_dec_ref(v_vals_3330_);
lean_dec_ref(v_keys_3329_);
v_r_3335_ = lean_box(v_res_3334_);
return v_r_3335_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Functions(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_MonadVar(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Poly(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_Functions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_MonadVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_Poly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM = _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM);
l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM = _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM);
l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM = _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM);
l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM = _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Arith_Functions(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Arith_MonadVar(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Arith_Poly(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Arith_Functions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Arith_MonadVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Arith_Poly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
}
#ifdef __cplusplus
}
#endif
