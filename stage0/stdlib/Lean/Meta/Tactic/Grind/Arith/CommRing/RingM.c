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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_charOneInst_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_charOneInst_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_charOneInst_x3f(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(lean_object* v_a_1_, lean_object* v_a_2_, lean_object* v_a_3_){
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
v_ringSteps_12_ = lean_ctor_get(v_a_8_, 7);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg___boxed(lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(v_a_36_, v_a_37_, v_a_38_);
lean_dec_ref(v_a_38_);
lean_dec_ref(v_a_37_);
lean_dec(v_a_36_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps(lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(v_a_41_, v_a_43_, v_a_49_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___boxed(lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps(v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
lean_dec(v_a_58_);
lean_dec_ref(v_a_57_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
lean_dec(v_a_54_);
lean_dec(v_a_53_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0(uint8_t v___x_65_, lean_object* v_s_66_){
_start:
{
lean_object* v_rings_67_; lean_object* v_exprToRingId_68_; lean_object* v_semirings_69_; lean_object* v_exprToSemiringId_70_; lean_object* v_ncRings_71_; lean_object* v_exprToNCRingId_72_; lean_object* v_ncSemirings_73_; lean_object* v_exprToNCSemiringId_74_; lean_object* v_steps_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_82_; 
v_rings_67_ = lean_ctor_get(v_s_66_, 0);
v_exprToRingId_68_ = lean_ctor_get(v_s_66_, 1);
v_semirings_69_ = lean_ctor_get(v_s_66_, 2);
v_exprToSemiringId_70_ = lean_ctor_get(v_s_66_, 3);
v_ncRings_71_ = lean_ctor_get(v_s_66_, 4);
v_exprToNCRingId_72_ = lean_ctor_get(v_s_66_, 5);
v_ncSemirings_73_ = lean_ctor_get(v_s_66_, 6);
v_exprToNCSemiringId_74_ = lean_ctor_get(v_s_66_, 7);
v_steps_75_ = lean_ctor_get(v_s_66_, 8);
v_isSharedCheck_82_ = !lean_is_exclusive(v_s_66_);
if (v_isSharedCheck_82_ == 0)
{
v___x_77_ = v_s_66_;
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_steps_75_);
lean_inc(v_exprToNCSemiringId_74_);
lean_inc(v_ncSemirings_73_);
lean_inc(v_exprToNCRingId_72_);
lean_inc(v_ncRings_71_);
lean_inc(v_exprToSemiringId_70_);
lean_inc(v_semirings_69_);
lean_inc(v_exprToRingId_68_);
lean_inc(v_rings_67_);
lean_dec(v_s_66_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_80_; 
if (v_isShared_78_ == 0)
{
v___x_80_ = v___x_77_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_rings_67_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v_exprToRingId_68_);
lean_ctor_set(v_reuseFailAlloc_81_, 2, v_semirings_69_);
lean_ctor_set(v_reuseFailAlloc_81_, 3, v_exprToSemiringId_70_);
lean_ctor_set(v_reuseFailAlloc_81_, 4, v_ncRings_71_);
lean_ctor_set(v_reuseFailAlloc_81_, 5, v_exprToNCRingId_72_);
lean_ctor_set(v_reuseFailAlloc_81_, 6, v_ncSemirings_73_);
lean_ctor_set(v_reuseFailAlloc_81_, 7, v_exprToNCSemiringId_74_);
lean_ctor_set(v_reuseFailAlloc_81_, 8, v_steps_75_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*9, v___x_65_);
return v___x_80_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0___boxed(lean_object* v___x_83_, lean_object* v_s_84_){
_start:
{
uint8_t v___x_5932__boxed_85_; lean_object* v_res_86_; 
v___x_5932__boxed_85_ = lean_unbox(v___x_83_);
v_res_86_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0(v___x_5932__boxed_85_, v_s_84_);
return v_res_86_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__0));
v___x_89_ = l_Lean_stringToMessageData(v___x_88_);
return v___x_89_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__2));
v___x_92_ = l_Lean_stringToMessageData(v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__4));
v___x_95_ = l_Lean_stringToMessageData(v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg(lean_object* v_p_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_98_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_196_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_196_ == 0)
{
v___x_109_ = v___x_106_;
v_isShared_110_ = v_isSharedCheck_196_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_196_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v_ringMaxDegree_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v_ringMaxDegree_111_ = lean_ctor_get(v_a_107_, 8);
lean_inc(v_ringMaxDegree_111_);
lean_dec(v_a_107_);
v___x_112_ = l_Lean_Grind_CommRing_Poly_degree(v_p_96_);
v___x_113_ = lean_nat_dec_le(v_ringMaxDegree_111_, v___x_112_);
lean_dec(v_ringMaxDegree_111_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; lean_object* v___x_116_; 
lean_dec(v___x_112_);
v___x_114_ = lean_box(v___x_113_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v___x_114_);
v___x_116_ = v___x_109_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
else
{
lean_object* v___x_118_; lean_object* v___f_119_; lean_object* v___x_120_; 
lean_del_object(v___x_109_);
v___x_118_ = lean_box(v___x_113_);
v___f_119_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_119_, 0, v___x_118_);
v___x_120_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_97_, v_a_103_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_187_; 
v_a_121_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_187_ == 0)
{
v___x_123_ = v___x_120_;
v_isShared_124_ = v_isSharedCheck_187_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_120_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_187_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
uint8_t v_reportedMaxDegreeIssue_125_; 
v_reportedMaxDegreeIssue_125_ = lean_ctor_get_uint8(v_a_121_, sizeof(void*)*9);
lean_dec(v_a_121_);
if (v_reportedMaxDegreeIssue_125_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; 
lean_del_object(v___x_123_);
v___x_126_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_127_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_126_, v___f_119_, v_a_97_);
if (lean_obj_tag(v___x_127_) == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
lean_dec_ref_known(v___x_127_, 1);
v___x_128_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1);
v___x_129_ = l_Nat_reprFast(v___x_112_);
v___x_130_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
v___x_131_ = l_Lean_MessageData_ofFormat(v___x_130_);
lean_inc_ref(v___x_131_);
v___x_132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_128_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
v___x_133_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3, &l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3);
v___x_134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_132_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
v___x_135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v___x_131_);
v___x_136_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5, &l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5);
v___x_137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_135_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v___x_138_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_99_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_166_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_166_ == 0)
{
v___x_141_ = v___x_138_;
v_isShared_142_ = v_isSharedCheck_166_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_138_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_166_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
uint8_t v_verbose_143_; 
v_verbose_143_ = lean_ctor_get_uint8(v_a_139_, 0);
lean_dec(v_a_139_);
if (v_verbose_143_ == 0)
{
lean_object* v___x_144_; lean_object* v___x_146_; 
lean_dec_ref_known(v___x_137_, 2);
v___x_144_ = lean_box(v___x_113_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v___x_144_);
v___x_146_ = v___x_141_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_144_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
else
{
lean_object* v___x_148_; 
lean_del_object(v___x_141_);
v___x_148_ = l_Lean_Meta_Sym_reportIssue(v___x_137_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_156_; 
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_156_ == 0)
{
lean_object* v_unused_157_; 
v_unused_157_ = lean_ctor_get(v___x_148_, 0);
lean_dec(v_unused_157_);
v___x_150_ = v___x_148_;
v_isShared_151_ = v_isSharedCheck_156_;
goto v_resetjp_149_;
}
else
{
lean_dec(v___x_148_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_156_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_152_; lean_object* v___x_154_; 
v___x_152_ = lean_box(v___x_113_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 0, v___x_152_);
v___x_154_ = v___x_150_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_152_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
else
{
lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_165_; 
v_a_158_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_165_ == 0)
{
v___x_160_ = v___x_148_;
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_a_158_);
lean_dec(v___x_148_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_163_; 
if (v_isShared_161_ == 0)
{
v___x_163_ = v___x_160_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_a_158_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
}
}
}
else
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_174_; 
lean_dec_ref_known(v___x_137_, 2);
v_a_167_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_174_ == 0)
{
v___x_169_ = v___x_138_;
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_138_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_a_167_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
else
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_182_; 
lean_dec(v___x_112_);
v_a_175_ = lean_ctor_get(v___x_127_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_127_);
if (v_isSharedCheck_182_ == 0)
{
v___x_177_ = v___x_127_;
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_127_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_180_; 
if (v_isShared_178_ == 0)
{
v___x_180_ = v___x_177_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_a_175_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
else
{
lean_object* v___x_183_; lean_object* v___x_185_; 
lean_dec_ref(v___f_119_);
lean_dec(v___x_112_);
v___x_183_ = lean_box(v___x_113_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 0, v___x_183_);
v___x_185_ = v___x_123_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_183_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
else
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_195_; 
lean_dec_ref(v___f_119_);
lean_dec(v___x_112_);
v_a_188_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_195_ == 0)
{
v___x_190_ = v___x_120_;
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_120_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_a_188_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
}
}
else
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
v_a_197_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_106_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_106_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___boxed(lean_object* v_p_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg(v_p_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_212_);
lean_dec(v_a_211_);
lean_dec_ref(v_a_210_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_p_205_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree(lean_object* v_p_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg(v_p_216_, v_a_217_, v_a_219_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___boxed(lean_object* v_p_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree(v_p_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_);
lean_dec(v_a_239_);
lean_dec_ref(v_a_238_);
lean_dec(v_a_237_);
lean_dec_ref(v_a_236_);
lean_dec(v_a_235_);
lean_dec_ref(v_a_234_);
lean_dec(v_a_233_);
lean_dec_ref(v_a_232_);
lean_dec(v_a_231_);
lean_dec(v_a_230_);
lean_dec_ref(v_p_229_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0(lean_object* v_n_242_, lean_object* v_s_243_){
_start:
{
lean_object* v_rings_244_; lean_object* v_exprToRingId_245_; lean_object* v_semirings_246_; lean_object* v_exprToSemiringId_247_; lean_object* v_ncRings_248_; lean_object* v_exprToNCRingId_249_; lean_object* v_ncSemirings_250_; lean_object* v_exprToNCSemiringId_251_; lean_object* v_steps_252_; uint8_t v_reportedMaxDegreeIssue_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_261_; 
v_rings_244_ = lean_ctor_get(v_s_243_, 0);
v_exprToRingId_245_ = lean_ctor_get(v_s_243_, 1);
v_semirings_246_ = lean_ctor_get(v_s_243_, 2);
v_exprToSemiringId_247_ = lean_ctor_get(v_s_243_, 3);
v_ncRings_248_ = lean_ctor_get(v_s_243_, 4);
v_exprToNCRingId_249_ = lean_ctor_get(v_s_243_, 5);
v_ncSemirings_250_ = lean_ctor_get(v_s_243_, 6);
v_exprToNCSemiringId_251_ = lean_ctor_get(v_s_243_, 7);
v_steps_252_ = lean_ctor_get(v_s_243_, 8);
v_reportedMaxDegreeIssue_253_ = lean_ctor_get_uint8(v_s_243_, sizeof(void*)*9);
v_isSharedCheck_261_ = !lean_is_exclusive(v_s_243_);
if (v_isSharedCheck_261_ == 0)
{
v___x_255_ = v_s_243_;
v_isShared_256_ = v_isSharedCheck_261_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_steps_252_);
lean_inc(v_exprToNCSemiringId_251_);
lean_inc(v_ncSemirings_250_);
lean_inc(v_exprToNCRingId_249_);
lean_inc(v_ncRings_248_);
lean_inc(v_exprToSemiringId_247_);
lean_inc(v_semirings_246_);
lean_inc(v_exprToRingId_245_);
lean_inc(v_rings_244_);
lean_dec(v_s_243_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_261_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_257_ = lean_nat_add(v_steps_252_, v_n_242_);
lean_dec(v_steps_252_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 8, v___x_257_);
v___x_259_ = v___x_255_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_rings_244_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_exprToRingId_245_);
lean_ctor_set(v_reuseFailAlloc_260_, 2, v_semirings_246_);
lean_ctor_set(v_reuseFailAlloc_260_, 3, v_exprToSemiringId_247_);
lean_ctor_set(v_reuseFailAlloc_260_, 4, v_ncRings_248_);
lean_ctor_set(v_reuseFailAlloc_260_, 5, v_exprToNCRingId_249_);
lean_ctor_set(v_reuseFailAlloc_260_, 6, v_ncSemirings_250_);
lean_ctor_set(v_reuseFailAlloc_260_, 7, v_exprToNCSemiringId_251_);
lean_ctor_set(v_reuseFailAlloc_260_, 8, v___x_257_);
lean_ctor_set_uint8(v_reuseFailAlloc_260_, sizeof(void*)*9, v_reportedMaxDegreeIssue_253_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0___boxed(lean_object* v_n_262_, lean_object* v_s_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0(v_n_262_, v_s_263_);
lean_dec(v_n_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(lean_object* v_n_265_, lean_object* v_a_266_){
_start:
{
lean_object* v___f_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___f_268_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_268_, 0, v_n_265_);
v___x_269_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_270_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_269_, v___f_268_, v_a_266_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___boxed(lean_object* v_n_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v_n_271_, v_a_272_);
lean_dec(v_a_272_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps(lean_object* v_n_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v_n_275_, v_a_276_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___boxed(lean_object* v_n_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps(v_n_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
lean_dec(v_a_290_);
lean_dec(v_a_289_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg(lean_object* v_ringId_301_, lean_object* v_x_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
uint8_t v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_314_ = 0;
v___x_315_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_315_, 0, v_ringId_301_);
lean_ctor_set_uint8(v___x_315_, sizeof(void*)*1, v___x_314_);
lean_inc(v_a_312_);
lean_inc_ref(v_a_311_);
lean_inc(v_a_310_);
lean_inc_ref(v_a_309_);
lean_inc(v_a_308_);
lean_inc_ref(v_a_307_);
lean_inc(v_a_306_);
lean_inc_ref(v_a_305_);
lean_inc(v_a_304_);
lean_inc(v_a_303_);
v___x_316_ = lean_apply_12(v_x_302_, v___x_315_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, lean_box(0));
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg___boxed(lean_object* v_ringId_317_, lean_object* v_x_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg(v_ringId_317_, v_x_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
lean_dec(v_a_320_);
lean_dec(v_a_319_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run(lean_object* v_00_u03b1_331_, lean_object* v_ringId_332_, lean_object* v_x_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
uint8_t v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_345_ = 0;
v___x_346_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_346_, 0, v_ringId_332_);
lean_ctor_set_uint8(v___x_346_, sizeof(void*)*1, v___x_345_);
lean_inc(v_a_343_);
lean_inc_ref(v_a_342_);
lean_inc(v_a_341_);
lean_inc_ref(v_a_340_);
lean_inc(v_a_339_);
lean_inc_ref(v_a_338_);
lean_inc(v_a_337_);
lean_inc_ref(v_a_336_);
lean_inc(v_a_335_);
lean_inc(v_a_334_);
v___x_347_ = lean_apply_12(v_x_333_, v___x_346_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, lean_box(0));
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___boxed(lean_object* v_00_u03b1_348_, lean_object* v_ringId_349_, lean_object* v_x_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_run(v_00_u03b1_348_, v_ringId_349_, v_x_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_354_);
lean_dec_ref(v_a_353_);
lean_dec(v_a_352_);
lean_dec(v_a_351_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg(lean_object* v_a_363_){
_start:
{
lean_object* v_ringId_365_; lean_object* v___x_366_; 
v_ringId_365_ = lean_ctor_get(v_a_363_, 0);
lean_inc(v_ringId_365_);
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v_ringId_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg___boxed(lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg(v_a_367_);
lean_dec_ref(v_a_367_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId(lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_ringId_382_; lean_object* v___x_383_; 
v_ringId_382_ = lean_ctor_get(v_a_370_, 0);
lean_inc(v_ringId_382_);
v___x_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_383_, 0, v_ringId_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___boxed(lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Meta_Grind_Arith_CommRing_getRingId(v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0(lean_object* v_e_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_Meta_Sym_canon(v_e_397_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; lean_object* v___x_412_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_a_411_);
lean_dec_ref_known(v___x_410_, 1);
v___x_412_ = l_Lean_Meta_Sym_shareCommon(v_a_411_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
return v___x_412_;
}
else
{
return v___x_410_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0___boxed(lean_object* v_e_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0(v_e_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1(lean_object* v_e_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_e_427_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1___boxed(lean_object* v_e_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1(v_e_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(lean_object* v_msgData_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v___x_467_; lean_object* v_env_468_; uint8_t v___x_469_; lean_object* v_env_470_; lean_object* v___x_471_; lean_object* v_toCold_472_; lean_object* v_mctx_473_; lean_object* v_lctx_474_; lean_object* v_options_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_467_ = lean_st_ref_get(v___y_465_);
v_env_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc_ref(v_env_468_);
lean_dec(v___x_467_);
v___x_469_ = 0;
v_env_470_ = l_Lean_Environment_setRecordingDeps(v_env_468_, v___x_469_);
v___x_471_ = lean_st_ref_get(v___y_463_);
v_toCold_472_ = lean_ctor_get(v___y_464_, 0);
v_mctx_473_ = lean_ctor_get(v___x_471_, 0);
lean_inc_ref(v_mctx_473_);
lean_dec(v___x_471_);
v_lctx_474_ = lean_ctor_get(v___y_462_, 2);
v_options_475_ = lean_ctor_get(v_toCold_472_, 2);
lean_inc_ref(v_options_475_);
lean_inc_ref(v_lctx_474_);
v___x_476_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_476_, 0, v_env_470_);
lean_ctor_set(v___x_476_, 1, v_mctx_473_);
lean_ctor_set(v___x_476_, 2, v_lctx_474_);
lean_ctor_set(v___x_476_, 3, v_options_475_);
v___x_477_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v_msgData_461_);
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0___boxed(lean_object* v_msgData_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(v_msgData_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(lean_object* v_msg_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v_ref_492_; lean_object* v___x_493_; lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_502_; 
v_ref_492_ = lean_ctor_get(v___y_489_, 2);
v___x_493_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(v_msg_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
v_a_494_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_502_ == 0)
{
v___x_496_ = v___x_493_;
v_isShared_497_ = v_isSharedCheck_502_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_493_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_502_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_500_; 
lean_inc(v_ref_492_);
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v_ref_492_);
lean_ctor_set(v___x_498_, 1, v_a_494_);
if (v_isShared_497_ == 0)
{
lean_ctor_set_tag(v___x_496_, 1);
lean_ctor_set(v___x_496_, 0, v___x_498_);
v___x_500_ = v___x_496_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_498_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg___boxed(lean_object* v_msg_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v_msg_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
return v_res_509_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__0));
v___x_512_ = l_Lean_stringToMessageData(v___x_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_519_, v_a_522_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_540_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_540_ == 0)
{
v___x_528_ = v___x_525_;
v_isShared_529_ = v_isSharedCheck_540_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_540_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v_ringId_530_; lean_object* v_rings_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v_ringId_530_ = lean_ctor_get(v_a_513_, 0);
v_rings_531_ = lean_ctor_get(v_a_526_, 1);
lean_inc_ref(v_rings_531_);
lean_dec(v_a_526_);
v___x_532_ = lean_array_get_size(v_rings_531_);
v___x_533_ = lean_nat_dec_lt(v_ringId_530_, v___x_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; lean_object* v___x_535_; 
lean_dec_ref(v_rings_531_);
lean_del_object(v___x_528_);
v___x_534_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1);
v___x_535_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v___x_534_, v_a_520_, v_a_521_, v_a_522_, v_a_523_);
return v___x_535_;
}
else
{
lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_536_ = lean_array_fget(v_rings_531_, v_ringId_530_);
lean_dec_ref(v_rings_531_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_536_);
v___x_538_ = v___x_528_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
v_a_541_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_525_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_525_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___boxed(lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
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
lean_dec_ref(v_a_549_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0(lean_object* v_00_u03b1_562_, lean_object* v_msg_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v_msg_563_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___boxed(lean_object* v_00_u03b1_577_, lean_object* v_msg_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0(v_00_u03b1_577_, v_msg_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0(lean_object* v_ringId_592_, lean_object* v_f_593_, lean_object* v_s_594_){
_start:
{
lean_object* v_exp_595_; lean_object* v_rings_596_; lean_object* v_semirings_597_; lean_object* v_ncRings_598_; lean_object* v_ncSemirings_599_; lean_object* v_typeClassify_600_; lean_object* v_orders_601_; lean_object* v_typeOrderClassify_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v_exp_595_ = lean_ctor_get(v_s_594_, 0);
v_rings_596_ = lean_ctor_get(v_s_594_, 1);
v_semirings_597_ = lean_ctor_get(v_s_594_, 2);
v_ncRings_598_ = lean_ctor_get(v_s_594_, 3);
v_ncSemirings_599_ = lean_ctor_get(v_s_594_, 4);
v_typeClassify_600_ = lean_ctor_get(v_s_594_, 5);
v_orders_601_ = lean_ctor_get(v_s_594_, 6);
v_typeOrderClassify_602_ = lean_ctor_get(v_s_594_, 7);
v___x_603_ = lean_array_get_size(v_rings_596_);
v___x_604_ = lean_nat_dec_lt(v_ringId_592_, v___x_603_);
if (v___x_604_ == 0)
{
lean_dec_ref(v_f_593_);
return v_s_594_;
}
else
{
lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_616_; 
lean_inc_ref(v_typeOrderClassify_602_);
lean_inc_ref(v_orders_601_);
lean_inc_ref(v_typeClassify_600_);
lean_inc_ref(v_ncSemirings_599_);
lean_inc_ref(v_ncRings_598_);
lean_inc_ref(v_semirings_597_);
lean_inc_ref(v_rings_596_);
lean_inc(v_exp_595_);
v_isSharedCheck_616_ = !lean_is_exclusive(v_s_594_);
if (v_isSharedCheck_616_ == 0)
{
lean_object* v_unused_617_; lean_object* v_unused_618_; lean_object* v_unused_619_; lean_object* v_unused_620_; lean_object* v_unused_621_; lean_object* v_unused_622_; lean_object* v_unused_623_; lean_object* v_unused_624_; 
v_unused_617_ = lean_ctor_get(v_s_594_, 7);
lean_dec(v_unused_617_);
v_unused_618_ = lean_ctor_get(v_s_594_, 6);
lean_dec(v_unused_618_);
v_unused_619_ = lean_ctor_get(v_s_594_, 5);
lean_dec(v_unused_619_);
v_unused_620_ = lean_ctor_get(v_s_594_, 4);
lean_dec(v_unused_620_);
v_unused_621_ = lean_ctor_get(v_s_594_, 3);
lean_dec(v_unused_621_);
v_unused_622_ = lean_ctor_get(v_s_594_, 2);
lean_dec(v_unused_622_);
v_unused_623_ = lean_ctor_get(v_s_594_, 1);
lean_dec(v_unused_623_);
v_unused_624_ = lean_ctor_get(v_s_594_, 0);
lean_dec(v_unused_624_);
v___x_606_ = v_s_594_;
v_isShared_607_ = v_isSharedCheck_616_;
goto v_resetjp_605_;
}
else
{
lean_dec(v_s_594_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_616_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v_v_608_; lean_object* v___x_609_; lean_object* v_xs_x27_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_614_; 
v_v_608_ = lean_array_fget(v_rings_596_, v_ringId_592_);
v___x_609_ = lean_box(0);
v_xs_x27_610_ = lean_array_fset(v_rings_596_, v_ringId_592_, v___x_609_);
v___x_611_ = lean_apply_1(v_f_593_, v_v_608_);
v___x_612_ = lean_array_fset(v_xs_x27_610_, v_ringId_592_, v___x_611_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 1, v___x_612_);
v___x_614_ = v___x_606_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_exp_595_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v_semirings_597_);
lean_ctor_set(v_reuseFailAlloc_615_, 3, v_ncRings_598_);
lean_ctor_set(v_reuseFailAlloc_615_, 4, v_ncSemirings_599_);
lean_ctor_set(v_reuseFailAlloc_615_, 5, v_typeClassify_600_);
lean_ctor_set(v_reuseFailAlloc_615_, 6, v_orders_601_);
lean_ctor_set(v_reuseFailAlloc_615_, 7, v_typeOrderClassify_602_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0___boxed(lean_object* v_ringId_625_, lean_object* v_f_626_, lean_object* v_s_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0(v_ringId_625_, v_f_626_, v_s_627_);
lean_dec(v_ringId_625_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(lean_object* v_f_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
lean_object* v_ringId_633_; lean_object* v___f_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v_ringId_633_ = lean_ctor_get(v_a_630_, 0);
lean_inc(v_ringId_633_);
v___f_634_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_634_, 0, v_ringId_633_);
lean_closure_set(v___f_634_, 1, v_f_629_);
v___x_635_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_636_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_635_, v___f_634_, v_a_631_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___boxed(lean_object* v_f_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v_f_637_, v_a_638_, v_a_639_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing(lean_object* v_f_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v_f_642_, v_a_643_, v_a_649_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___boxed(lean_object* v_f_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing(v_f_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
lean_dec(v_a_659_);
lean_dec(v_a_658_);
lean_dec_ref(v_a_657_);
return v_res_669_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_671_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__0));
v___x_672_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___boxed), 12, 0);
v___x_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
lean_ctor_set(v___x_673_, 1, v___x_671_);
return v___x_673_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM(void){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_676_, v_a_677_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_689_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_689_ == 0)
{
v___x_682_ = v___x_679_;
v_isShared_683_ = v_isSharedCheck_689_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_679_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_689_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v_ringId_684_; lean_object* v___x_685_; lean_object* v___x_687_; 
v_ringId_684_ = lean_ctor_get(v_a_675_, 0);
v___x_685_ = l_Lean_Meta_Grind_Arith_CommRing_State_getRing(v_a_680_, v_ringId_684_);
lean_dec(v_a_680_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 0, v___x_685_);
v___x_687_ = v___x_682_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
v_a_690_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_679_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_679_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg___boxed(lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_698_, v_a_699_, v_a_700_);
lean_dec_ref(v_a_700_);
lean_dec(v_a_699_);
lean_dec_ref(v_a_698_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState(lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_703_, v_a_704_, v_a_712_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___boxed(lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState(v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
lean_dec(v_a_726_);
lean_dec_ref(v_a_725_);
lean_dec(v_a_724_);
lean_dec_ref(v_a_723_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
lean_dec(v_a_718_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg___lam__0(lean_object* v_ringId_729_, lean_object* v_f_730_, lean_object* v_s_731_){
_start:
{
lean_object* v_rings_732_; lean_object* v_exprToRingId_733_; lean_object* v_semirings_734_; lean_object* v_exprToSemiringId_735_; lean_object* v_ncRings_736_; lean_object* v_exprToNCRingId_737_; lean_object* v_ncSemirings_738_; lean_object* v_exprToNCSemiringId_739_; lean_object* v_steps_740_; uint8_t v_reportedMaxDegreeIssue_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_762_; 
v_rings_732_ = lean_ctor_get(v_s_731_, 0);
v_exprToRingId_733_ = lean_ctor_get(v_s_731_, 1);
v_semirings_734_ = lean_ctor_get(v_s_731_, 2);
v_exprToSemiringId_735_ = lean_ctor_get(v_s_731_, 3);
v_ncRings_736_ = lean_ctor_get(v_s_731_, 4);
v_exprToNCRingId_737_ = lean_ctor_get(v_s_731_, 5);
v_ncSemirings_738_ = lean_ctor_get(v_s_731_, 6);
v_exprToNCSemiringId_739_ = lean_ctor_get(v_s_731_, 7);
v_steps_740_ = lean_ctor_get(v_s_731_, 8);
v_reportedMaxDegreeIssue_741_ = lean_ctor_get_uint8(v_s_731_, sizeof(void*)*9);
v_isSharedCheck_762_ = !lean_is_exclusive(v_s_731_);
if (v_isSharedCheck_762_ == 0)
{
v___x_743_ = v_s_731_;
v_isShared_744_ = v_isSharedCheck_762_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_steps_740_);
lean_inc(v_exprToNCSemiringId_739_);
lean_inc(v_ncSemirings_738_);
lean_inc(v_exprToNCRingId_737_);
lean_inc(v_ncRings_736_);
lean_inc(v_exprToSemiringId_735_);
lean_inc(v_semirings_734_);
lean_inc(v_exprToRingId_733_);
lean_inc(v_rings_732_);
lean_dec(v_s_731_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_762_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_745_ = lean_unsigned_to_nat(1u);
v___x_746_ = lean_nat_add(v_ringId_729_, v___x_745_);
v___x_747_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default;
v___x_748_ = l_Array_rightpad___redArg(v___x_746_, v___x_747_, v_rings_732_);
lean_dec(v___x_746_);
v___x_749_ = lean_array_get_size(v___x_748_);
v___x_750_ = lean_nat_dec_lt(v_ringId_729_, v___x_749_);
if (v___x_750_ == 0)
{
lean_object* v___x_752_; 
lean_dec_ref(v_f_730_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_748_);
v___x_752_ = v___x_743_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_exprToRingId_733_);
lean_ctor_set(v_reuseFailAlloc_753_, 2, v_semirings_734_);
lean_ctor_set(v_reuseFailAlloc_753_, 3, v_exprToSemiringId_735_);
lean_ctor_set(v_reuseFailAlloc_753_, 4, v_ncRings_736_);
lean_ctor_set(v_reuseFailAlloc_753_, 5, v_exprToNCRingId_737_);
lean_ctor_set(v_reuseFailAlloc_753_, 6, v_ncSemirings_738_);
lean_ctor_set(v_reuseFailAlloc_753_, 7, v_exprToNCSemiringId_739_);
lean_ctor_set(v_reuseFailAlloc_753_, 8, v_steps_740_);
lean_ctor_set_uint8(v_reuseFailAlloc_753_, sizeof(void*)*9, v_reportedMaxDegreeIssue_741_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
else
{
lean_object* v_v_754_; lean_object* v___x_755_; lean_object* v_xs_x27_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_760_; 
v_v_754_ = lean_array_fget(v___x_748_, v_ringId_729_);
v___x_755_ = lean_box(0);
v_xs_x27_756_ = lean_array_fset(v___x_748_, v_ringId_729_, v___x_755_);
v___x_757_ = lean_apply_1(v_f_730_, v_v_754_);
v___x_758_ = lean_array_fset(v_xs_x27_756_, v_ringId_729_, v___x_757_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_758_);
v___x_760_ = v___x_743_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_exprToRingId_733_);
lean_ctor_set(v_reuseFailAlloc_761_, 2, v_semirings_734_);
lean_ctor_set(v_reuseFailAlloc_761_, 3, v_exprToSemiringId_735_);
lean_ctor_set(v_reuseFailAlloc_761_, 4, v_ncRings_736_);
lean_ctor_set(v_reuseFailAlloc_761_, 5, v_exprToNCRingId_737_);
lean_ctor_set(v_reuseFailAlloc_761_, 6, v_ncSemirings_738_);
lean_ctor_set(v_reuseFailAlloc_761_, 7, v_exprToNCSemiringId_739_);
lean_ctor_set(v_reuseFailAlloc_761_, 8, v_steps_740_);
lean_ctor_set_uint8(v_reuseFailAlloc_761_, sizeof(void*)*9, v_reportedMaxDegreeIssue_741_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg___lam__0___boxed(lean_object* v_ringId_763_, lean_object* v_f_764_, lean_object* v_s_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg___lam__0(v_ringId_763_, v_f_764_, v_s_765_);
lean_dec(v_ringId_763_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(lean_object* v_f_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_ringId_771_; lean_object* v___f_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v_ringId_771_ = lean_ctor_get(v_a_768_, 0);
lean_inc(v_ringId_771_);
v___f_772_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_772_, 0, v_ringId_771_);
lean_closure_set(v___f_772_, 1, v_f_767_);
v___x_773_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_774_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_773_, v___f_772_, v_a_769_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg___boxed(lean_object* v_f_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(v_f_775_, v_a_776_, v_a_777_);
lean_dec(v_a_777_);
lean_dec_ref(v_a_776_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState(lean_object* v_f_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(v_f_780_, v_a_781_, v_a_782_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___boxed(lean_object* v_f_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState(v_f_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec(v_a_797_);
lean_dec(v_a_796_);
lean_dec_ref(v_a_795_);
return v_res_807_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__1(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_809_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__0));
v___x_810_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___boxed), 12, 0);
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
lean_ctor_set(v___x_811_, 1, v___x_809_);
return v___x_811_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM(void){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__1);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___lam__0(lean_object* v___x_813_, lean_object* v_x_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v___y_815_, v___y_816_, v___y_824_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_844_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_844_ == 0)
{
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_844_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_844_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v_toRingState_832_; lean_object* v_vars_833_; lean_object* v_size_834_; uint8_t v___x_835_; 
v_toRingState_832_ = lean_ctor_get(v_a_828_, 0);
lean_inc_ref(v_toRingState_832_);
lean_dec(v_a_828_);
v_vars_833_ = lean_ctor_get(v_toRingState_832_, 0);
lean_inc_ref(v_vars_833_);
lean_dec_ref(v_toRingState_832_);
v_size_834_ = lean_ctor_get(v_vars_833_, 2);
v___x_835_ = lean_nat_dec_lt(v_x_814_, v_size_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; lean_object* v___x_838_; 
lean_dec_ref(v_vars_833_);
v___x_836_ = l_outOfBounds___redArg(v___x_813_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_836_);
v___x_838_ = v___x_830_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_836_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
else
{
lean_object* v___x_840_; lean_object* v___x_842_; 
v___x_840_ = l_Lean_PersistentArray_get_x21___redArg(v___x_813_, v_vars_833_, v_x_814_);
lean_dec_ref(v_vars_833_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_840_);
v___x_842_ = v___x_830_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_840_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
v_a_845_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_827_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_827_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___lam__0___boxed(lean_object* v___x_853_, lean_object* v_x_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___lam__0(v___x_853_, v_x_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v_x_854_);
lean_dec_ref(v___x_853_);
return v_res_867_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___closed__0(void){
_start:
{
lean_object* v___x_868_; lean_object* v___f_869_; 
v___x_868_ = l_Lean_instInhabitedExpr;
v___f_869_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___lam__0___boxed), 14, 1);
lean_closure_set(v___f_869_, 0, v___x_868_);
return v___f_869_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM(void){
_start:
{
lean_object* v___f_870_; 
v___f_870_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___closed__0);
return v___f_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg(lean_object* v_x_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
lean_object* v_ringId_884_; uint8_t v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v_ringId_884_ = lean_ctor_get(v_a_872_, 0);
v___x_885_ = 1;
lean_inc(v_ringId_884_);
v___x_886_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_886_, 0, v_ringId_884_);
lean_ctor_set_uint8(v___x_886_, sizeof(void*)*1, v___x_885_);
lean_inc(v_a_882_);
lean_inc_ref(v_a_881_);
lean_inc(v_a_880_);
lean_inc_ref(v_a_879_);
lean_inc(v_a_878_);
lean_inc_ref(v_a_877_);
lean_inc(v_a_876_);
lean_inc_ref(v_a_875_);
lean_inc(v_a_874_);
lean_inc(v_a_873_);
v___x_887_ = lean_apply_12(v_x_871_, v___x_886_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, lean_box(0));
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg___boxed(lean_object* v_x_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg(v_x_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd(lean_object* v_00_u03b1_902_, lean_object* v_x_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
lean_object* v_ringId_916_; uint8_t v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v_ringId_916_ = lean_ctor_get(v_a_904_, 0);
v___x_917_ = 1;
lean_inc(v_ringId_916_);
v___x_918_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_918_, 0, v_ringId_916_);
lean_ctor_set_uint8(v___x_918_, sizeof(void*)*1, v___x_917_);
lean_inc(v_a_914_);
lean_inc_ref(v_a_913_);
lean_inc(v_a_912_);
lean_inc_ref(v_a_911_);
lean_inc(v_a_910_);
lean_inc_ref(v_a_909_);
lean_inc(v_a_908_);
lean_inc_ref(v_a_907_);
lean_inc(v_a_906_);
lean_inc(v_a_905_);
v___x_919_ = lean_apply_12(v_x_903_, v___x_918_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, lean_box(0));
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___boxed(lean_object* v_00_u03b1_920_, lean_object* v_x_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd(v_00_u03b1_920_, v_x_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_);
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
lean_dec_ref(v_a_922_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(lean_object* v_a_935_){
_start:
{
uint8_t v_checkCoeffDvd_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v_checkCoeffDvd_937_ = lean_ctor_get_uint8(v_a_935_, sizeof(void*)*1);
v___x_938_ = lean_box(v_checkCoeffDvd_937_);
v___x_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg___boxed(lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(v_a_940_);
lean_dec_ref(v_a_940_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd(lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(v_a_943_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___boxed(lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd(v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_969_, lean_object* v_vals_970_, lean_object* v_i_971_, lean_object* v_k_972_){
_start:
{
lean_object* v___x_973_; uint8_t v___x_974_; 
v___x_973_ = lean_array_get_size(v_keys_969_);
v___x_974_ = lean_nat_dec_lt(v_i_971_, v___x_973_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; 
lean_dec(v_i_971_);
v___x_975_ = lean_box(0);
return v___x_975_;
}
else
{
lean_object* v_k_x27_976_; size_t v___x_977_; size_t v___x_978_; uint8_t v___x_979_; 
v_k_x27_976_ = lean_array_fget_borrowed(v_keys_969_, v_i_971_);
v___x_977_ = lean_ptr_addr(v_k_972_);
v___x_978_ = lean_ptr_addr(v_k_x27_976_);
v___x_979_ = lean_usize_dec_eq(v___x_977_, v___x_978_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = lean_unsigned_to_nat(1u);
v___x_981_ = lean_nat_add(v_i_971_, v___x_980_);
lean_dec(v_i_971_);
v_i_971_ = v___x_981_;
goto _start;
}
else
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = lean_array_fget_borrowed(v_vals_970_, v_i_971_);
lean_dec(v_i_971_);
lean_inc(v___x_983_);
v___x_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
return v___x_984_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_985_, lean_object* v_vals_986_, lean_object* v_i_987_, lean_object* v_k_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_985_, v_vals_986_, v_i_987_, v_k_988_);
lean_dec_ref(v_k_988_);
lean_dec_ref(v_vals_986_);
lean_dec_ref(v_keys_985_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(lean_object* v_x_990_, size_t v_x_991_, lean_object* v_x_992_){
_start:
{
if (lean_obj_tag(v_x_990_) == 0)
{
lean_object* v_es_993_; lean_object* v___x_994_; size_t v___x_995_; size_t v___x_996_; lean_object* v_j_997_; lean_object* v___x_998_; 
v_es_993_ = lean_ctor_get(v_x_990_, 0);
v___x_994_ = lean_box(2);
v___x_995_ = ((size_t)31ULL);
v___x_996_ = lean_usize_land(v_x_991_, v___x_995_);
v_j_997_ = lean_usize_to_nat(v___x_996_);
v___x_998_ = lean_array_get_borrowed(v___x_994_, v_es_993_, v_j_997_);
lean_dec(v_j_997_);
switch(lean_obj_tag(v___x_998_))
{
case 0:
{
lean_object* v_key_999_; lean_object* v_val_1000_; size_t v___x_1001_; size_t v___x_1002_; uint8_t v___x_1003_; 
v_key_999_ = lean_ctor_get(v___x_998_, 0);
v_val_1000_ = lean_ctor_get(v___x_998_, 1);
v___x_1001_ = lean_ptr_addr(v_x_992_);
v___x_1002_ = lean_ptr_addr(v_key_999_);
v___x_1003_ = lean_usize_dec_eq(v___x_1001_, v___x_1002_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; 
v___x_1004_ = lean_box(0);
return v___x_1004_;
}
else
{
lean_object* v___x_1005_; 
lean_inc(v_val_1000_);
v___x_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1005_, 0, v_val_1000_);
return v___x_1005_;
}
}
case 1:
{
lean_object* v_node_1006_; size_t v___x_1007_; size_t v___x_1008_; 
v_node_1006_ = lean_ctor_get(v___x_998_, 0);
v___x_1007_ = ((size_t)5ULL);
v___x_1008_ = lean_usize_shift_right(v_x_991_, v___x_1007_);
v_x_990_ = v_node_1006_;
v_x_991_ = v___x_1008_;
goto _start;
}
default: 
{
lean_object* v___x_1010_; 
v___x_1010_ = lean_box(0);
return v___x_1010_;
}
}
}
else
{
lean_object* v_ks_1011_; lean_object* v_vs_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v_ks_1011_ = lean_ctor_get(v_x_990_, 0);
v_vs_1012_ = lean_ctor_get(v_x_990_, 1);
v___x_1013_ = lean_unsigned_to_nat(0u);
v___x_1014_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1011_, v_vs_1012_, v___x_1013_, v_x_992_);
return v___x_1014_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1015_, lean_object* v_x_1016_, lean_object* v_x_1017_){
_start:
{
size_t v_x_905__boxed_1018_; lean_object* v_res_1019_; 
v_x_905__boxed_1018_ = lean_unbox_usize(v_x_1016_);
lean_dec(v_x_1016_);
v_res_1019_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_1015_, v_x_905__boxed_1018_, v_x_1017_);
lean_dec_ref(v_x_1017_);
lean_dec_ref(v_x_1015_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(lean_object* v_x_1020_, lean_object* v_x_1021_){
_start:
{
size_t v___x_1022_; size_t v___x_1023_; size_t v___x_1024_; uint64_t v___x_1025_; size_t v___x_1026_; lean_object* v___x_1027_; 
v___x_1022_ = lean_ptr_addr(v_x_1021_);
v___x_1023_ = ((size_t)3ULL);
v___x_1024_ = lean_usize_shift_right(v___x_1022_, v___x_1023_);
v___x_1025_ = lean_usize_to_uint64(v___x_1024_);
v___x_1026_ = lean_uint64_to_usize(v___x_1025_);
v___x_1027_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_1020_, v___x_1026_, v_x_1021_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg___boxed(lean_object* v_x_1028_, lean_object* v_x_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_1028_, v_x_1029_);
lean_dec_ref(v_x_1029_);
lean_dec_ref(v_x_1028_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(lean_object* v_e_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1032_, v_a_1033_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1045_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1038_ = v___x_1035_;
v_isShared_1039_ = v_isSharedCheck_1045_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1035_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1045_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v_exprToRingId_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
v_exprToRingId_1040_ = lean_ctor_get(v_a_1036_, 1);
lean_inc_ref(v_exprToRingId_1040_);
lean_dec(v_a_1036_);
v___x_1041_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_exprToRingId_1040_, v_e_1031_);
lean_dec_ref(v_exprToRingId_1040_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 0, v___x_1041_);
v___x_1043_ = v___x_1038_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
v_a_1046_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_1035_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1035_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg___boxed(lean_object* v_e_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_1054_, v_a_1055_, v_a_1056_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_e_1054_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(lean_object* v_e_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_1059_, v_a_1060_, v_a_1068_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___boxed(lean_object* v_e_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(v_e_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec(v_a_1078_);
lean_dec_ref(v_a_1077_);
lean_dec(v_a_1076_);
lean_dec_ref(v_a_1075_);
lean_dec(v_a_1074_);
lean_dec(v_a_1073_);
lean_dec_ref(v_e_1072_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(lean_object* v_00_u03b2_1085_, lean_object* v_x_1086_, lean_object* v_x_1087_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_1086_, v_x_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___boxed(lean_object* v_00_u03b2_1089_, lean_object* v_x_1090_, lean_object* v_x_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(v_00_u03b2_1089_, v_x_1090_, v_x_1091_);
lean_dec_ref(v_x_1091_);
lean_dec_ref(v_x_1090_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1093_, lean_object* v_x_1094_, size_t v_x_1095_, lean_object* v_x_1096_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_1094_, v_x_1095_, v_x_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1098_, lean_object* v_x_1099_, lean_object* v_x_1100_, lean_object* v_x_1101_){
_start:
{
size_t v_x_1026__boxed_1102_; lean_object* v_res_1103_; 
v_x_1026__boxed_1102_ = lean_unbox_usize(v_x_1100_);
lean_dec(v_x_1100_);
v_res_1103_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(v_00_u03b2_1098_, v_x_1099_, v_x_1026__boxed_1102_, v_x_1101_);
lean_dec_ref(v_x_1101_);
lean_dec_ref(v_x_1099_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1104_, lean_object* v_keys_1105_, lean_object* v_vals_1106_, lean_object* v_heq_1107_, lean_object* v_i_1108_, lean_object* v_k_1109_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1105_, v_vals_1106_, v_i_1108_, v_k_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1111_, lean_object* v_keys_1112_, lean_object* v_vals_1113_, lean_object* v_heq_1114_, lean_object* v_i_1115_, lean_object* v_k_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1111_, v_keys_1112_, v_vals_1113_, v_heq_1114_, v_i_1115_, v_k_1116_);
lean_dec_ref(v_k_1116_);
lean_dec_ref(v_vals_1113_);
lean_dec_ref(v_keys_1112_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0(lean_object* v_toPure_1118_, lean_object* v_____do__lift_1119_){
_start:
{
lean_object* v_charInst_x3f_1123_; 
v_charInst_x3f_1123_ = lean_ctor_get(v_____do__lift_1119_, 5);
lean_inc(v_charInst_x3f_1123_);
lean_dec_ref(v_____do__lift_1119_);
if (lean_obj_tag(v_charInst_x3f_1123_) == 1)
{
lean_object* v_val_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1135_; 
v_val_1124_ = lean_ctor_get(v_charInst_x3f_1123_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v_charInst_x3f_1123_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1126_ = v_charInst_x3f_1123_;
v_isShared_1127_ = v_isSharedCheck_1135_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_val_1124_);
lean_dec(v_charInst_x3f_1123_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1135_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v_snd_1128_; lean_object* v___x_1129_; uint8_t v___x_1130_; 
v_snd_1128_ = lean_ctor_get(v_val_1124_, 1);
lean_inc(v_snd_1128_);
lean_dec(v_val_1124_);
v___x_1129_ = lean_unsigned_to_nat(0u);
v___x_1130_ = lean_nat_dec_eq(v_snd_1128_, v___x_1129_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1132_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v_snd_1128_);
v___x_1132_ = v___x_1126_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_snd_1128_);
v___x_1132_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1133_; 
v___x_1133_ = lean_apply_2(v_toPure_1118_, lean_box(0), v___x_1132_);
return v___x_1133_;
}
}
else
{
lean_dec(v_snd_1128_);
lean_del_object(v___x_1126_);
goto v___jp_1120_;
}
}
}
else
{
lean_dec(v_charInst_x3f_1123_);
goto v___jp_1120_;
}
v___jp_1120_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = lean_box(0);
v___x_1122_ = lean_apply_2(v_toPure_1118_, lean_box(0), v___x_1121_);
return v___x_1122_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(lean_object* v_inst_1136_, lean_object* v_inst_1137_){
_start:
{
lean_object* v_toApplicative_1138_; lean_object* v_toBind_1139_; lean_object* v_getRing_1140_; lean_object* v_toPure_1141_; lean_object* v___f_1142_; lean_object* v___x_1143_; 
v_toApplicative_1138_ = lean_ctor_get(v_inst_1136_, 0);
lean_inc_ref(v_toApplicative_1138_);
v_toBind_1139_ = lean_ctor_get(v_inst_1136_, 1);
lean_inc(v_toBind_1139_);
lean_dec_ref(v_inst_1136_);
v_getRing_1140_ = lean_ctor_get(v_inst_1137_, 0);
lean_inc(v_getRing_1140_);
lean_dec_ref(v_inst_1137_);
v_toPure_1141_ = lean_ctor_get(v_toApplicative_1138_, 1);
lean_inc(v_toPure_1141_);
lean_dec_ref(v_toApplicative_1138_);
v___f_1142_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1142_, 0, v_toPure_1141_);
v___x_1143_ = lean_apply_4(v_toBind_1139_, lean_box(0), lean_box(0), v_getRing_1140_, v___f_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f(lean_object* v_m_1144_, lean_object* v_inst_1145_, lean_object* v_inst_1146_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(v_inst_1145_, v_inst_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0(lean_object* v_toPure_1148_, lean_object* v_____do__lift_1149_){
_start:
{
lean_object* v_charInst_x3f_1153_; 
v_charInst_x3f_1153_ = lean_ctor_get(v_____do__lift_1149_, 5);
lean_inc(v_charInst_x3f_1153_);
lean_dec_ref(v_____do__lift_1149_);
if (lean_obj_tag(v_charInst_x3f_1153_) == 1)
{
lean_object* v_val_1154_; lean_object* v_snd_1155_; lean_object* v___x_1156_; uint8_t v___x_1157_; 
v_val_1154_ = lean_ctor_get(v_charInst_x3f_1153_, 0);
v_snd_1155_ = lean_ctor_get(v_val_1154_, 1);
v___x_1156_ = lean_unsigned_to_nat(0u);
v___x_1157_ = lean_nat_dec_eq(v_snd_1155_, v___x_1156_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; 
v___x_1158_ = lean_apply_2(v_toPure_1148_, lean_box(0), v_charInst_x3f_1153_);
return v___x_1158_;
}
else
{
lean_dec_ref_known(v_charInst_x3f_1153_, 1);
goto v___jp_1150_;
}
}
else
{
lean_dec(v_charInst_x3f_1153_);
goto v___jp_1150_;
}
v___jp_1150_:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = lean_box(0);
v___x_1152_ = lean_apply_2(v_toPure_1148_, lean_box(0), v___x_1151_);
return v___x_1152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(lean_object* v_inst_1159_, lean_object* v_inst_1160_){
_start:
{
lean_object* v_toApplicative_1161_; lean_object* v_toBind_1162_; lean_object* v_getRing_1163_; lean_object* v_toPure_1164_; lean_object* v___f_1165_; lean_object* v___x_1166_; 
v_toApplicative_1161_ = lean_ctor_get(v_inst_1159_, 0);
lean_inc_ref(v_toApplicative_1161_);
v_toBind_1162_ = lean_ctor_get(v_inst_1159_, 1);
lean_inc(v_toBind_1162_);
lean_dec_ref(v_inst_1159_);
v_getRing_1163_ = lean_ctor_get(v_inst_1160_, 0);
lean_inc(v_getRing_1163_);
lean_dec_ref(v_inst_1160_);
v_toPure_1164_ = lean_ctor_get(v_toApplicative_1161_, 1);
lean_inc(v_toPure_1164_);
lean_dec_ref(v_toApplicative_1161_);
v___f_1165_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1165_, 0, v_toPure_1164_);
v___x_1166_ = lean_apply_4(v_toBind_1162_, lean_box(0), lean_box(0), v_getRing_1163_, v___f_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f(lean_object* v_m_1167_, lean_object* v_inst_1168_, lean_object* v_inst_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(v_inst_1168_, v_inst_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_charOneInst_x3f___redArg___lam__0(lean_object* v_toPure_1171_, lean_object* v_____do__lift_1172_){
_start:
{
lean_object* v_charInst_x3f_1176_; 
v_charInst_x3f_1176_ = lean_ctor_get(v_____do__lift_1172_, 5);
lean_inc(v_charInst_x3f_1176_);
lean_dec_ref(v_____do__lift_1172_);
if (lean_obj_tag(v_charInst_x3f_1176_) == 1)
{
lean_object* v_val_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1189_; 
v_val_1177_ = lean_ctor_get(v_charInst_x3f_1176_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_charInst_x3f_1176_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1179_ = v_charInst_x3f_1176_;
v_isShared_1180_ = v_isSharedCheck_1189_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_val_1177_);
lean_dec(v_charInst_x3f_1176_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1189_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v_fst_1181_; lean_object* v_snd_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; 
v_fst_1181_ = lean_ctor_get(v_val_1177_, 0);
lean_inc(v_fst_1181_);
v_snd_1182_ = lean_ctor_get(v_val_1177_, 1);
lean_inc(v_snd_1182_);
lean_dec(v_val_1177_);
v___x_1183_ = lean_unsigned_to_nat(1u);
v___x_1184_ = lean_nat_dec_eq(v_snd_1182_, v___x_1183_);
lean_dec(v_snd_1182_);
if (v___x_1184_ == 0)
{
lean_dec(v_fst_1181_);
lean_del_object(v___x_1179_);
goto v___jp_1173_;
}
else
{
lean_object* v___x_1186_; 
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v_fst_1181_);
v___x_1186_ = v___x_1179_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_fst_1181_);
v___x_1186_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
lean_object* v___x_1187_; 
v___x_1187_ = lean_apply_2(v_toPure_1171_, lean_box(0), v___x_1186_);
return v___x_1187_;
}
}
}
}
else
{
lean_dec(v_charInst_x3f_1176_);
goto v___jp_1173_;
}
v___jp_1173_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = lean_box(0);
v___x_1175_ = lean_apply_2(v_toPure_1171_, lean_box(0), v___x_1174_);
return v___x_1175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_charOneInst_x3f___redArg(lean_object* v_inst_1190_, lean_object* v_inst_1191_){
_start:
{
lean_object* v_toApplicative_1192_; lean_object* v_toBind_1193_; lean_object* v_getRing_1194_; lean_object* v_toPure_1195_; lean_object* v___f_1196_; lean_object* v___x_1197_; 
v_toApplicative_1192_ = lean_ctor_get(v_inst_1190_, 0);
lean_inc_ref(v_toApplicative_1192_);
v_toBind_1193_ = lean_ctor_get(v_inst_1190_, 1);
lean_inc(v_toBind_1193_);
lean_dec_ref(v_inst_1190_);
v_getRing_1194_ = lean_ctor_get(v_inst_1191_, 0);
lean_inc(v_getRing_1194_);
lean_dec_ref(v_inst_1191_);
v_toPure_1195_ = lean_ctor_get(v_toApplicative_1192_, 1);
lean_inc(v_toPure_1195_);
lean_dec_ref(v_toApplicative_1192_);
v___f_1196_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_charOneInst_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1196_, 0, v_toPure_1195_);
v___x_1197_ = lean_apply_4(v_toBind_1193_, lean_box(0), lean_box(0), v_getRing_1194_, v___f_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_charOneInst_x3f(lean_object* v_m_1198_, lean_object* v_inst_1199_, lean_object* v_inst_1200_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Lean_Meta_Grind_Arith_CommRing_charOneInst_x3f___redArg(v_inst_1199_, v_inst_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1223_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1217_ = v___x_1214_;
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1214_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v_noZeroDivInst_x3f_1219_; lean_object* v___x_1221_; 
v_noZeroDivInst_x3f_1219_ = lean_ctor_get(v_a_1215_, 6);
lean_inc(v_noZeroDivInst_x3f_1219_);
lean_dec(v_a_1215_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v_noZeroDivInst_x3f_1219_);
v___x_1221_ = v___x_1217_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_noZeroDivInst_x3f_1219_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
v_a_1224_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1226_ = v___x_1214_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1214_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1224_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f___boxed(lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
lean_dec(v_a_1240_);
lean_dec_ref(v_a_1239_);
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1273_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1260_ = v___x_1257_;
v_isShared_1261_ = v_isSharedCheck_1273_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1257_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1273_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v_noZeroDivInst_x3f_1262_; 
v_noZeroDivInst_x3f_1262_ = lean_ctor_get(v_a_1258_, 6);
lean_inc(v_noZeroDivInst_x3f_1262_);
lean_dec(v_a_1258_);
if (lean_obj_tag(v_noZeroDivInst_x3f_1262_) == 0)
{
uint8_t v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1266_; 
v___x_1263_ = 0;
v___x_1264_ = lean_box(v___x_1263_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 0, v___x_1264_);
v___x_1266_ = v___x_1260_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
else
{
uint8_t v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1271_; 
lean_dec_ref_known(v_noZeroDivInst_x3f_1262_, 1);
v___x_1268_ = 1;
v___x_1269_ = lean_box(v___x_1268_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 0, v___x_1269_);
v___x_1271_ = v___x_1260_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1269_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
v_a_1274_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1257_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1257_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors___boxed(lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_);
lean_dec(v_a_1292_);
lean_dec_ref(v_a_1291_);
lean_dec(v_a_1290_);
lean_dec_ref(v_a_1289_);
lean_dec(v_a_1288_);
lean_dec_ref(v_a_1287_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
lean_dec(v_a_1284_);
lean_dec(v_a_1283_);
lean_dec_ref(v_a_1282_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar(lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1324_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1324_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1324_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v_toRing_1312_; lean_object* v_charInst_x3f_1313_; 
v_toRing_1312_ = lean_ctor_get(v_a_1308_, 0);
lean_inc_ref(v_toRing_1312_);
lean_dec(v_a_1308_);
v_charInst_x3f_1313_ = lean_ctor_get(v_toRing_1312_, 5);
lean_inc(v_charInst_x3f_1313_);
lean_dec_ref(v_toRing_1312_);
if (lean_obj_tag(v_charInst_x3f_1313_) == 0)
{
uint8_t v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1317_; 
v___x_1314_ = 0;
v___x_1315_ = lean_box(v___x_1314_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v___x_1315_);
v___x_1317_ = v___x_1310_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1315_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
else
{
uint8_t v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1322_; 
lean_dec_ref_known(v_charInst_x3f_1313_, 1);
v___x_1319_ = 1;
v___x_1320_ = lean_box(v___x_1319_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v___x_1320_);
v___x_1322_ = v___x_1310_;
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
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
v_a_1325_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1307_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1307_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar___boxed(lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lean_Meta_Grind_Arith_CommRing_hasChar(v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_);
lean_dec(v_a_1343_);
lean_dec_ref(v_a_1342_);
lean_dec(v_a_1341_);
lean_dec_ref(v_a_1340_);
lean_dec(v_a_1339_);
lean_dec_ref(v_a_1338_);
lean_dec(v_a_1337_);
lean_dec_ref(v_a_1336_);
lean_dec(v_a_1335_);
lean_dec(v_a_1334_);
lean_dec_ref(v_a_1333_);
return v_res_1345_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1(void){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0));
v___x_1348_ = l_Lean_stringToMessageData(v___x_1347_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst(lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1374_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1374_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1374_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v_toRing_1366_; lean_object* v_charInst_x3f_1367_; 
v_toRing_1366_ = lean_ctor_get(v_a_1362_, 0);
lean_inc_ref(v_toRing_1366_);
lean_dec(v_a_1362_);
v_charInst_x3f_1367_ = lean_ctor_get(v_toRing_1366_, 5);
lean_inc(v_charInst_x3f_1367_);
lean_dec_ref(v_toRing_1366_);
if (lean_obj_tag(v_charInst_x3f_1367_) == 1)
{
lean_object* v_val_1368_; lean_object* v___x_1370_; 
v_val_1368_ = lean_ctor_get(v_charInst_x3f_1367_, 0);
lean_inc(v_val_1368_);
lean_dec_ref_known(v_charInst_x3f_1367_, 1);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v_val_1368_);
v___x_1370_ = v___x_1364_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_val_1368_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
lean_dec(v_charInst_x3f_1367_);
lean_del_object(v___x_1364_);
v___x_1372_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1);
v___x_1373_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v___x_1372_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
return v___x_1373_;
}
}
}
else
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
v_a_1375_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___x_1361_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1361_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1375_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst___boxed(lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_Meta_Grind_Arith_CommRing_getCharInst(v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec(v_a_1391_);
lean_dec_ref(v_a_1390_);
lean_dec(v_a_1389_);
lean_dec_ref(v_a_1388_);
lean_dec(v_a_1387_);
lean_dec_ref(v_a_1386_);
lean_dec(v_a_1385_);
lean_dec(v_a_1384_);
lean_dec_ref(v_a_1383_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField(lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1424_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1411_ = v___x_1408_;
v_isShared_1412_ = v_isSharedCheck_1424_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1408_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1424_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v_fieldInst_x3f_1413_; 
v_fieldInst_x3f_1413_ = lean_ctor_get(v_a_1409_, 7);
lean_inc(v_fieldInst_x3f_1413_);
lean_dec(v_a_1409_);
if (lean_obj_tag(v_fieldInst_x3f_1413_) == 0)
{
uint8_t v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1417_; 
v___x_1414_ = 0;
v___x_1415_ = lean_box(v___x_1414_);
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 0, v___x_1415_);
v___x_1417_ = v___x_1411_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
else
{
uint8_t v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1422_; 
lean_dec_ref_known(v_fieldInst_x3f_1413_, 1);
v___x_1419_ = 1;
v___x_1420_ = lean_box(v___x_1419_);
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 0, v___x_1420_);
v___x_1422_ = v___x_1411_;
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
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
v_a_1425_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1408_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1408_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField___boxed(lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Lean_Meta_Grind_Arith_CommRing_isField(v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_);
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
lean_dec_ref(v_a_1433_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___redArg(lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1466_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1453_ = v___x_1450_;
v_isShared_1454_ = v_isSharedCheck_1466_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1450_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1466_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v_queue_1455_; 
v_queue_1455_ = lean_ctor_get(v_a_1451_, 4);
lean_inc(v_queue_1455_);
lean_dec(v_a_1451_);
if (lean_obj_tag(v_queue_1455_) == 0)
{
uint8_t v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1459_; 
lean_dec_ref_known(v_queue_1455_, 5);
v___x_1456_ = 0;
v___x_1457_ = lean_box(v___x_1456_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1457_);
v___x_1459_ = v___x_1453_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1457_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
else
{
uint8_t v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1464_; 
v___x_1461_ = 1;
v___x_1462_ = lean_box(v___x_1461_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1462_);
v___x_1464_ = v___x_1453_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1462_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
v_a_1467_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1450_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1450_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___redArg___boxed(lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___redArg(v_a_1475_, v_a_1476_, v_a_1477_);
lean_dec_ref(v_a_1477_);
lean_dec(v_a_1476_);
lean_dec_ref(v_a_1475_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___redArg(v_a_1480_, v_a_1481_, v_a_1489_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___boxed(lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_);
lean_dec(v_a_1503_);
lean_dec_ref(v_a_1502_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
lean_dec(v_a_1497_);
lean_dec_ref(v_a_1496_);
lean_dec(v_a_1495_);
lean_dec(v_a_1494_);
lean_dec_ref(v_a_1493_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(lean_object* v_k_1506_, lean_object* v_t_1507_){
_start:
{
if (lean_obj_tag(v_t_1507_) == 0)
{
lean_object* v_k_1508_; lean_object* v_v_1509_; lean_object* v_l_1510_; lean_object* v_r_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_2165_; 
v_k_1508_ = lean_ctor_get(v_t_1507_, 1);
v_v_1509_ = lean_ctor_get(v_t_1507_, 2);
v_l_1510_ = lean_ctor_get(v_t_1507_, 3);
v_r_1511_ = lean_ctor_get(v_t_1507_, 4);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_t_1507_);
if (v_isSharedCheck_2165_ == 0)
{
lean_object* v_unused_2166_; 
v_unused_2166_ = lean_ctor_get(v_t_1507_, 0);
lean_dec(v_unused_2166_);
v___x_1513_ = v_t_1507_;
v_isShared_1514_ = v_isSharedCheck_2165_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_r_1511_);
lean_inc(v_l_1510_);
lean_inc(v_v_1509_);
lean_inc(v_k_1508_);
lean_dec(v_t_1507_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_2165_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
uint8_t v___x_1515_; 
v___x_1515_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(v_k_1506_, v_k_1508_);
switch(v___x_1515_)
{
case 0:
{
lean_object* v_impl_1516_; lean_object* v___x_1517_; 
v_impl_1516_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1506_, v_l_1510_);
v___x_1517_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1516_) == 0)
{
if (lean_obj_tag(v_r_1511_) == 0)
{
lean_object* v_size_1518_; lean_object* v_size_1519_; lean_object* v_k_1520_; lean_object* v_v_1521_; lean_object* v_l_1522_; lean_object* v_r_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; uint8_t v___x_1526_; 
v_size_1518_ = lean_ctor_get(v_impl_1516_, 0);
v_size_1519_ = lean_ctor_get(v_r_1511_, 0);
v_k_1520_ = lean_ctor_get(v_r_1511_, 1);
v_v_1521_ = lean_ctor_get(v_r_1511_, 2);
v_l_1522_ = lean_ctor_get(v_r_1511_, 3);
lean_inc(v_l_1522_);
v_r_1523_ = lean_ctor_get(v_r_1511_, 4);
v___x_1524_ = lean_unsigned_to_nat(3u);
v___x_1525_ = lean_nat_mul(v___x_1524_, v_size_1518_);
v___x_1526_ = lean_nat_dec_lt(v___x_1525_, v_size_1519_);
lean_dec(v___x_1525_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1530_; 
lean_dec(v_l_1522_);
v___x_1527_ = lean_nat_add(v___x_1517_, v_size_1518_);
v___x_1528_ = lean_nat_add(v___x_1527_, v_size_1519_);
lean_dec(v___x_1527_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 3, v_impl_1516_);
lean_ctor_set(v___x_1513_, 0, v___x_1528_);
v___x_1530_ = v___x_1513_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1528_);
lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_k_1508_);
lean_ctor_set(v_reuseFailAlloc_1531_, 2, v_v_1509_);
lean_ctor_set(v_reuseFailAlloc_1531_, 3, v_impl_1516_);
lean_ctor_set(v_reuseFailAlloc_1531_, 4, v_r_1511_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
else
{
lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1595_; 
lean_inc(v_r_1523_);
lean_inc(v_v_1521_);
lean_inc(v_k_1520_);
lean_inc(v_size_1519_);
v_isSharedCheck_1595_ = !lean_is_exclusive(v_r_1511_);
if (v_isSharedCheck_1595_ == 0)
{
lean_object* v_unused_1596_; lean_object* v_unused_1597_; lean_object* v_unused_1598_; lean_object* v_unused_1599_; lean_object* v_unused_1600_; 
v_unused_1596_ = lean_ctor_get(v_r_1511_, 4);
lean_dec(v_unused_1596_);
v_unused_1597_ = lean_ctor_get(v_r_1511_, 3);
lean_dec(v_unused_1597_);
v_unused_1598_ = lean_ctor_get(v_r_1511_, 2);
lean_dec(v_unused_1598_);
v_unused_1599_ = lean_ctor_get(v_r_1511_, 1);
lean_dec(v_unused_1599_);
v_unused_1600_ = lean_ctor_get(v_r_1511_, 0);
lean_dec(v_unused_1600_);
v___x_1533_ = v_r_1511_;
v_isShared_1534_ = v_isSharedCheck_1595_;
goto v_resetjp_1532_;
}
else
{
lean_dec(v_r_1511_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1595_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v_size_1535_; lean_object* v_k_1536_; lean_object* v_v_1537_; lean_object* v_l_1538_; lean_object* v_r_1539_; lean_object* v_size_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; 
v_size_1535_ = lean_ctor_get(v_l_1522_, 0);
v_k_1536_ = lean_ctor_get(v_l_1522_, 1);
v_v_1537_ = lean_ctor_get(v_l_1522_, 2);
v_l_1538_ = lean_ctor_get(v_l_1522_, 3);
v_r_1539_ = lean_ctor_get(v_l_1522_, 4);
v_size_1540_ = lean_ctor_get(v_r_1523_, 0);
v___x_1541_ = lean_unsigned_to_nat(2u);
v___x_1542_ = lean_nat_mul(v___x_1541_, v_size_1540_);
v___x_1543_ = lean_nat_dec_lt(v_size_1535_, v___x_1542_);
lean_dec(v___x_1542_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1571_; 
lean_inc(v_r_1539_);
lean_inc(v_l_1538_);
lean_inc(v_v_1537_);
lean_inc(v_k_1536_);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_l_1522_);
if (v_isSharedCheck_1571_ == 0)
{
lean_object* v_unused_1572_; lean_object* v_unused_1573_; lean_object* v_unused_1574_; lean_object* v_unused_1575_; lean_object* v_unused_1576_; 
v_unused_1572_ = lean_ctor_get(v_l_1522_, 4);
lean_dec(v_unused_1572_);
v_unused_1573_ = lean_ctor_get(v_l_1522_, 3);
lean_dec(v_unused_1573_);
v_unused_1574_ = lean_ctor_get(v_l_1522_, 2);
lean_dec(v_unused_1574_);
v_unused_1575_ = lean_ctor_get(v_l_1522_, 1);
lean_dec(v_unused_1575_);
v_unused_1576_ = lean_ctor_get(v_l_1522_, 0);
lean_dec(v_unused_1576_);
v___x_1545_ = v_l_1522_;
v_isShared_1546_ = v_isSharedCheck_1571_;
goto v_resetjp_1544_;
}
else
{
lean_dec(v_l_1522_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1571_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1561_; 
v___x_1547_ = lean_nat_add(v___x_1517_, v_size_1518_);
v___x_1548_ = lean_nat_add(v___x_1547_, v_size_1519_);
lean_dec(v_size_1519_);
if (lean_obj_tag(v_l_1538_) == 0)
{
lean_object* v_size_1569_; 
v_size_1569_ = lean_ctor_get(v_l_1538_, 0);
lean_inc(v_size_1569_);
v___y_1561_ = v_size_1569_;
goto v___jp_1560_;
}
else
{
lean_object* v___x_1570_; 
v___x_1570_ = lean_unsigned_to_nat(0u);
v___y_1561_ = v___x_1570_;
goto v___jp_1560_;
}
v___jp_1549_:
{
lean_object* v___x_1553_; lean_object* v___x_1555_; 
v___x_1553_ = lean_nat_add(v___y_1550_, v___y_1552_);
lean_dec(v___y_1552_);
lean_dec(v___y_1550_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 4, v_r_1523_);
lean_ctor_set(v___x_1545_, 3, v_r_1539_);
lean_ctor_set(v___x_1545_, 2, v_v_1521_);
lean_ctor_set(v___x_1545_, 1, v_k_1520_);
lean_ctor_set(v___x_1545_, 0, v___x_1553_);
v___x_1555_ = v___x_1545_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_k_1520_);
lean_ctor_set(v_reuseFailAlloc_1559_, 2, v_v_1521_);
lean_ctor_set(v_reuseFailAlloc_1559_, 3, v_r_1539_);
lean_ctor_set(v_reuseFailAlloc_1559_, 4, v_r_1523_);
v___x_1555_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
lean_object* v___x_1557_; 
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 4, v___x_1555_);
lean_ctor_set(v___x_1533_, 3, v___y_1551_);
lean_ctor_set(v___x_1533_, 2, v_v_1537_);
lean_ctor_set(v___x_1533_, 1, v_k_1536_);
lean_ctor_set(v___x_1533_, 0, v___x_1548_);
v___x_1557_ = v___x_1533_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1548_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_k_1536_);
lean_ctor_set(v_reuseFailAlloc_1558_, 2, v_v_1537_);
lean_ctor_set(v_reuseFailAlloc_1558_, 3, v___y_1551_);
lean_ctor_set(v_reuseFailAlloc_1558_, 4, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
v___jp_1560_:
{
lean_object* v___x_1562_; lean_object* v___x_1564_; 
v___x_1562_ = lean_nat_add(v___x_1547_, v___y_1561_);
lean_dec(v___y_1561_);
lean_dec(v___x_1547_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 4, v_l_1538_);
lean_ctor_set(v___x_1513_, 3, v_impl_1516_);
lean_ctor_set(v___x_1513_, 0, v___x_1562_);
v___x_1564_ = v___x_1513_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1562_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v_k_1508_);
lean_ctor_set(v_reuseFailAlloc_1568_, 2, v_v_1509_);
lean_ctor_set(v_reuseFailAlloc_1568_, 3, v_impl_1516_);
lean_ctor_set(v_reuseFailAlloc_1568_, 4, v_l_1538_);
v___x_1564_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_nat_add(v___x_1517_, v_size_1540_);
if (lean_obj_tag(v_r_1539_) == 0)
{
lean_object* v_size_1566_; 
v_size_1566_ = lean_ctor_get(v_r_1539_, 0);
lean_inc(v_size_1566_);
v___y_1550_ = v___x_1565_;
v___y_1551_ = v___x_1564_;
v___y_1552_ = v_size_1566_;
goto v___jp_1549_;
}
else
{
lean_object* v___x_1567_; 
v___x_1567_ = lean_unsigned_to_nat(0u);
v___y_1550_ = v___x_1565_;
v___y_1551_ = v___x_1564_;
v___y_1552_ = v___x_1567_;
goto v___jp_1549_;
}
}
}
}
}
else
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1581_; 
lean_del_object(v___x_1513_);
v___x_1577_ = lean_nat_add(v___x_1517_, v_size_1518_);
v___x_1578_ = lean_nat_add(v___x_1577_, v_size_1519_);
lean_dec(v_size_1519_);
v___x_1579_ = lean_nat_add(v___x_1577_, v_size_1535_);
lean_dec(v___x_1577_);
lean_inc_ref(v_impl_1516_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 4, v_l_1522_);
lean_ctor_set(v___x_1533_, 3, v_impl_1516_);
lean_ctor_set(v___x_1533_, 2, v_v_1509_);
lean_ctor_set(v___x_1533_, 1, v_k_1508_);
lean_ctor_set(v___x_1533_, 0, v___x_1579_);
v___x_1581_ = v___x_1533_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1579_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_k_1508_);
lean_ctor_set(v_reuseFailAlloc_1594_, 2, v_v_1509_);
lean_ctor_set(v_reuseFailAlloc_1594_, 3, v_impl_1516_);
lean_ctor_set(v_reuseFailAlloc_1594_, 4, v_l_1522_);
v___x_1581_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
v_isSharedCheck_1588_ = !lean_is_exclusive(v_impl_1516_);
if (v_isSharedCheck_1588_ == 0)
{
lean_object* v_unused_1589_; lean_object* v_unused_1590_; lean_object* v_unused_1591_; lean_object* v_unused_1592_; lean_object* v_unused_1593_; 
v_unused_1589_ = lean_ctor_get(v_impl_1516_, 4);
lean_dec(v_unused_1589_);
v_unused_1590_ = lean_ctor_get(v_impl_1516_, 3);
lean_dec(v_unused_1590_);
v_unused_1591_ = lean_ctor_get(v_impl_1516_, 2);
lean_dec(v_unused_1591_);
v_unused_1592_ = lean_ctor_get(v_impl_1516_, 1);
lean_dec(v_unused_1592_);
v_unused_1593_ = lean_ctor_get(v_impl_1516_, 0);
lean_dec(v_unused_1593_);
v___x_1583_ = v_impl_1516_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_dec(v_impl_1516_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 4, v_r_1523_);
lean_ctor_set(v___x_1583_, 3, v___x_1581_);
lean_ctor_set(v___x_1583_, 2, v_v_1521_);
lean_ctor_set(v___x_1583_, 1, v_k_1520_);
lean_ctor_set(v___x_1583_, 0, v___x_1578_);
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v_k_1520_);
lean_ctor_set(v_reuseFailAlloc_1587_, 2, v_v_1521_);
lean_ctor_set(v_reuseFailAlloc_1587_, 3, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1587_, 4, v_r_1523_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1601_; lean_object* v___x_1602_; lean_object* v___x_1604_; 
v_size_1601_ = lean_ctor_get(v_impl_1516_, 0);
v___x_1602_ = lean_nat_add(v___x_1517_, v_size_1601_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 3, v_impl_1516_);
lean_ctor_set(v___x_1513_, 0, v___x_1602_);
v___x_1604_ = v___x_1513_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1602_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_k_1508_);
lean_ctor_set(v_reuseFailAlloc_1605_, 2, v_v_1509_);
lean_ctor_set(v_reuseFailAlloc_1605_, 3, v_impl_1516_);
lean_ctor_set(v_reuseFailAlloc_1605_, 4, v_r_1511_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
else
{
if (lean_obj_tag(v_r_1511_) == 0)
{
lean_object* v_l_1606_; 
v_l_1606_ = lean_ctor_get(v_r_1511_, 3);
lean_inc(v_l_1606_);
if (lean_obj_tag(v_l_1606_) == 0)
{
lean_object* v_r_1607_; 
v_r_1607_ = lean_ctor_get(v_r_1511_, 4);
lean_inc(v_r_1607_);
if (lean_obj_tag(v_r_1607_) == 0)
{
lean_object* v_size_1608_; lean_object* v_k_1609_; lean_object* v_v_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1623_; 
v_size_1608_ = lean_ctor_get(v_r_1511_, 0);
v_k_1609_ = lean_ctor_get(v_r_1511_, 1);
v_v_1610_ = lean_ctor_get(v_r_1511_, 2);
v_isSharedCheck_1623_ = !lean_is_exclusive(v_r_1511_);
if (v_isSharedCheck_1623_ == 0)
{
lean_object* v_unused_1624_; lean_object* v_unused_1625_; 
v_unused_1624_ = lean_ctor_get(v_r_1511_, 4);
lean_dec(v_unused_1624_);
v_unused_1625_ = lean_ctor_get(v_r_1511_, 3);
lean_dec(v_unused_1625_);
v___x_1612_ = v_r_1511_;
v_isShared_1613_ = v_isSharedCheck_1623_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_v_1610_);
lean_inc(v_k_1609_);
lean_inc(v_size_1608_);
lean_dec(v_r_1511_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1623_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v_size_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1618_; 
v_size_1614_ = lean_ctor_get(v_l_1606_, 0);
v___x_1615_ = lean_nat_add(v___x_1517_, v_size_1608_);
lean_dec(v_size_1608_);
v___x_1616_ = lean_nat_add(v___x_1517_, v_size_1614_);
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 4, v_l_1606_);
lean_ctor_set(v___x_1612_, 3, v_impl_1516_);
lean_ctor_set(v___x_1612_, 2, v_v_1509_);
lean_ctor_set(v___x_1612_, 1, v_k_1508_);
lean_ctor_set(v___x_1612_, 0, v___x_1616_);
v___x_1618_ = v___x_1612_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1616_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v_k_1508_);
lean_ctor_set(v_reuseFailAlloc_1622_, 2, v_v_1509_);
lean_ctor_set(v_reuseFailAlloc_1622_, 3, v_impl_1516_);
lean_ctor_set(v_reuseFailAlloc_1622_, 4, v_l_1606_);
v___x_1618_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
lean_object* v___x_1620_; 
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 4, v_r_1607_);
lean_ctor_set(v___x_1513_, 3, v___x_1618_);
lean_ctor_set(v___x_1513_, 2, v_v_1610_);
lean_ctor_set(v___x_1513_, 1, v_k_1609_);
lean_ctor_set(v___x_1513_, 0, v___x_1615_);
v___x_1620_ = v___x_1513_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1615_);
lean_ctor_set(v_reuseFailAlloc_1621_, 1, v_k_1609_);
lean_ctor_set(v_reuseFailAlloc_1621_, 2, v_v_1610_);
lean_ctor_set(v_reuseFailAlloc_1621_, 3, v___x_1618_);
lean_ctor_set(v_reuseFailAlloc_1621_, 4, v_r_1607_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
else
{
lean_object* v_k_1626_; lean_object* v_v_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1650_; 
v_k_1626_ = lean_ctor_get(v_r_1511_, 1);
v_v_1627_ = lean_ctor_get(v_r_1511_, 2);
v_isSharedCheck_1650_ = !lean_is_exclusive(v_r_1511_);
if (v_isSharedCheck_1650_ == 0)
{
lean_object* v_unused_1651_; lean_object* v_unused_1652_; lean_object* v_unused_1653_; 
v_unused_1651_ = lean_ctor_get(v_r_1511_, 4);
lean_dec(v_unused_1651_);
v_unused_1652_ = lean_ctor_get(v_r_1511_, 3);
lean_dec(v_unused_1652_);
v_unused_1653_ = lean_ctor_get(v_r_1511_, 0);
lean_dec(v_unused_1653_);
v___x_1629_ = v_r_1511_;
v_isShared_1630_ = v_isSharedCheck_1650_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_v_1627_);
lean_inc(v_k_1626_);
lean_dec(v_r_1511_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1650_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v_k_1631_; lean_object* v_v_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1646_; 
v_k_1631_ = lean_ctor_get(v_l_1606_, 1);
v_v_1632_ = lean_ctor_get(v_l_1606_, 2);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_l_1606_);
if (v_isSharedCheck_1646_ == 0)
{
lean_object* v_unused_1647_; lean_object* v_unused_1648_; lean_object* v_unused_1649_; 
v_unused_1647_ = lean_ctor_get(v_l_1606_, 4);
lean_dec(v_unused_1647_);
v_unused_1648_ = lean_ctor_get(v_l_1606_, 3);
lean_dec(v_unused_1648_);
v_unused_1649_ = lean_ctor_get(v_l_1606_, 0);
lean_dec(v_unused_1649_);
v___x_1634_ = v_l_1606_;
v_isShared_1635_ = v_isSharedCheck_1646_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_v_1632_);
lean_inc(v_k_1631_);
lean_dec(v_l_1606_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1646_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1636_; lean_object* v___x_1638_; 
v___x_1636_ = lean_unsigned_to_nat(3u);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 4, v_r_1607_);
lean_ctor_set(v___x_1634_, 3, v_r_1607_);
lean_ctor_set(v___x_1634_, 2, v_v_1509_);
lean_ctor_set(v___x_1634_, 1, v_k_1508_);
lean_ctor_set(v___x_1634_, 0, v___x_1517_);
v___x_1638_ = v___x_1634_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_k_1508_);
lean_ctor_set(v_reuseFailAlloc_1645_, 2, v_v_1509_);
lean_ctor_set(v_reuseFailAlloc_1645_, 3, v_r_1607_);
lean_ctor_set(v_reuseFailAlloc_1645_, 4, v_r_1607_);
v___x_1638_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
lean_object* v___x_1640_; 
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 3, v_r_1607_);
lean_ctor_set(v___x_1629_, 0, v___x_1517_);
v___x_1640_ = v___x_1629_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_k_1626_);
lean_ctor_set(v_reuseFailAlloc_1644_, 2, v_v_1627_);
lean_ctor_set(v_reuseFailAlloc_1644_, 3, v_r_1607_);
lean_ctor_set(v_reuseFailAlloc_1644_, 4, v_r_1607_);
v___x_1640_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
lean_object* v___x_1642_; 
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 4, v___x_1640_);
lean_ctor_set(v___x_1513_, 3, v___x_1638_);
lean_ctor_set(v___x_1513_, 2, v_v_1632_);
lean_ctor_set(v___x_1513_, 1, v_k_1631_);
lean_ctor_set(v___x_1513_, 0, v___x_1636_);
v___x_1642_ = v___x_1513_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1636_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_k_1631_);
lean_ctor_set(v_reuseFailAlloc_1643_, 2, v_v_1632_);
lean_ctor_set(v_reuseFailAlloc_1643_, 3, v___x_1638_);
lean_ctor_set(v_reuseFailAlloc_1643_, 4, v___x_1640_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1654_; 
v_r_1654_ = lean_ctor_get(v_r_1511_, 4);
lean_inc(v_r_1654_);
if (lean_obj_tag(v_r_1654_) == 0)
{
lean_object* v_k_1655_; lean_object* v_v_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1667_; 
v_k_1655_ = lean_ctor_get(v_r_1511_, 1);
v_v_1656_ = lean_ctor_get(v_r_1511_, 2);
v_isSharedCheck_1667_ = !lean_is_exclusive(v_r_1511_);
if (v_isSharedCheck_1667_ == 0)
{
lean_object* v_unused_1668_; lean_object* v_unused_1669_; lean_object* v_unused_1670_; 
v_unused_1668_ = lean_ctor_get(v_r_1511_, 4);
lean_dec(v_unused_1668_);
v_unused_1669_ = lean_ctor_get(v_r_1511_, 3);
lean_dec(v_unused_1669_);
v_unused_1670_ = lean_ctor_get(v_r_1511_, 0);
lean_dec(v_unused_1670_);
v___x_1658_ = v_r_1511_;
v_isShared_1659_ = v_isSharedCheck_1667_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_v_1656_);
lean_inc(v_k_1655_);
lean_dec(v_r_1511_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1667_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1660_; lean_object* v___x_1662_; 
v___x_1660_ = lean_unsigned_to_nat(3u);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 4, v_l_1606_);
lean_ctor_set(v___x_1658_, 2, v_v_1509_);
lean_ctor_set(v___x_1658_, 1, v_k_1508_);
lean_ctor_set(v___x_1658_, 0, v___x_1517_);
v___x_1662_ = v___x_1658_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_k_1508_);
lean_ctor_set(v_reuseFailAlloc_1666_, 2, v_v_1509_);
lean_ctor_set(v_reuseFailAlloc_1666_, 3, v_l_1606_);
lean_ctor_set(v_reuseFailAlloc_1666_, 4, v_l_1606_);
v___x_1662_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1664_; 
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 4, v_r_1654_);
lean_ctor_set(v___x_1513_, 3, v___x_1662_);
lean_ctor_set(v___x_1513_, 2, v_v_1656_);
lean_ctor_set(v___x_1513_, 1, v_k_1655_);
lean_ctor_set(v___x_1513_, 0, v___x_1660_);
v___x_1664_ = v___x_1513_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1660_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_k_1655_);
lean_ctor_set(v_reuseFailAlloc_1665_, 2, v_v_1656_);
lean_ctor_set(v_reuseFailAlloc_1665_, 3, v___x_1662_);
lean_ctor_set(v_reuseFailAlloc_1665_, 4, v_r_1654_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
else
{
lean_object* v_size_1671_; lean_object* v_k_1672_; lean_object* v_v_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1684_; 
v_size_1671_ = lean_ctor_get(v_r_1511_, 0);
v_k_1672_ = lean_ctor_get(v_r_1511_, 1);
v_v_1673_ = lean_ctor_get(v_r_1511_, 2);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_r_1511_);
if (v_isSharedCheck_1684_ == 0)
{
lean_object* v_unused_1685_; lean_object* v_unused_1686_; 
v_unused_1685_ = lean_ctor_get(v_r_1511_, 4);
lean_dec(v_unused_1685_);
v_unused_1686_ = lean_ctor_get(v_r_1511_, 3);
lean_dec(v_unused_1686_);
v___x_1675_ = v_r_1511_;
v_isShared_1676_ = v_isSharedCheck_1684_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_v_1673_);
lean_inc(v_k_1672_);
lean_inc(v_size_1671_);
lean_dec(v_r_1511_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1684_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 3, v_r_1654_);
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_size_1671_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_k_1672_);
lean_ctor_set(v_reuseFailAlloc_1683_, 2, v_v_1673_);
lean_ctor_set(v_reuseFailAlloc_1683_, 3, v_r_1654_);
lean_ctor_set(v_reuseFailAlloc_1683_, 4, v_r_1654_);
v___x_1678_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1679_ = lean_unsigned_to_nat(2u);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 4, v___x_1678_);
lean_ctor_set(v___x_1513_, 3, v_r_1654_);
lean_ctor_set(v___x_1513_, 0, v___x_1679_);
v___x_1681_ = v___x_1513_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v_k_1508_);
lean_ctor_set(v_reuseFailAlloc_1682_, 2, v_v_1509_);
lean_ctor_set(v_reuseFailAlloc_1682_, 3, v_r_1654_);
lean_ctor_set(v_reuseFailAlloc_1682_, 4, v___x_1678_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
}
}
else
{
lean_object* v___x_1688_; 
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 3, v_r_1511_);
lean_ctor_set(v___x_1513_, 0, v___x_1517_);
v___x_1688_ = v___x_1513_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v_k_1508_);
lean_ctor_set(v_reuseFailAlloc_1689_, 2, v_v_1509_);
lean_ctor_set(v_reuseFailAlloc_1689_, 3, v_r_1511_);
lean_ctor_set(v_reuseFailAlloc_1689_, 4, v_r_1511_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1513_);
lean_dec(v_v_1509_);
lean_dec(v_k_1508_);
if (lean_obj_tag(v_l_1510_) == 0)
{
if (lean_obj_tag(v_r_1511_) == 0)
{
lean_object* v_size_1690_; lean_object* v_k_1691_; lean_object* v_v_1692_; lean_object* v_l_1693_; lean_object* v_r_1694_; lean_object* v_size_1695_; lean_object* v_k_1696_; lean_object* v_v_1697_; lean_object* v_l_1698_; lean_object* v_r_1699_; lean_object* v___x_1700_; uint8_t v___x_1701_; 
v_size_1690_ = lean_ctor_get(v_l_1510_, 0);
v_k_1691_ = lean_ctor_get(v_l_1510_, 1);
v_v_1692_ = lean_ctor_get(v_l_1510_, 2);
v_l_1693_ = lean_ctor_get(v_l_1510_, 3);
v_r_1694_ = lean_ctor_get(v_l_1510_, 4);
lean_inc(v_r_1694_);
v_size_1695_ = lean_ctor_get(v_r_1511_, 0);
v_k_1696_ = lean_ctor_get(v_r_1511_, 1);
v_v_1697_ = lean_ctor_get(v_r_1511_, 2);
v_l_1698_ = lean_ctor_get(v_r_1511_, 3);
lean_inc(v_l_1698_);
v_r_1699_ = lean_ctor_get(v_r_1511_, 4);
v___x_1700_ = lean_unsigned_to_nat(1u);
v___x_1701_ = lean_nat_dec_lt(v_size_1690_, v_size_1695_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1837_; 
lean_inc(v_l_1693_);
lean_inc(v_v_1692_);
lean_inc(v_k_1691_);
v_isSharedCheck_1837_ = !lean_is_exclusive(v_l_1510_);
if (v_isSharedCheck_1837_ == 0)
{
lean_object* v_unused_1838_; lean_object* v_unused_1839_; lean_object* v_unused_1840_; lean_object* v_unused_1841_; lean_object* v_unused_1842_; 
v_unused_1838_ = lean_ctor_get(v_l_1510_, 4);
lean_dec(v_unused_1838_);
v_unused_1839_ = lean_ctor_get(v_l_1510_, 3);
lean_dec(v_unused_1839_);
v_unused_1840_ = lean_ctor_get(v_l_1510_, 2);
lean_dec(v_unused_1840_);
v_unused_1841_ = lean_ctor_get(v_l_1510_, 1);
lean_dec(v_unused_1841_);
v_unused_1842_ = lean_ctor_get(v_l_1510_, 0);
lean_dec(v_unused_1842_);
v___x_1703_ = v_l_1510_;
v_isShared_1704_ = v_isSharedCheck_1837_;
goto v_resetjp_1702_;
}
else
{
lean_dec(v_l_1510_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1837_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1705_; lean_object* v_tree_1706_; 
v___x_1705_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1691_, v_v_1692_, v_l_1693_, v_r_1694_);
v_tree_1706_ = lean_ctor_get(v___x_1705_, 2);
if (lean_obj_tag(v_tree_1706_) == 0)
{
lean_object* v_k_1707_; lean_object* v_v_1708_; lean_object* v_size_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
lean_inc_ref(v_tree_1706_);
v_k_1707_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_k_1707_);
v_v_1708_ = lean_ctor_get(v___x_1705_, 1);
lean_inc(v_v_1708_);
lean_dec_ref(v___x_1705_);
v_size_1709_ = lean_ctor_get(v_tree_1706_, 0);
v___x_1710_ = lean_unsigned_to_nat(3u);
v___x_1711_ = lean_nat_mul(v___x_1710_, v_size_1709_);
v___x_1712_ = lean_nat_dec_lt(v___x_1711_, v_size_1695_);
lean_dec(v___x_1711_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1716_; 
lean_dec(v_l_1698_);
v___x_1713_ = lean_nat_add(v___x_1700_, v_size_1709_);
v___x_1714_ = lean_nat_add(v___x_1713_, v_size_1695_);
lean_dec(v___x_1713_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 4, v_r_1511_);
lean_ctor_set(v___x_1703_, 3, v_tree_1706_);
lean_ctor_set(v___x_1703_, 2, v_v_1708_);
lean_ctor_set(v___x_1703_, 1, v_k_1707_);
lean_ctor_set(v___x_1703_, 0, v___x_1714_);
v___x_1716_ = v___x_1703_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1714_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_k_1707_);
lean_ctor_set(v_reuseFailAlloc_1717_, 2, v_v_1708_);
lean_ctor_set(v_reuseFailAlloc_1717_, 3, v_tree_1706_);
lean_ctor_set(v_reuseFailAlloc_1717_, 4, v_r_1511_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
else
{
lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1772_; 
lean_inc(v_r_1699_);
lean_inc(v_v_1697_);
lean_inc(v_k_1696_);
lean_inc(v_size_1695_);
v_isSharedCheck_1772_ = !lean_is_exclusive(v_r_1511_);
if (v_isSharedCheck_1772_ == 0)
{
lean_object* v_unused_1773_; lean_object* v_unused_1774_; lean_object* v_unused_1775_; lean_object* v_unused_1776_; lean_object* v_unused_1777_; 
v_unused_1773_ = lean_ctor_get(v_r_1511_, 4);
lean_dec(v_unused_1773_);
v_unused_1774_ = lean_ctor_get(v_r_1511_, 3);
lean_dec(v_unused_1774_);
v_unused_1775_ = lean_ctor_get(v_r_1511_, 2);
lean_dec(v_unused_1775_);
v_unused_1776_ = lean_ctor_get(v_r_1511_, 1);
lean_dec(v_unused_1776_);
v_unused_1777_ = lean_ctor_get(v_r_1511_, 0);
lean_dec(v_unused_1777_);
v___x_1719_ = v_r_1511_;
v_isShared_1720_ = v_isSharedCheck_1772_;
goto v_resetjp_1718_;
}
else
{
lean_dec(v_r_1511_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1772_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v_size_1721_; lean_object* v_k_1722_; lean_object* v_v_1723_; lean_object* v_l_1724_; lean_object* v_r_1725_; lean_object* v_size_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v_size_1721_ = lean_ctor_get(v_l_1698_, 0);
v_k_1722_ = lean_ctor_get(v_l_1698_, 1);
v_v_1723_ = lean_ctor_get(v_l_1698_, 2);
v_l_1724_ = lean_ctor_get(v_l_1698_, 3);
v_r_1725_ = lean_ctor_get(v_l_1698_, 4);
v_size_1726_ = lean_ctor_get(v_r_1699_, 0);
v___x_1727_ = lean_unsigned_to_nat(2u);
v___x_1728_ = lean_nat_mul(v___x_1727_, v_size_1726_);
v___x_1729_ = lean_nat_dec_lt(v_size_1721_, v___x_1728_);
lean_dec(v___x_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1757_; 
lean_inc(v_r_1725_);
lean_inc(v_l_1724_);
lean_inc(v_v_1723_);
lean_inc(v_k_1722_);
v_isSharedCheck_1757_ = !lean_is_exclusive(v_l_1698_);
if (v_isSharedCheck_1757_ == 0)
{
lean_object* v_unused_1758_; lean_object* v_unused_1759_; lean_object* v_unused_1760_; lean_object* v_unused_1761_; lean_object* v_unused_1762_; 
v_unused_1758_ = lean_ctor_get(v_l_1698_, 4);
lean_dec(v_unused_1758_);
v_unused_1759_ = lean_ctor_get(v_l_1698_, 3);
lean_dec(v_unused_1759_);
v_unused_1760_ = lean_ctor_get(v_l_1698_, 2);
lean_dec(v_unused_1760_);
v_unused_1761_ = lean_ctor_get(v_l_1698_, 1);
lean_dec(v_unused_1761_);
v_unused_1762_ = lean_ctor_get(v_l_1698_, 0);
lean_dec(v_unused_1762_);
v___x_1731_ = v_l_1698_;
v_isShared_1732_ = v_isSharedCheck_1757_;
goto v_resetjp_1730_;
}
else
{
lean_dec(v_l_1698_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1757_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1747_; 
v___x_1733_ = lean_nat_add(v___x_1700_, v_size_1709_);
v___x_1734_ = lean_nat_add(v___x_1733_, v_size_1695_);
lean_dec(v_size_1695_);
if (lean_obj_tag(v_l_1724_) == 0)
{
lean_object* v_size_1755_; 
v_size_1755_ = lean_ctor_get(v_l_1724_, 0);
lean_inc(v_size_1755_);
v___y_1747_ = v_size_1755_;
goto v___jp_1746_;
}
else
{
lean_object* v___x_1756_; 
v___x_1756_ = lean_unsigned_to_nat(0u);
v___y_1747_ = v___x_1756_;
goto v___jp_1746_;
}
v___jp_1735_:
{
lean_object* v___x_1739_; lean_object* v___x_1741_; 
v___x_1739_ = lean_nat_add(v___y_1736_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec(v___y_1736_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 4, v_r_1699_);
lean_ctor_set(v___x_1731_, 3, v_r_1725_);
lean_ctor_set(v___x_1731_, 2, v_v_1697_);
lean_ctor_set(v___x_1731_, 1, v_k_1696_);
lean_ctor_set(v___x_1731_, 0, v___x_1739_);
v___x_1741_ = v___x_1731_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1739_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_k_1696_);
lean_ctor_set(v_reuseFailAlloc_1745_, 2, v_v_1697_);
lean_ctor_set(v_reuseFailAlloc_1745_, 3, v_r_1725_);
lean_ctor_set(v_reuseFailAlloc_1745_, 4, v_r_1699_);
v___x_1741_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1743_; 
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 4, v___x_1741_);
lean_ctor_set(v___x_1719_, 3, v___y_1737_);
lean_ctor_set(v___x_1719_, 2, v_v_1723_);
lean_ctor_set(v___x_1719_, 1, v_k_1722_);
lean_ctor_set(v___x_1719_, 0, v___x_1734_);
v___x_1743_ = v___x_1719_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1734_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_k_1722_);
lean_ctor_set(v_reuseFailAlloc_1744_, 2, v_v_1723_);
lean_ctor_set(v_reuseFailAlloc_1744_, 3, v___y_1737_);
lean_ctor_set(v_reuseFailAlloc_1744_, 4, v___x_1741_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
v___jp_1746_:
{
lean_object* v___x_1748_; lean_object* v___x_1750_; 
v___x_1748_ = lean_nat_add(v___x_1733_, v___y_1747_);
lean_dec(v___y_1747_);
lean_dec(v___x_1733_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 4, v_l_1724_);
lean_ctor_set(v___x_1703_, 3, v_tree_1706_);
lean_ctor_set(v___x_1703_, 2, v_v_1708_);
lean_ctor_set(v___x_1703_, 1, v_k_1707_);
lean_ctor_set(v___x_1703_, 0, v___x_1748_);
v___x_1750_ = v___x_1703_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v___x_1748_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v_k_1707_);
lean_ctor_set(v_reuseFailAlloc_1754_, 2, v_v_1708_);
lean_ctor_set(v_reuseFailAlloc_1754_, 3, v_tree_1706_);
lean_ctor_set(v_reuseFailAlloc_1754_, 4, v_l_1724_);
v___x_1750_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
lean_object* v___x_1751_; 
v___x_1751_ = lean_nat_add(v___x_1700_, v_size_1726_);
if (lean_obj_tag(v_r_1725_) == 0)
{
lean_object* v_size_1752_; 
v_size_1752_ = lean_ctor_get(v_r_1725_, 0);
lean_inc(v_size_1752_);
v___y_1736_ = v___x_1751_;
v___y_1737_ = v___x_1750_;
v___y_1738_ = v_size_1752_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_1753_; 
v___x_1753_ = lean_unsigned_to_nat(0u);
v___y_1736_ = v___x_1751_;
v___y_1737_ = v___x_1750_;
v___y_1738_ = v___x_1753_;
goto v___jp_1735_;
}
}
}
}
}
else
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1767_; 
v___x_1763_ = lean_nat_add(v___x_1700_, v_size_1709_);
v___x_1764_ = lean_nat_add(v___x_1763_, v_size_1695_);
lean_dec(v_size_1695_);
v___x_1765_ = lean_nat_add(v___x_1763_, v_size_1721_);
lean_dec(v___x_1763_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 4, v_l_1698_);
lean_ctor_set(v___x_1719_, 3, v_tree_1706_);
lean_ctor_set(v___x_1719_, 2, v_v_1708_);
lean_ctor_set(v___x_1719_, 1, v_k_1707_);
lean_ctor_set(v___x_1719_, 0, v___x_1765_);
v___x_1767_ = v___x_1719_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1765_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v_k_1707_);
lean_ctor_set(v_reuseFailAlloc_1771_, 2, v_v_1708_);
lean_ctor_set(v_reuseFailAlloc_1771_, 3, v_tree_1706_);
lean_ctor_set(v_reuseFailAlloc_1771_, 4, v_l_1698_);
v___x_1767_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
lean_object* v___x_1769_; 
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 4, v_r_1699_);
lean_ctor_set(v___x_1703_, 3, v___x_1767_);
lean_ctor_set(v___x_1703_, 2, v_v_1697_);
lean_ctor_set(v___x_1703_, 1, v_k_1696_);
lean_ctor_set(v___x_1703_, 0, v___x_1764_);
v___x_1769_ = v___x_1703_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1764_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_k_1696_);
lean_ctor_set(v_reuseFailAlloc_1770_, 2, v_v_1697_);
lean_ctor_set(v_reuseFailAlloc_1770_, 3, v___x_1767_);
lean_ctor_set(v_reuseFailAlloc_1770_, 4, v_r_1699_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
}
}
else
{
lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1831_; 
lean_inc(v_r_1699_);
lean_inc(v_v_1697_);
lean_inc(v_k_1696_);
lean_inc(v_size_1695_);
v_isSharedCheck_1831_ = !lean_is_exclusive(v_r_1511_);
if (v_isSharedCheck_1831_ == 0)
{
lean_object* v_unused_1832_; lean_object* v_unused_1833_; lean_object* v_unused_1834_; lean_object* v_unused_1835_; lean_object* v_unused_1836_; 
v_unused_1832_ = lean_ctor_get(v_r_1511_, 4);
lean_dec(v_unused_1832_);
v_unused_1833_ = lean_ctor_get(v_r_1511_, 3);
lean_dec(v_unused_1833_);
v_unused_1834_ = lean_ctor_get(v_r_1511_, 2);
lean_dec(v_unused_1834_);
v_unused_1835_ = lean_ctor_get(v_r_1511_, 1);
lean_dec(v_unused_1835_);
v_unused_1836_ = lean_ctor_get(v_r_1511_, 0);
lean_dec(v_unused_1836_);
v___x_1779_ = v_r_1511_;
v_isShared_1780_ = v_isSharedCheck_1831_;
goto v_resetjp_1778_;
}
else
{
lean_dec(v_r_1511_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1831_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
if (lean_obj_tag(v_l_1698_) == 0)
{
if (lean_obj_tag(v_r_1699_) == 0)
{
lean_object* v_k_1781_; lean_object* v_v_1782_; lean_object* v_size_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1787_; 
lean_inc(v_tree_1706_);
v_k_1781_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_k_1781_);
v_v_1782_ = lean_ctor_get(v___x_1705_, 1);
lean_inc(v_v_1782_);
lean_dec_ref(v___x_1705_);
v_size_1783_ = lean_ctor_get(v_l_1698_, 0);
v___x_1784_ = lean_nat_add(v___x_1700_, v_size_1695_);
lean_dec(v_size_1695_);
v___x_1785_ = lean_nat_add(v___x_1700_, v_size_1783_);
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 4, v_l_1698_);
lean_ctor_set(v___x_1779_, 3, v_tree_1706_);
lean_ctor_set(v___x_1779_, 2, v_v_1782_);
lean_ctor_set(v___x_1779_, 1, v_k_1781_);
lean_ctor_set(v___x_1779_, 0, v___x_1785_);
v___x_1787_ = v___x_1779_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1785_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_k_1781_);
lean_ctor_set(v_reuseFailAlloc_1791_, 2, v_v_1782_);
lean_ctor_set(v_reuseFailAlloc_1791_, 3, v_tree_1706_);
lean_ctor_set(v_reuseFailAlloc_1791_, 4, v_l_1698_);
v___x_1787_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
lean_object* v___x_1789_; 
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 4, v_r_1699_);
lean_ctor_set(v___x_1703_, 3, v___x_1787_);
lean_ctor_set(v___x_1703_, 2, v_v_1697_);
lean_ctor_set(v___x_1703_, 1, v_k_1696_);
lean_ctor_set(v___x_1703_, 0, v___x_1784_);
v___x_1789_ = v___x_1703_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1784_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_k_1696_);
lean_ctor_set(v_reuseFailAlloc_1790_, 2, v_v_1697_);
lean_ctor_set(v_reuseFailAlloc_1790_, 3, v___x_1787_);
lean_ctor_set(v_reuseFailAlloc_1790_, 4, v_r_1699_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
else
{
lean_object* v_k_1792_; lean_object* v_v_1793_; lean_object* v_k_1794_; lean_object* v_v_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1809_; 
lean_dec(v_size_1695_);
v_k_1792_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_k_1792_);
v_v_1793_ = lean_ctor_get(v___x_1705_, 1);
lean_inc(v_v_1793_);
lean_dec_ref(v___x_1705_);
v_k_1794_ = lean_ctor_get(v_l_1698_, 1);
v_v_1795_ = lean_ctor_get(v_l_1698_, 2);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_l_1698_);
if (v_isSharedCheck_1809_ == 0)
{
lean_object* v_unused_1810_; lean_object* v_unused_1811_; lean_object* v_unused_1812_; 
v_unused_1810_ = lean_ctor_get(v_l_1698_, 4);
lean_dec(v_unused_1810_);
v_unused_1811_ = lean_ctor_get(v_l_1698_, 3);
lean_dec(v_unused_1811_);
v_unused_1812_ = lean_ctor_get(v_l_1698_, 0);
lean_dec(v_unused_1812_);
v___x_1797_ = v_l_1698_;
v_isShared_1798_ = v_isSharedCheck_1809_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_v_1795_);
lean_inc(v_k_1794_);
lean_dec(v_l_1698_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1809_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1799_; lean_object* v___x_1801_; 
v___x_1799_ = lean_unsigned_to_nat(3u);
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 4, v_r_1699_);
lean_ctor_set(v___x_1797_, 3, v_r_1699_);
lean_ctor_set(v___x_1797_, 2, v_v_1793_);
lean_ctor_set(v___x_1797_, 1, v_k_1792_);
lean_ctor_set(v___x_1797_, 0, v___x_1700_);
v___x_1801_ = v___x_1797_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1700_);
lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_k_1792_);
lean_ctor_set(v_reuseFailAlloc_1808_, 2, v_v_1793_);
lean_ctor_set(v_reuseFailAlloc_1808_, 3, v_r_1699_);
lean_ctor_set(v_reuseFailAlloc_1808_, 4, v_r_1699_);
v___x_1801_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
lean_object* v___x_1803_; 
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 3, v_r_1699_);
lean_ctor_set(v___x_1779_, 0, v___x_1700_);
v___x_1803_ = v___x_1779_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1700_);
lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_k_1696_);
lean_ctor_set(v_reuseFailAlloc_1807_, 2, v_v_1697_);
lean_ctor_set(v_reuseFailAlloc_1807_, 3, v_r_1699_);
lean_ctor_set(v_reuseFailAlloc_1807_, 4, v_r_1699_);
v___x_1803_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
lean_object* v___x_1805_; 
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 4, v___x_1803_);
lean_ctor_set(v___x_1703_, 3, v___x_1801_);
lean_ctor_set(v___x_1703_, 2, v_v_1795_);
lean_ctor_set(v___x_1703_, 1, v_k_1794_);
lean_ctor_set(v___x_1703_, 0, v___x_1799_);
v___x_1805_ = v___x_1703_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1799_);
lean_ctor_set(v_reuseFailAlloc_1806_, 1, v_k_1794_);
lean_ctor_set(v_reuseFailAlloc_1806_, 2, v_v_1795_);
lean_ctor_set(v_reuseFailAlloc_1806_, 3, v___x_1801_);
lean_ctor_set(v_reuseFailAlloc_1806_, 4, v___x_1803_);
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
}
}
else
{
if (lean_obj_tag(v_r_1699_) == 0)
{
lean_object* v_k_1813_; lean_object* v_v_1814_; lean_object* v___x_1815_; lean_object* v___x_1817_; 
lean_dec(v_size_1695_);
v_k_1813_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_k_1813_);
v_v_1814_ = lean_ctor_get(v___x_1705_, 1);
lean_inc(v_v_1814_);
lean_dec_ref(v___x_1705_);
v___x_1815_ = lean_unsigned_to_nat(3u);
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 4, v_l_1698_);
lean_ctor_set(v___x_1779_, 2, v_v_1814_);
lean_ctor_set(v___x_1779_, 1, v_k_1813_);
lean_ctor_set(v___x_1779_, 0, v___x_1700_);
v___x_1817_ = v___x_1779_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1700_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v_k_1813_);
lean_ctor_set(v_reuseFailAlloc_1821_, 2, v_v_1814_);
lean_ctor_set(v_reuseFailAlloc_1821_, 3, v_l_1698_);
lean_ctor_set(v_reuseFailAlloc_1821_, 4, v_l_1698_);
v___x_1817_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
lean_object* v___x_1819_; 
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 4, v_r_1699_);
lean_ctor_set(v___x_1703_, 3, v___x_1817_);
lean_ctor_set(v___x_1703_, 2, v_v_1697_);
lean_ctor_set(v___x_1703_, 1, v_k_1696_);
lean_ctor_set(v___x_1703_, 0, v___x_1815_);
v___x_1819_ = v___x_1703_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1815_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v_k_1696_);
lean_ctor_set(v_reuseFailAlloc_1820_, 2, v_v_1697_);
lean_ctor_set(v_reuseFailAlloc_1820_, 3, v___x_1817_);
lean_ctor_set(v_reuseFailAlloc_1820_, 4, v_r_1699_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
else
{
lean_object* v_k_1822_; lean_object* v_v_1823_; lean_object* v___x_1825_; 
v_k_1822_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_k_1822_);
v_v_1823_ = lean_ctor_get(v___x_1705_, 1);
lean_inc(v_v_1823_);
lean_dec_ref(v___x_1705_);
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 3, v_r_1699_);
v___x_1825_ = v___x_1779_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_size_1695_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v_k_1696_);
lean_ctor_set(v_reuseFailAlloc_1830_, 2, v_v_1697_);
lean_ctor_set(v_reuseFailAlloc_1830_, 3, v_r_1699_);
lean_ctor_set(v_reuseFailAlloc_1830_, 4, v_r_1699_);
v___x_1825_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
lean_object* v___x_1826_; lean_object* v___x_1828_; 
v___x_1826_ = lean_unsigned_to_nat(2u);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 4, v___x_1825_);
lean_ctor_set(v___x_1703_, 3, v_r_1699_);
lean_ctor_set(v___x_1703_, 2, v_v_1823_);
lean_ctor_set(v___x_1703_, 1, v_k_1822_);
lean_ctor_set(v___x_1703_, 0, v___x_1826_);
v___x_1828_ = v___x_1703_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1826_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_k_1822_);
lean_ctor_set(v_reuseFailAlloc_1829_, 2, v_v_1823_);
lean_ctor_set(v_reuseFailAlloc_1829_, 3, v_r_1699_);
lean_ctor_set(v_reuseFailAlloc_1829_, 4, v___x_1825_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
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
lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1995_; 
lean_inc(v_r_1699_);
lean_inc(v_v_1697_);
lean_inc(v_k_1696_);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_r_1511_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; lean_object* v_unused_1997_; lean_object* v_unused_1998_; lean_object* v_unused_1999_; lean_object* v_unused_2000_; 
v_unused_1996_ = lean_ctor_get(v_r_1511_, 4);
lean_dec(v_unused_1996_);
v_unused_1997_ = lean_ctor_get(v_r_1511_, 3);
lean_dec(v_unused_1997_);
v_unused_1998_ = lean_ctor_get(v_r_1511_, 2);
lean_dec(v_unused_1998_);
v_unused_1999_ = lean_ctor_get(v_r_1511_, 1);
lean_dec(v_unused_1999_);
v_unused_2000_ = lean_ctor_get(v_r_1511_, 0);
lean_dec(v_unused_2000_);
v___x_1844_ = v_r_1511_;
v_isShared_1845_ = v_isSharedCheck_1995_;
goto v_resetjp_1843_;
}
else
{
lean_dec(v_r_1511_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1995_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1846_; lean_object* v_tree_1847_; 
v___x_1846_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1696_, v_v_1697_, v_l_1698_, v_r_1699_);
v_tree_1847_ = lean_ctor_get(v___x_1846_, 2);
lean_inc(v_tree_1847_);
if (lean_obj_tag(v_tree_1847_) == 0)
{
lean_object* v_k_1848_; lean_object* v_v_1849_; lean_object* v_size_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; uint8_t v___x_1853_; 
v_k_1848_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_k_1848_);
v_v_1849_ = lean_ctor_get(v___x_1846_, 1);
lean_inc(v_v_1849_);
lean_dec_ref(v___x_1846_);
v_size_1850_ = lean_ctor_get(v_tree_1847_, 0);
v___x_1851_ = lean_unsigned_to_nat(3u);
v___x_1852_ = lean_nat_mul(v___x_1851_, v_size_1850_);
v___x_1853_ = lean_nat_dec_lt(v___x_1852_, v_size_1690_);
lean_dec(v___x_1852_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1857_; 
lean_dec(v_r_1694_);
v___x_1854_ = lean_nat_add(v___x_1700_, v_size_1690_);
v___x_1855_ = lean_nat_add(v___x_1854_, v_size_1850_);
lean_dec(v___x_1854_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 4, v_tree_1847_);
lean_ctor_set(v___x_1844_, 3, v_l_1510_);
lean_ctor_set(v___x_1844_, 2, v_v_1849_);
lean_ctor_set(v___x_1844_, 1, v_k_1848_);
lean_ctor_set(v___x_1844_, 0, v___x_1855_);
v___x_1857_ = v___x_1844_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_k_1848_);
lean_ctor_set(v_reuseFailAlloc_1858_, 2, v_v_1849_);
lean_ctor_set(v_reuseFailAlloc_1858_, 3, v_l_1510_);
lean_ctor_set(v_reuseFailAlloc_1858_, 4, v_tree_1847_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
else
{
lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1924_; 
lean_inc(v_l_1693_);
lean_inc(v_v_1692_);
lean_inc(v_k_1691_);
lean_inc(v_size_1690_);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_l_1510_);
if (v_isSharedCheck_1924_ == 0)
{
lean_object* v_unused_1925_; lean_object* v_unused_1926_; lean_object* v_unused_1927_; lean_object* v_unused_1928_; lean_object* v_unused_1929_; 
v_unused_1925_ = lean_ctor_get(v_l_1510_, 4);
lean_dec(v_unused_1925_);
v_unused_1926_ = lean_ctor_get(v_l_1510_, 3);
lean_dec(v_unused_1926_);
v_unused_1927_ = lean_ctor_get(v_l_1510_, 2);
lean_dec(v_unused_1927_);
v_unused_1928_ = lean_ctor_get(v_l_1510_, 1);
lean_dec(v_unused_1928_);
v_unused_1929_ = lean_ctor_get(v_l_1510_, 0);
lean_dec(v_unused_1929_);
v___x_1860_ = v_l_1510_;
v_isShared_1861_ = v_isSharedCheck_1924_;
goto v_resetjp_1859_;
}
else
{
lean_dec(v_l_1510_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1924_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v_size_1862_; lean_object* v_size_1863_; lean_object* v_k_1864_; lean_object* v_v_1865_; lean_object* v_l_1866_; lean_object* v_r_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; uint8_t v___x_1870_; 
v_size_1862_ = lean_ctor_get(v_l_1693_, 0);
v_size_1863_ = lean_ctor_get(v_r_1694_, 0);
v_k_1864_ = lean_ctor_get(v_r_1694_, 1);
v_v_1865_ = lean_ctor_get(v_r_1694_, 2);
v_l_1866_ = lean_ctor_get(v_r_1694_, 3);
v_r_1867_ = lean_ctor_get(v_r_1694_, 4);
v___x_1868_ = lean_unsigned_to_nat(2u);
v___x_1869_ = lean_nat_mul(v___x_1868_, v_size_1862_);
v___x_1870_ = lean_nat_dec_lt(v_size_1863_, v___x_1869_);
lean_dec(v___x_1869_);
if (v___x_1870_ == 0)
{
lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1908_; 
lean_inc(v_r_1867_);
lean_inc(v_l_1866_);
lean_inc(v_v_1865_);
lean_inc(v_k_1864_);
lean_del_object(v___x_1860_);
v_isSharedCheck_1908_ = !lean_is_exclusive(v_r_1694_);
if (v_isSharedCheck_1908_ == 0)
{
lean_object* v_unused_1909_; lean_object* v_unused_1910_; lean_object* v_unused_1911_; lean_object* v_unused_1912_; lean_object* v_unused_1913_; 
v_unused_1909_ = lean_ctor_get(v_r_1694_, 4);
lean_dec(v_unused_1909_);
v_unused_1910_ = lean_ctor_get(v_r_1694_, 3);
lean_dec(v_unused_1910_);
v_unused_1911_ = lean_ctor_get(v_r_1694_, 2);
lean_dec(v_unused_1911_);
v_unused_1912_ = lean_ctor_get(v_r_1694_, 1);
lean_dec(v_unused_1912_);
v_unused_1913_ = lean_ctor_get(v_r_1694_, 0);
lean_dec(v_unused_1913_);
v___x_1872_ = v_r_1694_;
v_isShared_1873_ = v_isSharedCheck_1908_;
goto v_resetjp_1871_;
}
else
{
lean_dec(v_r_1694_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1908_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___x_1896_; lean_object* v___y_1898_; 
v___x_1874_ = lean_nat_add(v___x_1700_, v_size_1690_);
lean_dec(v_size_1690_);
v___x_1875_ = lean_nat_add(v___x_1874_, v_size_1850_);
lean_dec(v___x_1874_);
v___x_1896_ = lean_nat_add(v___x_1700_, v_size_1862_);
if (lean_obj_tag(v_l_1866_) == 0)
{
lean_object* v_size_1906_; 
v_size_1906_ = lean_ctor_get(v_l_1866_, 0);
lean_inc(v_size_1906_);
v___y_1898_ = v_size_1906_;
goto v___jp_1897_;
}
else
{
lean_object* v___x_1907_; 
v___x_1907_ = lean_unsigned_to_nat(0u);
v___y_1898_ = v___x_1907_;
goto v___jp_1897_;
}
v___jp_1876_:
{
lean_object* v___x_1880_; lean_object* v___x_1882_; 
v___x_1880_ = lean_nat_add(v___y_1878_, v___y_1879_);
lean_dec(v___y_1879_);
lean_dec(v___y_1878_);
lean_inc_ref(v_tree_1847_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 4, v_tree_1847_);
lean_ctor_set(v___x_1872_, 3, v_r_1867_);
lean_ctor_set(v___x_1872_, 2, v_v_1849_);
lean_ctor_set(v___x_1872_, 1, v_k_1848_);
lean_ctor_set(v___x_1872_, 0, v___x_1880_);
v___x_1882_ = v___x_1872_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1880_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v_k_1848_);
lean_ctor_set(v_reuseFailAlloc_1895_, 2, v_v_1849_);
lean_ctor_set(v_reuseFailAlloc_1895_, 3, v_r_1867_);
lean_ctor_set(v_reuseFailAlloc_1895_, 4, v_tree_1847_);
v___x_1882_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
v_isSharedCheck_1889_ = !lean_is_exclusive(v_tree_1847_);
if (v_isSharedCheck_1889_ == 0)
{
lean_object* v_unused_1890_; lean_object* v_unused_1891_; lean_object* v_unused_1892_; lean_object* v_unused_1893_; lean_object* v_unused_1894_; 
v_unused_1890_ = lean_ctor_get(v_tree_1847_, 4);
lean_dec(v_unused_1890_);
v_unused_1891_ = lean_ctor_get(v_tree_1847_, 3);
lean_dec(v_unused_1891_);
v_unused_1892_ = lean_ctor_get(v_tree_1847_, 2);
lean_dec(v_unused_1892_);
v_unused_1893_ = lean_ctor_get(v_tree_1847_, 1);
lean_dec(v_unused_1893_);
v_unused_1894_ = lean_ctor_get(v_tree_1847_, 0);
lean_dec(v_unused_1894_);
v___x_1884_ = v_tree_1847_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_dec(v_tree_1847_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 4, v___x_1882_);
lean_ctor_set(v___x_1884_, 3, v___y_1877_);
lean_ctor_set(v___x_1884_, 2, v_v_1865_);
lean_ctor_set(v___x_1884_, 1, v_k_1864_);
lean_ctor_set(v___x_1884_, 0, v___x_1875_);
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1875_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_k_1864_);
lean_ctor_set(v_reuseFailAlloc_1888_, 2, v_v_1865_);
lean_ctor_set(v_reuseFailAlloc_1888_, 3, v___y_1877_);
lean_ctor_set(v_reuseFailAlloc_1888_, 4, v___x_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
v___jp_1897_:
{
lean_object* v___x_1899_; lean_object* v___x_1901_; 
v___x_1899_ = lean_nat_add(v___x_1896_, v___y_1898_);
lean_dec(v___y_1898_);
lean_dec(v___x_1896_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 4, v_l_1866_);
lean_ctor_set(v___x_1844_, 3, v_l_1693_);
lean_ctor_set(v___x_1844_, 2, v_v_1692_);
lean_ctor_set(v___x_1844_, 1, v_k_1691_);
lean_ctor_set(v___x_1844_, 0, v___x_1899_);
v___x_1901_ = v___x_1844_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v___x_1899_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v_k_1691_);
lean_ctor_set(v_reuseFailAlloc_1905_, 2, v_v_1692_);
lean_ctor_set(v_reuseFailAlloc_1905_, 3, v_l_1693_);
lean_ctor_set(v_reuseFailAlloc_1905_, 4, v_l_1866_);
v___x_1901_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
lean_object* v___x_1902_; 
v___x_1902_ = lean_nat_add(v___x_1700_, v_size_1850_);
if (lean_obj_tag(v_r_1867_) == 0)
{
lean_object* v_size_1903_; 
v_size_1903_ = lean_ctor_get(v_r_1867_, 0);
lean_inc(v_size_1903_);
v___y_1877_ = v___x_1901_;
v___y_1878_ = v___x_1902_;
v___y_1879_ = v_size_1903_;
goto v___jp_1876_;
}
else
{
lean_object* v___x_1904_; 
v___x_1904_ = lean_unsigned_to_nat(0u);
v___y_1877_ = v___x_1901_;
v___y_1878_ = v___x_1902_;
v___y_1879_ = v___x_1904_;
goto v___jp_1876_;
}
}
}
}
}
else
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1919_; 
v___x_1914_ = lean_nat_add(v___x_1700_, v_size_1690_);
lean_dec(v_size_1690_);
v___x_1915_ = lean_nat_add(v___x_1914_, v_size_1850_);
lean_dec(v___x_1914_);
v___x_1916_ = lean_nat_add(v___x_1700_, v_size_1850_);
v___x_1917_ = lean_nat_add(v___x_1916_, v_size_1863_);
lean_dec(v___x_1916_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 4, v_tree_1847_);
lean_ctor_set(v___x_1844_, 3, v_r_1694_);
lean_ctor_set(v___x_1844_, 2, v_v_1849_);
lean_ctor_set(v___x_1844_, 1, v_k_1848_);
lean_ctor_set(v___x_1844_, 0, v___x_1917_);
v___x_1919_ = v___x_1844_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1917_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v_k_1848_);
lean_ctor_set(v_reuseFailAlloc_1923_, 2, v_v_1849_);
lean_ctor_set(v_reuseFailAlloc_1923_, 3, v_r_1694_);
lean_ctor_set(v_reuseFailAlloc_1923_, 4, v_tree_1847_);
v___x_1919_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
lean_object* v___x_1921_; 
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 4, v___x_1919_);
lean_ctor_set(v___x_1860_, 0, v___x_1915_);
v___x_1921_ = v___x_1860_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1915_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v_k_1691_);
lean_ctor_set(v_reuseFailAlloc_1922_, 2, v_v_1692_);
lean_ctor_set(v_reuseFailAlloc_1922_, 3, v_l_1693_);
lean_ctor_set(v_reuseFailAlloc_1922_, 4, v___x_1919_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1693_) == 0)
{
lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1953_; 
lean_inc_ref(v_l_1693_);
lean_inc(v_v_1692_);
lean_inc(v_k_1691_);
lean_inc(v_size_1690_);
v_isSharedCheck_1953_ = !lean_is_exclusive(v_l_1510_);
if (v_isSharedCheck_1953_ == 0)
{
lean_object* v_unused_1954_; lean_object* v_unused_1955_; lean_object* v_unused_1956_; lean_object* v_unused_1957_; lean_object* v_unused_1958_; 
v_unused_1954_ = lean_ctor_get(v_l_1510_, 4);
lean_dec(v_unused_1954_);
v_unused_1955_ = lean_ctor_get(v_l_1510_, 3);
lean_dec(v_unused_1955_);
v_unused_1956_ = lean_ctor_get(v_l_1510_, 2);
lean_dec(v_unused_1956_);
v_unused_1957_ = lean_ctor_get(v_l_1510_, 1);
lean_dec(v_unused_1957_);
v_unused_1958_ = lean_ctor_get(v_l_1510_, 0);
lean_dec(v_unused_1958_);
v___x_1931_ = v_l_1510_;
v_isShared_1932_ = v_isSharedCheck_1953_;
goto v_resetjp_1930_;
}
else
{
lean_dec(v_l_1510_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1953_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
if (lean_obj_tag(v_r_1694_) == 0)
{
lean_object* v_k_1933_; lean_object* v_v_1934_; lean_object* v_size_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1939_; 
v_k_1933_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_k_1933_);
v_v_1934_ = lean_ctor_get(v___x_1846_, 1);
lean_inc(v_v_1934_);
lean_dec_ref(v___x_1846_);
v_size_1935_ = lean_ctor_get(v_r_1694_, 0);
v___x_1936_ = lean_nat_add(v___x_1700_, v_size_1690_);
lean_dec(v_size_1690_);
v___x_1937_ = lean_nat_add(v___x_1700_, v_size_1935_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 4, v_tree_1847_);
lean_ctor_set(v___x_1844_, 3, v_r_1694_);
lean_ctor_set(v___x_1844_, 2, v_v_1934_);
lean_ctor_set(v___x_1844_, 1, v_k_1933_);
lean_ctor_set(v___x_1844_, 0, v___x_1937_);
v___x_1939_ = v___x_1844_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1937_);
lean_ctor_set(v_reuseFailAlloc_1943_, 1, v_k_1933_);
lean_ctor_set(v_reuseFailAlloc_1943_, 2, v_v_1934_);
lean_ctor_set(v_reuseFailAlloc_1943_, 3, v_r_1694_);
lean_ctor_set(v_reuseFailAlloc_1943_, 4, v_tree_1847_);
v___x_1939_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
lean_object* v___x_1941_; 
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 4, v___x_1939_);
lean_ctor_set(v___x_1931_, 0, v___x_1936_);
v___x_1941_ = v___x_1931_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1936_);
lean_ctor_set(v_reuseFailAlloc_1942_, 1, v_k_1691_);
lean_ctor_set(v_reuseFailAlloc_1942_, 2, v_v_1692_);
lean_ctor_set(v_reuseFailAlloc_1942_, 3, v_l_1693_);
lean_ctor_set(v_reuseFailAlloc_1942_, 4, v___x_1939_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
else
{
lean_object* v_k_1944_; lean_object* v_v_1945_; lean_object* v___x_1946_; lean_object* v___x_1948_; 
lean_dec(v_size_1690_);
v_k_1944_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_k_1944_);
v_v_1945_ = lean_ctor_get(v___x_1846_, 1);
lean_inc(v_v_1945_);
lean_dec_ref(v___x_1846_);
v___x_1946_ = lean_unsigned_to_nat(3u);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 4, v_r_1694_);
lean_ctor_set(v___x_1844_, 3, v_r_1694_);
lean_ctor_set(v___x_1844_, 2, v_v_1945_);
lean_ctor_set(v___x_1844_, 1, v_k_1944_);
lean_ctor_set(v___x_1844_, 0, v___x_1700_);
v___x_1948_ = v___x_1844_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v___x_1700_);
lean_ctor_set(v_reuseFailAlloc_1952_, 1, v_k_1944_);
lean_ctor_set(v_reuseFailAlloc_1952_, 2, v_v_1945_);
lean_ctor_set(v_reuseFailAlloc_1952_, 3, v_r_1694_);
lean_ctor_set(v_reuseFailAlloc_1952_, 4, v_r_1694_);
v___x_1948_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
lean_object* v___x_1950_; 
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 4, v___x_1948_);
lean_ctor_set(v___x_1931_, 0, v___x_1946_);
v___x_1950_ = v___x_1931_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v___x_1946_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_k_1691_);
lean_ctor_set(v_reuseFailAlloc_1951_, 2, v_v_1692_);
lean_ctor_set(v_reuseFailAlloc_1951_, 3, v_l_1693_);
lean_ctor_set(v_reuseFailAlloc_1951_, 4, v___x_1948_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1694_) == 0)
{
lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1983_; 
lean_inc(v_l_1693_);
lean_inc(v_v_1692_);
lean_inc(v_k_1691_);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_l_1510_);
if (v_isSharedCheck_1983_ == 0)
{
lean_object* v_unused_1984_; lean_object* v_unused_1985_; lean_object* v_unused_1986_; lean_object* v_unused_1987_; lean_object* v_unused_1988_; 
v_unused_1984_ = lean_ctor_get(v_l_1510_, 4);
lean_dec(v_unused_1984_);
v_unused_1985_ = lean_ctor_get(v_l_1510_, 3);
lean_dec(v_unused_1985_);
v_unused_1986_ = lean_ctor_get(v_l_1510_, 2);
lean_dec(v_unused_1986_);
v_unused_1987_ = lean_ctor_get(v_l_1510_, 1);
lean_dec(v_unused_1987_);
v_unused_1988_ = lean_ctor_get(v_l_1510_, 0);
lean_dec(v_unused_1988_);
v___x_1960_ = v_l_1510_;
v_isShared_1961_ = v_isSharedCheck_1983_;
goto v_resetjp_1959_;
}
else
{
lean_dec(v_l_1510_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1983_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v_k_1962_; lean_object* v_v_1963_; lean_object* v_k_1964_; lean_object* v_v_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1979_; 
v_k_1962_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_k_1962_);
v_v_1963_ = lean_ctor_get(v___x_1846_, 1);
lean_inc(v_v_1963_);
lean_dec_ref(v___x_1846_);
v_k_1964_ = lean_ctor_get(v_r_1694_, 1);
v_v_1965_ = lean_ctor_get(v_r_1694_, 2);
v_isSharedCheck_1979_ = !lean_is_exclusive(v_r_1694_);
if (v_isSharedCheck_1979_ == 0)
{
lean_object* v_unused_1980_; lean_object* v_unused_1981_; lean_object* v_unused_1982_; 
v_unused_1980_ = lean_ctor_get(v_r_1694_, 4);
lean_dec(v_unused_1980_);
v_unused_1981_ = lean_ctor_get(v_r_1694_, 3);
lean_dec(v_unused_1981_);
v_unused_1982_ = lean_ctor_get(v_r_1694_, 0);
lean_dec(v_unused_1982_);
v___x_1967_ = v_r_1694_;
v_isShared_1968_ = v_isSharedCheck_1979_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_v_1965_);
lean_inc(v_k_1964_);
lean_dec(v_r_1694_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1979_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1969_; lean_object* v___x_1971_; 
v___x_1969_ = lean_unsigned_to_nat(3u);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 4, v_l_1693_);
lean_ctor_set(v___x_1967_, 3, v_l_1693_);
lean_ctor_set(v___x_1967_, 2, v_v_1692_);
lean_ctor_set(v___x_1967_, 1, v_k_1691_);
lean_ctor_set(v___x_1967_, 0, v___x_1700_);
v___x_1971_ = v___x_1967_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1700_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v_k_1691_);
lean_ctor_set(v_reuseFailAlloc_1978_, 2, v_v_1692_);
lean_ctor_set(v_reuseFailAlloc_1978_, 3, v_l_1693_);
lean_ctor_set(v_reuseFailAlloc_1978_, 4, v_l_1693_);
v___x_1971_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
lean_object* v___x_1973_; 
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 4, v_l_1693_);
lean_ctor_set(v___x_1844_, 3, v_l_1693_);
lean_ctor_set(v___x_1844_, 2, v_v_1963_);
lean_ctor_set(v___x_1844_, 1, v_k_1962_);
lean_ctor_set(v___x_1844_, 0, v___x_1700_);
v___x_1973_ = v___x_1844_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1700_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v_k_1962_);
lean_ctor_set(v_reuseFailAlloc_1977_, 2, v_v_1963_);
lean_ctor_set(v_reuseFailAlloc_1977_, 3, v_l_1693_);
lean_ctor_set(v_reuseFailAlloc_1977_, 4, v_l_1693_);
v___x_1973_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
lean_object* v___x_1975_; 
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 4, v___x_1973_);
lean_ctor_set(v___x_1960_, 3, v___x_1971_);
lean_ctor_set(v___x_1960_, 2, v_v_1965_);
lean_ctor_set(v___x_1960_, 1, v_k_1964_);
lean_ctor_set(v___x_1960_, 0, v___x_1969_);
v___x_1975_ = v___x_1960_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v___x_1969_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v_k_1964_);
lean_ctor_set(v_reuseFailAlloc_1976_, 2, v_v_1965_);
lean_ctor_set(v_reuseFailAlloc_1976_, 3, v___x_1971_);
lean_ctor_set(v_reuseFailAlloc_1976_, 4, v___x_1973_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
}
}
else
{
lean_object* v_k_1989_; lean_object* v_v_1990_; lean_object* v___x_1991_; lean_object* v___x_1993_; 
v_k_1989_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_k_1989_);
v_v_1990_ = lean_ctor_get(v___x_1846_, 1);
lean_inc(v_v_1990_);
lean_dec_ref(v___x_1846_);
v___x_1991_ = lean_unsigned_to_nat(2u);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 4, v_r_1694_);
lean_ctor_set(v___x_1844_, 3, v_l_1510_);
lean_ctor_set(v___x_1844_, 2, v_v_1990_);
lean_ctor_set(v___x_1844_, 1, v_k_1989_);
lean_ctor_set(v___x_1844_, 0, v___x_1991_);
v___x_1993_ = v___x_1844_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1991_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_k_1989_);
lean_ctor_set(v_reuseFailAlloc_1994_, 2, v_v_1990_);
lean_ctor_set(v_reuseFailAlloc_1994_, 3, v_l_1510_);
lean_ctor_set(v_reuseFailAlloc_1994_, 4, v_r_1694_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
}
}
}
else
{
return v_l_1510_;
}
}
else
{
return v_r_1511_;
}
}
default: 
{
lean_object* v_impl_2001_; lean_object* v___x_2002_; 
v_impl_2001_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1506_, v_r_1511_);
v___x_2002_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2001_) == 0)
{
if (lean_obj_tag(v_l_1510_) == 0)
{
lean_object* v_size_2003_; lean_object* v_size_2004_; lean_object* v_k_2005_; lean_object* v_v_2006_; lean_object* v_l_2007_; lean_object* v_r_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; uint8_t v___x_2011_; 
v_size_2003_ = lean_ctor_get(v_impl_2001_, 0);
v_size_2004_ = lean_ctor_get(v_l_1510_, 0);
v_k_2005_ = lean_ctor_get(v_l_1510_, 1);
v_v_2006_ = lean_ctor_get(v_l_1510_, 2);
v_l_2007_ = lean_ctor_get(v_l_1510_, 3);
v_r_2008_ = lean_ctor_get(v_l_1510_, 4);
lean_inc(v_r_2008_);
v___x_2009_ = lean_unsigned_to_nat(3u);
v___x_2010_ = lean_nat_mul(v___x_2009_, v_size_2003_);
v___x_2011_ = lean_nat_dec_lt(v___x_2010_, v_size_2004_);
lean_dec(v___x_2010_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2015_; 
lean_dec(v_r_2008_);
v___x_2012_ = lean_nat_add(v___x_2002_, v_size_2004_);
v___x_2013_ = lean_nat_add(v___x_2012_, v_size_2003_);
lean_dec(v___x_2012_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 4, v_impl_2001_);
lean_ctor_set(v___x_1513_, 0, v___x_2013_);
v___x_2015_ = v___x_1513_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2013_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_k_1508_);
lean_ctor_set(v_reuseFailAlloc_2016_, 2, v_v_1509_);
lean_ctor_set(v_reuseFailAlloc_2016_, 3, v_l_1510_);
lean_ctor_set(v_reuseFailAlloc_2016_, 4, v_impl_2001_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
else
{
lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2082_; 
lean_inc(v_l_2007_);
lean_inc(v_v_2006_);
lean_inc(v_k_2005_);
lean_inc(v_size_2004_);
v_isSharedCheck_2082_ = !lean_is_exclusive(v_l_1510_);
if (v_isSharedCheck_2082_ == 0)
{
lean_object* v_unused_2083_; lean_object* v_unused_2084_; lean_object* v_unused_2085_; lean_object* v_unused_2086_; lean_object* v_unused_2087_; 
v_unused_2083_ = lean_ctor_get(v_l_1510_, 4);
lean_dec(v_unused_2083_);
v_unused_2084_ = lean_ctor_get(v_l_1510_, 3);
lean_dec(v_unused_2084_);
v_unused_2085_ = lean_ctor_get(v_l_1510_, 2);
lean_dec(v_unused_2085_);
v_unused_2086_ = lean_ctor_get(v_l_1510_, 1);
lean_dec(v_unused_2086_);
v_unused_2087_ = lean_ctor_get(v_l_1510_, 0);
lean_dec(v_unused_2087_);
v___x_2018_ = v_l_1510_;
v_isShared_2019_ = v_isSharedCheck_2082_;
goto v_resetjp_2017_;
}
else
{
lean_dec(v_l_1510_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2082_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v_size_2020_; lean_object* v_size_2021_; lean_object* v_k_2022_; lean_object* v_v_2023_; lean_object* v_l_2024_; lean_object* v_r_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; uint8_t v___x_2028_; 
v_size_2020_ = lean_ctor_get(v_l_2007_, 0);
v_size_2021_ = lean_ctor_get(v_r_2008_, 0);
v_k_2022_ = lean_ctor_get(v_r_2008_, 1);
v_v_2023_ = lean_ctor_get(v_r_2008_, 2);
v_l_2024_ = lean_ctor_get(v_r_2008_, 3);
v_r_2025_ = lean_ctor_get(v_r_2008_, 4);
v___x_2026_ = lean_unsigned_to_nat(2u);
v___x_2027_ = lean_nat_mul(v___x_2026_, v_size_2020_);
v___x_2028_ = lean_nat_dec_lt(v_size_2021_, v___x_2027_);
lean_dec(v___x_2027_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2057_; 
lean_inc(v_r_2025_);
lean_inc(v_l_2024_);
lean_inc(v_v_2023_);
lean_inc(v_k_2022_);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_r_2008_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; lean_object* v_unused_2059_; lean_object* v_unused_2060_; lean_object* v_unused_2061_; lean_object* v_unused_2062_; 
v_unused_2058_ = lean_ctor_get(v_r_2008_, 4);
lean_dec(v_unused_2058_);
v_unused_2059_ = lean_ctor_get(v_r_2008_, 3);
lean_dec(v_unused_2059_);
v_unused_2060_ = lean_ctor_get(v_r_2008_, 2);
lean_dec(v_unused_2060_);
v_unused_2061_ = lean_ctor_get(v_r_2008_, 1);
lean_dec(v_unused_2061_);
v_unused_2062_ = lean_ctor_get(v_r_2008_, 0);
lean_dec(v_unused_2062_);
v___x_2030_ = v_r_2008_;
v_isShared_2031_ = v_isSharedCheck_2057_;
goto v_resetjp_2029_;
}
else
{
lean_dec(v_r_2008_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2057_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___x_2045_; lean_object* v___y_2047_; 
v___x_2032_ = lean_nat_add(v___x_2002_, v_size_2004_);
lean_dec(v_size_2004_);
v___x_2033_ = lean_nat_add(v___x_2032_, v_size_2003_);
lean_dec(v___x_2032_);
v___x_2045_ = lean_nat_add(v___x_2002_, v_size_2020_);
if (lean_obj_tag(v_l_2024_) == 0)
{
lean_object* v_size_2055_; 
v_size_2055_ = lean_ctor_get(v_l_2024_, 0);
lean_inc(v_size_2055_);
v___y_2047_ = v_size_2055_;
goto v___jp_2046_;
}
else
{
lean_object* v___x_2056_; 
v___x_2056_ = lean_unsigned_to_nat(0u);
v___y_2047_ = v___x_2056_;
goto v___jp_2046_;
}
v___jp_2034_:
{
lean_object* v___x_2038_; lean_object* v___x_2040_; 
v___x_2038_ = lean_nat_add(v___y_2035_, v___y_2037_);
lean_dec(v___y_2037_);
lean_dec(v___y_2035_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 4, v_impl_2001_);
lean_ctor_set(v___x_2030_, 3, v_r_2025_);
lean_ctor_set(v___x_2030_, 2, v_v_1509_);
lean_ctor_set(v___x_2030_, 1, v_k_1508_);
lean_ctor_set(v___x_2030_, 0, v___x_2038_);
v___x_2040_ = v___x_2030_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_k_1508_);
lean_ctor_set(v_reuseFailAlloc_2044_, 2, v_v_1509_);
lean_ctor_set(v_reuseFailAlloc_2044_, 3, v_r_2025_);
lean_ctor_set(v_reuseFailAlloc_2044_, 4, v_impl_2001_);
v___x_2040_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_object* v___x_2042_; 
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 4, v___x_2040_);
lean_ctor_set(v___x_2018_, 3, v___y_2036_);
lean_ctor_set(v___x_2018_, 2, v_v_2023_);
lean_ctor_set(v___x_2018_, 1, v_k_2022_);
lean_ctor_set(v___x_2018_, 0, v___x_2033_);
v___x_2042_ = v___x_2018_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2033_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_k_2022_);
lean_ctor_set(v_reuseFailAlloc_2043_, 2, v_v_2023_);
lean_ctor_set(v_reuseFailAlloc_2043_, 3, v___y_2036_);
lean_ctor_set(v_reuseFailAlloc_2043_, 4, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
v___jp_2046_:
{
lean_object* v___x_2048_; lean_object* v___x_2050_; 
v___x_2048_ = lean_nat_add(v___x_2045_, v___y_2047_);
lean_dec(v___y_2047_);
lean_dec(v___x_2045_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 4, v_l_2024_);
lean_ctor_set(v___x_1513_, 3, v_l_2007_);
lean_ctor_set(v___x_1513_, 2, v_v_2006_);
lean_ctor_set(v___x_1513_, 1, v_k_2005_);
lean_ctor_set(v___x_1513_, 0, v___x_2048_);
v___x_2050_ = v___x_1513_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2048_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v_k_2005_);
lean_ctor_set(v_reuseFailAlloc_2054_, 2, v_v_2006_);
lean_ctor_set(v_reuseFailAlloc_2054_, 3, v_l_2007_);
lean_ctor_set(v_reuseFailAlloc_2054_, 4, v_l_2024_);
v___x_2050_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
lean_object* v___x_2051_; 
v___x_2051_ = lean_nat_add(v___x_2002_, v_size_2003_);
if (lean_obj_tag(v_r_2025_) == 0)
{
lean_object* v_size_2052_; 
v_size_2052_ = lean_ctor_get(v_r_2025_, 0);
lean_inc(v_size_2052_);
v___y_2035_ = v___x_2051_;
v___y_2036_ = v___x_2050_;
v___y_2037_ = v_size_2052_;
goto v___jp_2034_;
}
else
{
lean_object* v___x_2053_; 
v___x_2053_ = lean_unsigned_to_nat(0u);
v___y_2035_ = v___x_2051_;
v___y_2036_ = v___x_2050_;
v___y_2037_ = v___x_2053_;
goto v___jp_2034_;
}
}
}
}
}
else
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2068_; 
lean_del_object(v___x_1513_);
v___x_2063_ = lean_nat_add(v___x_2002_, v_size_2004_);
lean_dec(v_size_2004_);
v___x_2064_ = lean_nat_add(v___x_2063_, v_size_2003_);
lean_dec(v___x_2063_);
v___x_2065_ = lean_nat_add(v___x_2002_, v_size_2003_);
v___x_2066_ = lean_nat_add(v___x_2065_, v_size_2021_);
lean_dec(v___x_2065_);
lean_inc_ref(v_impl_2001_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 4, v_impl_2001_);
lean_ctor_set(v___x_2018_, 3, v_r_2008_);
lean_ctor_set(v___x_2018_, 2, v_v_1509_);
lean_ctor_set(v___x_2018_, 1, v_k_1508_);
lean_ctor_set(v___x_2018_, 0, v___x_2066_);
v___x_2068_ = v___x_2018_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2066_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v_k_1508_);
lean_ctor_set(v_reuseFailAlloc_2081_, 2, v_v_1509_);
lean_ctor_set(v_reuseFailAlloc_2081_, 3, v_r_2008_);
lean_ctor_set(v_reuseFailAlloc_2081_, 4, v_impl_2001_);
v___x_2068_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
v_isSharedCheck_2075_ = !lean_is_exclusive(v_impl_2001_);
if (v_isSharedCheck_2075_ == 0)
{
lean_object* v_unused_2076_; lean_object* v_unused_2077_; lean_object* v_unused_2078_; lean_object* v_unused_2079_; lean_object* v_unused_2080_; 
v_unused_2076_ = lean_ctor_get(v_impl_2001_, 4);
lean_dec(v_unused_2076_);
v_unused_2077_ = lean_ctor_get(v_impl_2001_, 3);
lean_dec(v_unused_2077_);
v_unused_2078_ = lean_ctor_get(v_impl_2001_, 2);
lean_dec(v_unused_2078_);
v_unused_2079_ = lean_ctor_get(v_impl_2001_, 1);
lean_dec(v_unused_2079_);
v_unused_2080_ = lean_ctor_get(v_impl_2001_, 0);
lean_dec(v_unused_2080_);
v___x_2070_ = v_impl_2001_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_dec(v_impl_2001_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 4, v___x_2068_);
lean_ctor_set(v___x_2070_, 3, v_l_2007_);
lean_ctor_set(v___x_2070_, 2, v_v_2006_);
lean_ctor_set(v___x_2070_, 1, v_k_2005_);
lean_ctor_set(v___x_2070_, 0, v___x_2064_);
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2064_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_k_2005_);
lean_ctor_set(v_reuseFailAlloc_2074_, 2, v_v_2006_);
lean_ctor_set(v_reuseFailAlloc_2074_, 3, v_l_2007_);
lean_ctor_set(v_reuseFailAlloc_2074_, 4, v___x_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2088_; lean_object* v___x_2089_; lean_object* v___x_2091_; 
v_size_2088_ = lean_ctor_get(v_impl_2001_, 0);
v___x_2089_ = lean_nat_add(v___x_2002_, v_size_2088_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 4, v_impl_2001_);
lean_ctor_set(v___x_1513_, 0, v___x_2089_);
v___x_2091_ = v___x_1513_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v_k_1508_);
lean_ctor_set(v_reuseFailAlloc_2092_, 2, v_v_1509_);
lean_ctor_set(v_reuseFailAlloc_2092_, 3, v_l_1510_);
lean_ctor_set(v_reuseFailAlloc_2092_, 4, v_impl_2001_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
else
{
if (lean_obj_tag(v_l_1510_) == 0)
{
lean_object* v_l_2093_; 
v_l_2093_ = lean_ctor_get(v_l_1510_, 3);
if (lean_obj_tag(v_l_2093_) == 0)
{
lean_object* v_r_2094_; 
lean_inc_ref(v_l_2093_);
v_r_2094_ = lean_ctor_get(v_l_1510_, 4);
lean_inc(v_r_2094_);
if (lean_obj_tag(v_r_2094_) == 0)
{
lean_object* v_size_2095_; lean_object* v_k_2096_; lean_object* v_v_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2110_; 
v_size_2095_ = lean_ctor_get(v_l_1510_, 0);
v_k_2096_ = lean_ctor_get(v_l_1510_, 1);
v_v_2097_ = lean_ctor_get(v_l_1510_, 2);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_l_1510_);
if (v_isSharedCheck_2110_ == 0)
{
lean_object* v_unused_2111_; lean_object* v_unused_2112_; 
v_unused_2111_ = lean_ctor_get(v_l_1510_, 4);
lean_dec(v_unused_2111_);
v_unused_2112_ = lean_ctor_get(v_l_1510_, 3);
lean_dec(v_unused_2112_);
v___x_2099_ = v_l_1510_;
v_isShared_2100_ = v_isSharedCheck_2110_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_v_2097_);
lean_inc(v_k_2096_);
lean_inc(v_size_2095_);
lean_dec(v_l_1510_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2110_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v_size_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2105_; 
v_size_2101_ = lean_ctor_get(v_r_2094_, 0);
v___x_2102_ = lean_nat_add(v___x_2002_, v_size_2095_);
lean_dec(v_size_2095_);
v___x_2103_ = lean_nat_add(v___x_2002_, v_size_2101_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 4, v_impl_2001_);
lean_ctor_set(v___x_2099_, 3, v_r_2094_);
lean_ctor_set(v___x_2099_, 2, v_v_1509_);
lean_ctor_set(v___x_2099_, 1, v_k_1508_);
lean_ctor_set(v___x_2099_, 0, v___x_2103_);
v___x_2105_ = v___x_2099_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2103_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v_k_1508_);
lean_ctor_set(v_reuseFailAlloc_2109_, 2, v_v_1509_);
lean_ctor_set(v_reuseFailAlloc_2109_, 3, v_r_2094_);
lean_ctor_set(v_reuseFailAlloc_2109_, 4, v_impl_2001_);
v___x_2105_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
lean_object* v___x_2107_; 
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 4, v___x_2105_);
lean_ctor_set(v___x_1513_, 3, v_l_2093_);
lean_ctor_set(v___x_1513_, 2, v_v_2097_);
lean_ctor_set(v___x_1513_, 1, v_k_2096_);
lean_ctor_set(v___x_1513_, 0, v___x_2102_);
v___x_2107_ = v___x_1513_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2102_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_k_2096_);
lean_ctor_set(v_reuseFailAlloc_2108_, 2, v_v_2097_);
lean_ctor_set(v_reuseFailAlloc_2108_, 3, v_l_2093_);
lean_ctor_set(v_reuseFailAlloc_2108_, 4, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
else
{
lean_object* v_k_2113_; lean_object* v_v_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2125_; 
v_k_2113_ = lean_ctor_get(v_l_1510_, 1);
v_v_2114_ = lean_ctor_get(v_l_1510_, 2);
v_isSharedCheck_2125_ = !lean_is_exclusive(v_l_1510_);
if (v_isSharedCheck_2125_ == 0)
{
lean_object* v_unused_2126_; lean_object* v_unused_2127_; lean_object* v_unused_2128_; 
v_unused_2126_ = lean_ctor_get(v_l_1510_, 4);
lean_dec(v_unused_2126_);
v_unused_2127_ = lean_ctor_get(v_l_1510_, 3);
lean_dec(v_unused_2127_);
v_unused_2128_ = lean_ctor_get(v_l_1510_, 0);
lean_dec(v_unused_2128_);
v___x_2116_ = v_l_1510_;
v_isShared_2117_ = v_isSharedCheck_2125_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_v_2114_);
lean_inc(v_k_2113_);
lean_dec(v_l_1510_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2125_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2118_; lean_object* v___x_2120_; 
v___x_2118_ = lean_unsigned_to_nat(3u);
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 3, v_r_2094_);
lean_ctor_set(v___x_2116_, 2, v_v_1509_);
lean_ctor_set(v___x_2116_, 1, v_k_1508_);
lean_ctor_set(v___x_2116_, 0, v___x_2002_);
v___x_2120_ = v___x_2116_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2002_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_k_1508_);
lean_ctor_set(v_reuseFailAlloc_2124_, 2, v_v_1509_);
lean_ctor_set(v_reuseFailAlloc_2124_, 3, v_r_2094_);
lean_ctor_set(v_reuseFailAlloc_2124_, 4, v_r_2094_);
v___x_2120_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
lean_object* v___x_2122_; 
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 4, v___x_2120_);
lean_ctor_set(v___x_1513_, 3, v_l_2093_);
lean_ctor_set(v___x_1513_, 2, v_v_2114_);
lean_ctor_set(v___x_1513_, 1, v_k_2113_);
lean_ctor_set(v___x_1513_, 0, v___x_2118_);
v___x_2122_ = v___x_1513_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2118_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v_k_2113_);
lean_ctor_set(v_reuseFailAlloc_2123_, 2, v_v_2114_);
lean_ctor_set(v_reuseFailAlloc_2123_, 3, v_l_2093_);
lean_ctor_set(v_reuseFailAlloc_2123_, 4, v___x_2120_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
}
else
{
lean_object* v_r_2129_; 
v_r_2129_ = lean_ctor_get(v_l_1510_, 4);
lean_inc(v_r_2129_);
if (lean_obj_tag(v_r_2129_) == 0)
{
lean_object* v_k_2130_; lean_object* v_v_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2154_; 
lean_inc(v_l_2093_);
v_k_2130_ = lean_ctor_get(v_l_1510_, 1);
v_v_2131_ = lean_ctor_get(v_l_1510_, 2);
v_isSharedCheck_2154_ = !lean_is_exclusive(v_l_1510_);
if (v_isSharedCheck_2154_ == 0)
{
lean_object* v_unused_2155_; lean_object* v_unused_2156_; lean_object* v_unused_2157_; 
v_unused_2155_ = lean_ctor_get(v_l_1510_, 4);
lean_dec(v_unused_2155_);
v_unused_2156_ = lean_ctor_get(v_l_1510_, 3);
lean_dec(v_unused_2156_);
v_unused_2157_ = lean_ctor_get(v_l_1510_, 0);
lean_dec(v_unused_2157_);
v___x_2133_ = v_l_1510_;
v_isShared_2134_ = v_isSharedCheck_2154_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_v_2131_);
lean_inc(v_k_2130_);
lean_dec(v_l_1510_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2154_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v_k_2135_; lean_object* v_v_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2150_; 
v_k_2135_ = lean_ctor_get(v_r_2129_, 1);
v_v_2136_ = lean_ctor_get(v_r_2129_, 2);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_r_2129_);
if (v_isSharedCheck_2150_ == 0)
{
lean_object* v_unused_2151_; lean_object* v_unused_2152_; lean_object* v_unused_2153_; 
v_unused_2151_ = lean_ctor_get(v_r_2129_, 4);
lean_dec(v_unused_2151_);
v_unused_2152_ = lean_ctor_get(v_r_2129_, 3);
lean_dec(v_unused_2152_);
v_unused_2153_ = lean_ctor_get(v_r_2129_, 0);
lean_dec(v_unused_2153_);
v___x_2138_ = v_r_2129_;
v_isShared_2139_ = v_isSharedCheck_2150_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_v_2136_);
lean_inc(v_k_2135_);
lean_dec(v_r_2129_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2150_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2140_ = lean_unsigned_to_nat(3u);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 4, v_l_2093_);
lean_ctor_set(v___x_2138_, 3, v_l_2093_);
lean_ctor_set(v___x_2138_, 2, v_v_2131_);
lean_ctor_set(v___x_2138_, 1, v_k_2130_);
lean_ctor_set(v___x_2138_, 0, v___x_2002_);
v___x_2142_ = v___x_2138_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2002_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_k_2130_);
lean_ctor_set(v_reuseFailAlloc_2149_, 2, v_v_2131_);
lean_ctor_set(v_reuseFailAlloc_2149_, 3, v_l_2093_);
lean_ctor_set(v_reuseFailAlloc_2149_, 4, v_l_2093_);
v___x_2142_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_object* v___x_2144_; 
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 4, v_l_2093_);
lean_ctor_set(v___x_2133_, 2, v_v_1509_);
lean_ctor_set(v___x_2133_, 1, v_k_1508_);
lean_ctor_set(v___x_2133_, 0, v___x_2002_);
v___x_2144_ = v___x_2133_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2002_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_k_1508_);
lean_ctor_set(v_reuseFailAlloc_2148_, 2, v_v_1509_);
lean_ctor_set(v_reuseFailAlloc_2148_, 3, v_l_2093_);
lean_ctor_set(v_reuseFailAlloc_2148_, 4, v_l_2093_);
v___x_2144_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
lean_object* v___x_2146_; 
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 4, v___x_2144_);
lean_ctor_set(v___x_1513_, 3, v___x_2142_);
lean_ctor_set(v___x_1513_, 2, v_v_2136_);
lean_ctor_set(v___x_1513_, 1, v_k_2135_);
lean_ctor_set(v___x_1513_, 0, v___x_2140_);
v___x_2146_ = v___x_1513_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2140_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v_k_2135_);
lean_ctor_set(v_reuseFailAlloc_2147_, 2, v_v_2136_);
lean_ctor_set(v_reuseFailAlloc_2147_, 3, v___x_2142_);
lean_ctor_set(v_reuseFailAlloc_2147_, 4, v___x_2144_);
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
}
else
{
lean_object* v___x_2158_; lean_object* v___x_2160_; 
v___x_2158_ = lean_unsigned_to_nat(2u);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 4, v_r_2129_);
lean_ctor_set(v___x_1513_, 0, v___x_2158_);
v___x_2160_ = v___x_1513_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2158_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_k_1508_);
lean_ctor_set(v_reuseFailAlloc_2161_, 2, v_v_1509_);
lean_ctor_set(v_reuseFailAlloc_2161_, 3, v_l_1510_);
lean_ctor_set(v_reuseFailAlloc_2161_, 4, v_r_2129_);
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
else
{
lean_object* v___x_2163_; 
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 4, v_l_1510_);
lean_ctor_set(v___x_1513_, 0, v___x_2002_);
v___x_2163_ = v___x_1513_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2002_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_k_1508_);
lean_ctor_set(v_reuseFailAlloc_2164_, 2, v_v_1509_);
lean_ctor_set(v_reuseFailAlloc_2164_, 3, v_l_1510_);
lean_ctor_set(v_reuseFailAlloc_2164_, 4, v_l_1510_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
}
}
}
else
{
return v_t_1507_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg___boxed(lean_object* v_k_2167_, lean_object* v_t_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_2167_, v_t_2168_);
lean_dec_ref(v_k_2167_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___lam__0(lean_object* v_val_2170_, lean_object* v_s_2171_){
_start:
{
lean_object* v_toRingState_2172_; lean_object* v_denoteEntries_2173_; lean_object* v_nextId_2174_; lean_object* v_steps_2175_; lean_object* v_queue_2176_; lean_object* v_basis_2177_; lean_object* v_diseqs_2178_; uint8_t v_recheck_2179_; lean_object* v_invSet_2180_; lean_object* v_powIdentityVarCount_2181_; lean_object* v_numEq0_x3f_2182_; uint8_t v_numEq0Updated_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2191_; 
v_toRingState_2172_ = lean_ctor_get(v_s_2171_, 0);
v_denoteEntries_2173_ = lean_ctor_get(v_s_2171_, 1);
v_nextId_2174_ = lean_ctor_get(v_s_2171_, 2);
v_steps_2175_ = lean_ctor_get(v_s_2171_, 3);
v_queue_2176_ = lean_ctor_get(v_s_2171_, 4);
v_basis_2177_ = lean_ctor_get(v_s_2171_, 5);
v_diseqs_2178_ = lean_ctor_get(v_s_2171_, 6);
v_recheck_2179_ = lean_ctor_get_uint8(v_s_2171_, sizeof(void*)*10);
v_invSet_2180_ = lean_ctor_get(v_s_2171_, 7);
v_powIdentityVarCount_2181_ = lean_ctor_get(v_s_2171_, 8);
v_numEq0_x3f_2182_ = lean_ctor_get(v_s_2171_, 9);
v_numEq0Updated_2183_ = lean_ctor_get_uint8(v_s_2171_, sizeof(void*)*10 + 1);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_s_2171_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2185_ = v_s_2171_;
v_isShared_2186_ = v_isSharedCheck_2191_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_numEq0_x3f_2182_);
lean_inc(v_powIdentityVarCount_2181_);
lean_inc(v_invSet_2180_);
lean_inc(v_diseqs_2178_);
lean_inc(v_basis_2177_);
lean_inc(v_queue_2176_);
lean_inc(v_steps_2175_);
lean_inc(v_nextId_2174_);
lean_inc(v_denoteEntries_2173_);
lean_inc(v_toRingState_2172_);
lean_dec(v_s_2171_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2191_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2187_; lean_object* v___x_2189_; 
v___x_2187_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_val_2170_, v_queue_2176_);
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 4, v___x_2187_);
v___x_2189_ = v___x_2185_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_toRingState_2172_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v_denoteEntries_2173_);
lean_ctor_set(v_reuseFailAlloc_2190_, 2, v_nextId_2174_);
lean_ctor_set(v_reuseFailAlloc_2190_, 3, v_steps_2175_);
lean_ctor_set(v_reuseFailAlloc_2190_, 4, v___x_2187_);
lean_ctor_set(v_reuseFailAlloc_2190_, 5, v_basis_2177_);
lean_ctor_set(v_reuseFailAlloc_2190_, 6, v_diseqs_2178_);
lean_ctor_set(v_reuseFailAlloc_2190_, 7, v_invSet_2180_);
lean_ctor_set(v_reuseFailAlloc_2190_, 8, v_powIdentityVarCount_2181_);
lean_ctor_set(v_reuseFailAlloc_2190_, 9, v_numEq0_x3f_2182_);
lean_ctor_set_uint8(v_reuseFailAlloc_2190_, sizeof(void*)*10, v_recheck_2179_);
lean_ctor_set_uint8(v_reuseFailAlloc_2190_, sizeof(void*)*10 + 1, v_numEq0Updated_2183_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___lam__0___boxed(lean_object* v_val_2192_, lean_object* v_s_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___lam__0(v_val_2192_, v_s_2193_);
lean_dec_ref(v_val_2192_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg(lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_){
_start:
{
lean_object* v___x_2199_; 
v___x_2199_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_2195_, v_a_2196_, v_a_2197_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2239_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2202_ = v___x_2199_;
v_isShared_2203_ = v_isSharedCheck_2239_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2199_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2239_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v_queue_2204_; lean_object* v___x_2205_; 
v_queue_2204_ = lean_ctor_get(v_a_2200_, 4);
lean_inc(v_queue_2204_);
lean_dec(v_a_2200_);
v___x_2205_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_queue_2204_);
lean_dec(v_queue_2204_);
if (lean_obj_tag(v___x_2205_) == 1)
{
lean_object* v_val_2206_; lean_object* v___f_2207_; lean_object* v___x_2208_; 
lean_del_object(v___x_2202_);
v_val_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_val_2206_);
v___f_2207_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2207_, 0, v_val_2206_);
v___x_2208_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(v___f_2207_, v_a_2195_, v_a_2196_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v___x_2209_; lean_object* v___x_2210_; 
lean_dec_ref_known(v___x_2208_, 1);
v___x_2209_ = lean_unsigned_to_nat(1u);
v___x_2210_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v___x_2209_, v_a_2196_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2217_ == 0)
{
lean_object* v_unused_2218_; 
v_unused_2218_ = lean_ctor_get(v___x_2210_, 0);
lean_dec(v_unused_2218_);
v___x_2212_ = v___x_2210_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_dec(v___x_2210_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 0, v___x_2205_);
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2205_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2226_; 
lean_dec_ref_known(v___x_2205_, 1);
v_a_2219_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2221_ = v___x_2210_;
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2210_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2219_);
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
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
lean_dec_ref_known(v___x_2205_, 1);
v_a_2227_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2208_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2208_);
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
lean_object* v___x_2235_; lean_object* v___x_2237_; 
lean_dec(v___x_2205_);
v___x_2235_ = lean_box(0);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v___x_2235_);
v___x_2237_ = v___x_2202_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2235_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
v_a_2240_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2199_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2199_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___boxed(lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg(v_a_2248_, v_a_2249_, v_a_2250_);
lean_dec_ref(v_a_2250_);
lean_dec(v_a_2249_);
lean_dec_ref(v_a_2248_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_){
_start:
{
lean_object* v___x_2265_; 
v___x_2265_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg(v_a_2253_, v_a_2254_, v_a_2262_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___boxed(lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_);
lean_dec(v_a_2276_);
lean_dec_ref(v_a_2275_);
lean_dec(v_a_2274_);
lean_dec_ref(v_a_2273_);
lean_dec(v_a_2272_);
lean_dec_ref(v_a_2271_);
lean_dec(v_a_2270_);
lean_dec_ref(v_a_2269_);
lean_dec(v_a_2268_);
lean_dec(v_a_2267_);
lean_dec_ref(v_a_2266_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(lean_object* v_00_u03b2_2279_, lean_object* v_k_2280_, lean_object* v_t_2281_, lean_object* v_h_2282_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_2280_, v_t_2281_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___boxed(lean_object* v_00_u03b2_2284_, lean_object* v_k_2285_, lean_object* v_t_2286_, lean_object* v_h_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(v_00_u03b2_2284_, v_k_2285_, v_t_2286_, v_h_2287_);
lean_dec_ref(v_k_2285_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2289_, lean_object* v_x_2290_, lean_object* v_x_2291_, lean_object* v_x_2292_){
_start:
{
lean_object* v_ks_2293_; lean_object* v_vs_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2320_; 
v_ks_2293_ = lean_ctor_get(v_x_2289_, 0);
v_vs_2294_ = lean_ctor_get(v_x_2289_, 1);
v_isSharedCheck_2320_ = !lean_is_exclusive(v_x_2289_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2296_ = v_x_2289_;
v_isShared_2297_ = v_isSharedCheck_2320_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_vs_2294_);
lean_inc(v_ks_2293_);
lean_dec(v_x_2289_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2320_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; uint8_t v___x_2299_; 
v___x_2298_ = lean_array_get_size(v_ks_2293_);
v___x_2299_ = lean_nat_dec_lt(v_x_2290_, v___x_2298_);
if (v___x_2299_ == 0)
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2303_; 
lean_dec(v_x_2290_);
v___x_2300_ = lean_array_push(v_ks_2293_, v_x_2291_);
v___x_2301_ = lean_array_push(v_vs_2294_, v_x_2292_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 1, v___x_2301_);
lean_ctor_set(v___x_2296_, 0, v___x_2300_);
v___x_2303_ = v___x_2296_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v___x_2300_);
lean_ctor_set(v_reuseFailAlloc_2304_, 1, v___x_2301_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
else
{
lean_object* v_k_x27_2305_; size_t v___x_2306_; size_t v___x_2307_; uint8_t v___x_2308_; 
v_k_x27_2305_ = lean_array_fget_borrowed(v_ks_2293_, v_x_2290_);
v___x_2306_ = lean_ptr_addr(v_x_2291_);
v___x_2307_ = lean_ptr_addr(v_k_x27_2305_);
v___x_2308_ = lean_usize_dec_eq(v___x_2306_, v___x_2307_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2310_; 
if (v_isShared_2297_ == 0)
{
v___x_2310_ = v___x_2296_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_ks_2293_);
lean_ctor_set(v_reuseFailAlloc_2314_, 1, v_vs_2294_);
v___x_2310_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = lean_unsigned_to_nat(1u);
v___x_2312_ = lean_nat_add(v_x_2290_, v___x_2311_);
lean_dec(v_x_2290_);
v_x_2289_ = v___x_2310_;
v_x_2290_ = v___x_2312_;
goto _start;
}
}
else
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2318_; 
v___x_2315_ = lean_array_fset(v_ks_2293_, v_x_2290_, v_x_2291_);
v___x_2316_ = lean_array_fset(v_vs_2294_, v_x_2290_, v_x_2292_);
lean_dec(v_x_2290_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 1, v___x_2316_);
lean_ctor_set(v___x_2296_, 0, v___x_2315_);
v___x_2318_ = v___x_2296_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2315_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v___x_2316_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2321_, lean_object* v_k_2322_, lean_object* v_v_2323_){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = lean_unsigned_to_nat(0u);
v___x_2325_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2321_, v___x_2324_, v_k_2322_, v_v_2323_);
return v___x_2325_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2326_; 
v___x_2326_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(lean_object* v_x_2327_, size_t v_x_2328_, size_t v_x_2329_, lean_object* v_x_2330_, lean_object* v_x_2331_){
_start:
{
if (lean_obj_tag(v_x_2327_) == 0)
{
lean_object* v_es_2332_; size_t v___x_2333_; size_t v___x_2334_; lean_object* v_j_2335_; lean_object* v___x_2336_; uint8_t v___x_2337_; 
v_es_2332_ = lean_ctor_get(v_x_2327_, 0);
v___x_2333_ = ((size_t)31ULL);
v___x_2334_ = lean_usize_land(v_x_2328_, v___x_2333_);
v_j_2335_ = lean_usize_to_nat(v___x_2334_);
v___x_2336_ = lean_array_get_size(v_es_2332_);
v___x_2337_ = lean_nat_dec_lt(v_j_2335_, v___x_2336_);
if (v___x_2337_ == 0)
{
lean_dec(v_j_2335_);
lean_dec(v_x_2331_);
lean_dec_ref(v_x_2330_);
return v_x_2327_;
}
else
{
lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2378_; 
lean_inc_ref(v_es_2332_);
v_isSharedCheck_2378_ = !lean_is_exclusive(v_x_2327_);
if (v_isSharedCheck_2378_ == 0)
{
lean_object* v_unused_2379_; 
v_unused_2379_ = lean_ctor_get(v_x_2327_, 0);
lean_dec(v_unused_2379_);
v___x_2339_ = v_x_2327_;
v_isShared_2340_ = v_isSharedCheck_2378_;
goto v_resetjp_2338_;
}
else
{
lean_dec(v_x_2327_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2378_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v_v_2341_; lean_object* v___x_2342_; lean_object* v_xs_x27_2343_; lean_object* v___y_2345_; 
v_v_2341_ = lean_array_fget(v_es_2332_, v_j_2335_);
v___x_2342_ = lean_box(0);
v_xs_x27_2343_ = lean_array_fset(v_es_2332_, v_j_2335_, v___x_2342_);
switch(lean_obj_tag(v_v_2341_))
{
case 0:
{
lean_object* v_key_2350_; lean_object* v_val_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2363_; 
v_key_2350_ = lean_ctor_get(v_v_2341_, 0);
v_val_2351_ = lean_ctor_get(v_v_2341_, 1);
v_isSharedCheck_2363_ = !lean_is_exclusive(v_v_2341_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2353_ = v_v_2341_;
v_isShared_2354_ = v_isSharedCheck_2363_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_val_2351_);
lean_inc(v_key_2350_);
lean_dec(v_v_2341_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2363_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
size_t v___x_2355_; size_t v___x_2356_; uint8_t v___x_2357_; 
v___x_2355_ = lean_ptr_addr(v_x_2330_);
v___x_2356_ = lean_ptr_addr(v_key_2350_);
v___x_2357_ = lean_usize_dec_eq(v___x_2355_, v___x_2356_);
if (v___x_2357_ == 0)
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
lean_del_object(v___x_2353_);
v___x_2358_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2350_, v_val_2351_, v_x_2330_, v_x_2331_);
v___x_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
v___y_2345_ = v___x_2359_;
goto v___jp_2344_;
}
else
{
lean_object* v___x_2361_; 
lean_dec(v_val_2351_);
lean_dec(v_key_2350_);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 1, v_x_2331_);
lean_ctor_set(v___x_2353_, 0, v_x_2330_);
v___x_2361_ = v___x_2353_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_x_2330_);
lean_ctor_set(v_reuseFailAlloc_2362_, 1, v_x_2331_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
v___y_2345_ = v___x_2361_;
goto v___jp_2344_;
}
}
}
}
case 1:
{
lean_object* v_node_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2376_; 
v_node_2364_ = lean_ctor_get(v_v_2341_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_v_2341_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2366_ = v_v_2341_;
v_isShared_2367_ = v_isSharedCheck_2376_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_node_2364_);
lean_dec(v_v_2341_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2376_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
size_t v___x_2368_; size_t v___x_2369_; size_t v___x_2370_; size_t v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2374_; 
v___x_2368_ = ((size_t)5ULL);
v___x_2369_ = lean_usize_shift_right(v_x_2328_, v___x_2368_);
v___x_2370_ = ((size_t)1ULL);
v___x_2371_ = lean_usize_add(v_x_2329_, v___x_2370_);
v___x_2372_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_node_2364_, v___x_2369_, v___x_2371_, v_x_2330_, v_x_2331_);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 0, v___x_2372_);
v___x_2374_ = v___x_2366_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2372_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
v___y_2345_ = v___x_2374_;
goto v___jp_2344_;
}
}
}
default: 
{
lean_object* v___x_2377_; 
v___x_2377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2377_, 0, v_x_2330_);
lean_ctor_set(v___x_2377_, 1, v_x_2331_);
v___y_2345_ = v___x_2377_;
goto v___jp_2344_;
}
}
v___jp_2344_:
{
lean_object* v___x_2346_; lean_object* v___x_2348_; 
v___x_2346_ = lean_array_fset(v_xs_x27_2343_, v_j_2335_, v___y_2345_);
lean_dec(v_j_2335_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2346_);
v___x_2348_ = v___x_2339_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___x_2346_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
}
else
{
lean_object* v_ks_2380_; lean_object* v_vs_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2399_; 
v_ks_2380_ = lean_ctor_get(v_x_2327_, 0);
v_vs_2381_ = lean_ctor_get(v_x_2327_, 1);
v_isSharedCheck_2399_ = !lean_is_exclusive(v_x_2327_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2383_ = v_x_2327_;
v_isShared_2384_ = v_isSharedCheck_2399_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_vs_2381_);
lean_inc(v_ks_2380_);
lean_dec(v_x_2327_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2399_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_ks_2380_);
lean_ctor_set(v_reuseFailAlloc_2398_, 1, v_vs_2381_);
v___x_2386_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
lean_object* v_newNode_2387_; size_t v___x_2388_; uint8_t v___x_2389_; 
v_newNode_2387_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v___x_2386_, v_x_2330_, v_x_2331_);
v___x_2388_ = ((size_t)7ULL);
v___x_2389_ = lean_usize_dec_le(v___x_2388_, v_x_2329_);
if (v___x_2389_ == 0)
{
lean_object* v___x_2390_; lean_object* v___x_2391_; uint8_t v___x_2392_; 
v___x_2390_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2387_);
v___x_2391_ = lean_unsigned_to_nat(4u);
v___x_2392_ = lean_nat_dec_lt(v___x_2390_, v___x_2391_);
lean_dec(v___x_2390_);
if (v___x_2392_ == 0)
{
lean_object* v_ks_2393_; lean_object* v_vs_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v_ks_2393_ = lean_ctor_get(v_newNode_2387_, 0);
lean_inc_ref(v_ks_2393_);
v_vs_2394_ = lean_ctor_get(v_newNode_2387_, 1);
lean_inc_ref(v_vs_2394_);
lean_dec_ref(v_newNode_2387_);
v___x_2395_ = lean_unsigned_to_nat(0u);
v___x_2396_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0);
v___x_2397_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_x_2329_, v_ks_2393_, v_vs_2394_, v___x_2395_, v___x_2396_);
lean_dec_ref(v_vs_2394_);
lean_dec_ref(v_ks_2393_);
return v___x_2397_;
}
else
{
return v_newNode_2387_;
}
}
else
{
return v_newNode_2387_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(size_t v_depth_2400_, lean_object* v_keys_2401_, lean_object* v_vals_2402_, lean_object* v_i_2403_, lean_object* v_entries_2404_){
_start:
{
lean_object* v___x_2405_; uint8_t v___x_2406_; 
v___x_2405_ = lean_array_get_size(v_keys_2401_);
v___x_2406_ = lean_nat_dec_lt(v_i_2403_, v___x_2405_);
if (v___x_2406_ == 0)
{
lean_dec(v_i_2403_);
return v_entries_2404_;
}
else
{
lean_object* v_k_2407_; lean_object* v_v_2408_; size_t v___x_2409_; size_t v___x_2410_; size_t v___x_2411_; uint64_t v___x_2412_; size_t v_h_2413_; size_t v___x_2414_; lean_object* v___x_2415_; size_t v___x_2416_; size_t v___x_2417_; size_t v___x_2418_; size_t v_h_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v_k_2407_ = lean_array_fget_borrowed(v_keys_2401_, v_i_2403_);
v_v_2408_ = lean_array_fget_borrowed(v_vals_2402_, v_i_2403_);
v___x_2409_ = lean_ptr_addr(v_k_2407_);
v___x_2410_ = ((size_t)3ULL);
v___x_2411_ = lean_usize_shift_right(v___x_2409_, v___x_2410_);
v___x_2412_ = lean_usize_to_uint64(v___x_2411_);
v_h_2413_ = lean_uint64_to_usize(v___x_2412_);
v___x_2414_ = ((size_t)5ULL);
v___x_2415_ = lean_unsigned_to_nat(1u);
v___x_2416_ = ((size_t)1ULL);
v___x_2417_ = lean_usize_sub(v_depth_2400_, v___x_2416_);
v___x_2418_ = lean_usize_mul(v___x_2414_, v___x_2417_);
v_h_2419_ = lean_usize_shift_right(v_h_2413_, v___x_2418_);
v___x_2420_ = lean_nat_add(v_i_2403_, v___x_2415_);
lean_dec(v_i_2403_);
lean_inc(v_v_2408_);
lean_inc(v_k_2407_);
v___x_2421_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_entries_2404_, v_h_2419_, v_depth_2400_, v_k_2407_, v_v_2408_);
v_i_2403_ = v___x_2420_;
v_entries_2404_ = v___x_2421_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2423_, lean_object* v_keys_2424_, lean_object* v_vals_2425_, lean_object* v_i_2426_, lean_object* v_entries_2427_){
_start:
{
size_t v_depth_boxed_2428_; lean_object* v_res_2429_; 
v_depth_boxed_2428_ = lean_unbox_usize(v_depth_2423_);
lean_dec(v_depth_2423_);
v_res_2429_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2428_, v_keys_2424_, v_vals_2425_, v_i_2426_, v_entries_2427_);
lean_dec_ref(v_vals_2425_);
lean_dec_ref(v_keys_2424_);
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___boxed(lean_object* v_x_2430_, lean_object* v_x_2431_, lean_object* v_x_2432_, lean_object* v_x_2433_, lean_object* v_x_2434_){
_start:
{
size_t v_x_6465__boxed_2435_; size_t v_x_6466__boxed_2436_; lean_object* v_res_2437_; 
v_x_6465__boxed_2435_ = lean_unbox_usize(v_x_2431_);
lean_dec(v_x_2431_);
v_x_6466__boxed_2436_ = lean_unbox_usize(v_x_2432_);
lean_dec(v_x_2432_);
v_res_2437_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2430_, v_x_6465__boxed_2435_, v_x_6466__boxed_2436_, v_x_2433_, v_x_2434_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(lean_object* v_x_2438_, lean_object* v_x_2439_, lean_object* v_x_2440_){
_start:
{
size_t v___x_2441_; size_t v___x_2442_; size_t v___x_2443_; uint64_t v___x_2444_; size_t v___x_2445_; size_t v___x_2446_; lean_object* v___x_2447_; 
v___x_2441_ = lean_ptr_addr(v_x_2439_);
v___x_2442_ = ((size_t)3ULL);
v___x_2443_ = lean_usize_shift_right(v___x_2441_, v___x_2442_);
v___x_2444_ = lean_usize_to_uint64(v___x_2443_);
v___x_2445_ = lean_uint64_to_usize(v___x_2444_);
v___x_2446_ = ((size_t)1ULL);
v___x_2447_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2438_, v___x_2445_, v___x_2446_, v_x_2439_, v_x_2440_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0(lean_object* v_e_2448_, lean_object* v_ringId_2449_, lean_object* v_s_2450_){
_start:
{
lean_object* v_rings_2451_; lean_object* v_exprToRingId_2452_; lean_object* v_semirings_2453_; lean_object* v_exprToSemiringId_2454_; lean_object* v_ncRings_2455_; lean_object* v_exprToNCRingId_2456_; lean_object* v_ncSemirings_2457_; lean_object* v_exprToNCSemiringId_2458_; lean_object* v_steps_2459_; uint8_t v_reportedMaxDegreeIssue_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2468_; 
v_rings_2451_ = lean_ctor_get(v_s_2450_, 0);
v_exprToRingId_2452_ = lean_ctor_get(v_s_2450_, 1);
v_semirings_2453_ = lean_ctor_get(v_s_2450_, 2);
v_exprToSemiringId_2454_ = lean_ctor_get(v_s_2450_, 3);
v_ncRings_2455_ = lean_ctor_get(v_s_2450_, 4);
v_exprToNCRingId_2456_ = lean_ctor_get(v_s_2450_, 5);
v_ncSemirings_2457_ = lean_ctor_get(v_s_2450_, 6);
v_exprToNCSemiringId_2458_ = lean_ctor_get(v_s_2450_, 7);
v_steps_2459_ = lean_ctor_get(v_s_2450_, 8);
v_reportedMaxDegreeIssue_2460_ = lean_ctor_get_uint8(v_s_2450_, sizeof(void*)*9);
v_isSharedCheck_2468_ = !lean_is_exclusive(v_s_2450_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2462_ = v_s_2450_;
v_isShared_2463_ = v_isSharedCheck_2468_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_steps_2459_);
lean_inc(v_exprToNCSemiringId_2458_);
lean_inc(v_ncSemirings_2457_);
lean_inc(v_exprToNCRingId_2456_);
lean_inc(v_ncRings_2455_);
lean_inc(v_exprToSemiringId_2454_);
lean_inc(v_semirings_2453_);
lean_inc(v_exprToRingId_2452_);
lean_inc(v_rings_2451_);
lean_dec(v_s_2450_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2468_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2464_; lean_object* v___x_2466_; 
v___x_2464_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_exprToRingId_2452_, v_e_2448_, v_ringId_2449_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 1, v___x_2464_);
v___x_2466_ = v___x_2462_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_rings_2451_);
lean_ctor_set(v_reuseFailAlloc_2467_, 1, v___x_2464_);
lean_ctor_set(v_reuseFailAlloc_2467_, 2, v_semirings_2453_);
lean_ctor_set(v_reuseFailAlloc_2467_, 3, v_exprToSemiringId_2454_);
lean_ctor_set(v_reuseFailAlloc_2467_, 4, v_ncRings_2455_);
lean_ctor_set(v_reuseFailAlloc_2467_, 5, v_exprToNCRingId_2456_);
lean_ctor_set(v_reuseFailAlloc_2467_, 6, v_ncSemirings_2457_);
lean_ctor_set(v_reuseFailAlloc_2467_, 7, v_exprToNCSemiringId_2458_);
lean_ctor_set(v_reuseFailAlloc_2467_, 8, v_steps_2459_);
lean_ctor_set_uint8(v_reuseFailAlloc_2467_, sizeof(void*)*9, v_reportedMaxDegreeIssue_2460_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1(void){
_start:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2470_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__0));
v___x_2471_ = l_Lean_stringToMessageData(v___x_2470_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(lean_object* v_e_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_){
_start:
{
lean_object* v_ringId_2485_; lean_object* v___f_2486_; lean_object* v___x_2487_; 
v_ringId_2485_ = lean_ctor_get(v_a_2473_, 0);
lean_inc(v_ringId_2485_);
lean_inc_ref(v_e_2472_);
v___f_2486_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2486_, 0, v_e_2472_);
lean_closure_set(v___f_2486_, 1, v_ringId_2485_);
v___x_2487_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_2472_, v_a_2474_, v_a_2479_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v_a_2488_; 
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_a_2488_);
lean_dec_ref_known(v___x_2487_, 1);
if (lean_obj_tag(v_a_2488_) == 1)
{
lean_object* v_val_2489_; uint8_t v___x_2490_; 
lean_dec_ref(v___f_2486_);
v_val_2489_ = lean_ctor_get(v_a_2488_, 0);
lean_inc(v_val_2489_);
lean_dec_ref_known(v_a_2488_, 1);
v___x_2490_ = lean_nat_dec_eq(v_val_2489_, v_ringId_2485_);
lean_dec(v_val_2489_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2491_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1);
v___x_2492_ = l_Lean_indentExpr(v_e_2472_);
v___x_2493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2491_);
lean_ctor_set(v___x_2493_, 1, v___x_2492_);
v___x_2494_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2475_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; uint8_t v_verbose_2496_; 
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2495_);
lean_dec_ref_known(v___x_2494_, 1);
v_verbose_2496_ = lean_ctor_get_uint8(v_a_2495_, 0);
lean_dec(v_a_2495_);
if (v_verbose_2496_ == 0)
{
lean_dec_ref_known(v___x_2493_, 2);
goto v___jp_2482_;
}
else
{
lean_object* v___x_2497_; 
v___x_2497_ = l_Lean_Meta_Sym_reportIssue(v___x_2493_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_dec_ref_known(v___x_2497_, 1);
goto v___jp_2482_;
}
else
{
return v___x_2497_;
}
}
}
else
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
lean_dec_ref_known(v___x_2493_, 2);
v_a_2498_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2500_ = v___x_2494_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2494_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2498_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
else
{
lean_dec_ref(v_e_2472_);
goto v___jp_2482_;
}
}
else
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
lean_dec(v_a_2488_);
lean_dec_ref(v_e_2472_);
v___x_2506_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2507_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2506_, v___f_2486_, v_a_2474_);
return v___x_2507_;
}
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
lean_dec_ref(v___f_2486_);
lean_dec_ref(v_e_2472_);
v_a_2508_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2487_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2487_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
v___jp_2482_:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2483_ = lean_box(0);
v___x_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2483_);
return v___x_2484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___boxed(lean_object* v_e_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_);
lean_dec(v_a_2524_);
lean_dec_ref(v_a_2523_);
lean_dec(v_a_2522_);
lean_dec_ref(v_a_2521_);
lean_dec(v_a_2520_);
lean_dec_ref(v_a_2519_);
lean_dec(v_a_2518_);
lean_dec_ref(v_a_2517_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(lean_object* v_e_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_){
_start:
{
lean_object* v___x_2540_; 
v___x_2540_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2527_, v_a_2528_, v_a_2529_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___boxed(lean_object* v_e_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(v_e_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_);
lean_dec(v_a_2552_);
lean_dec_ref(v_a_2551_);
lean_dec(v_a_2550_);
lean_dec_ref(v_a_2549_);
lean_dec(v_a_2548_);
lean_dec_ref(v_a_2547_);
lean_dec(v_a_2546_);
lean_dec_ref(v_a_2545_);
lean_dec(v_a_2544_);
lean_dec(v_a_2543_);
lean_dec_ref(v_a_2542_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0(lean_object* v_00_u03b2_2555_, lean_object* v_x_2556_, lean_object* v_x_2557_, lean_object* v_x_2558_){
_start:
{
lean_object* v___x_2559_; 
v___x_2559_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_x_2556_, v_x_2557_, v_x_2558_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(lean_object* v_00_u03b2_2560_, lean_object* v_x_2561_, size_t v_x_2562_, size_t v_x_2563_, lean_object* v_x_2564_, lean_object* v_x_2565_){
_start:
{
lean_object* v___x_2566_; 
v___x_2566_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2561_, v_x_2562_, v_x_2563_, v_x_2564_, v_x_2565_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2567_, lean_object* v_x_2568_, lean_object* v_x_2569_, lean_object* v_x_2570_, lean_object* v_x_2571_, lean_object* v_x_2572_){
_start:
{
size_t v_x_6751__boxed_2573_; size_t v_x_6752__boxed_2574_; lean_object* v_res_2575_; 
v_x_6751__boxed_2573_ = lean_unbox_usize(v_x_2569_);
lean_dec(v_x_2569_);
v_x_6752__boxed_2574_ = lean_unbox_usize(v_x_2570_);
lean_dec(v_x_2570_);
v_res_2575_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(v_00_u03b2_2567_, v_x_2568_, v_x_6751__boxed_2573_, v_x_6752__boxed_2574_, v_x_2571_, v_x_2572_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2576_, lean_object* v_n_2577_, lean_object* v_k_2578_, lean_object* v_v_2579_){
_start:
{
lean_object* v___x_2580_; 
v___x_2580_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v_n_2577_, v_k_2578_, v_v_2579_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2581_, size_t v_depth_2582_, lean_object* v_keys_2583_, lean_object* v_vals_2584_, lean_object* v_heq_2585_, lean_object* v_i_2586_, lean_object* v_entries_2587_){
_start:
{
lean_object* v___x_2588_; 
v___x_2588_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_2582_, v_keys_2583_, v_vals_2584_, v_i_2586_, v_entries_2587_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2589_, lean_object* v_depth_2590_, lean_object* v_keys_2591_, lean_object* v_vals_2592_, lean_object* v_heq_2593_, lean_object* v_i_2594_, lean_object* v_entries_2595_){
_start:
{
size_t v_depth_boxed_2596_; lean_object* v_res_2597_; 
v_depth_boxed_2596_ = lean_unbox_usize(v_depth_2590_);
lean_dec(v_depth_2590_);
v_res_2597_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(v_00_u03b2_2589_, v_depth_boxed_2596_, v_keys_2591_, v_vals_2592_, v_heq_2593_, v_i_2594_, v_entries_2595_);
lean_dec_ref(v_vals_2592_);
lean_dec_ref(v_keys_2591_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2598_, lean_object* v_x_2599_, lean_object* v_x_2600_, lean_object* v_x_2601_, lean_object* v_x_2602_){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2599_, v_x_2600_, v_x_2601_, v_x_2602_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0(lean_object* v_e_2604_, lean_object* v___f_2605_, lean_object* v___f_2606_, lean_object* v_size_2607_, lean_object* v_s_2608_){
_start:
{
lean_object* v_vars_2609_; lean_object* v_varMap_2610_; lean_object* v_denote_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2620_; 
v_vars_2609_ = lean_ctor_get(v_s_2608_, 0);
v_varMap_2610_ = lean_ctor_get(v_s_2608_, 1);
v_denote_2611_ = lean_ctor_get(v_s_2608_, 2);
v_isSharedCheck_2620_ = !lean_is_exclusive(v_s_2608_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2613_ = v_s_2608_;
v_isShared_2614_ = v_isSharedCheck_2620_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_denote_2611_);
lean_inc(v_varMap_2610_);
lean_inc(v_vars_2609_);
lean_dec(v_s_2608_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2620_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2618_; 
lean_inc_ref(v_e_2604_);
v___x_2615_ = l_Lean_PersistentArray_push___redArg(v_vars_2609_, v_e_2604_);
v___x_2616_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2605_, v___f_2606_, v_varMap_2610_, v_e_2604_, v_size_2607_);
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 1, v___x_2616_);
lean_ctor_set(v___x_2613_, 0, v___x_2615_);
v___x_2618_ = v___x_2613_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2615_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v___x_2616_);
lean_ctor_set(v_reuseFailAlloc_2619_, 2, v_denote_2611_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1(lean_object* v_toPure_2621_, lean_object* v_size_2622_, lean_object* v_____r_2623_){
_start:
{
lean_object* v___x_2624_; 
v___x_2624_ = lean_apply_2(v_toPure_2621_, lean_box(0), v_size_2622_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2(lean_object* v_e_2625_, lean_object* v_inst_2626_, lean_object* v_toBind_2627_, lean_object* v___f_2628_, lean_object* v_____r_2629_){
_start:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2630_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2631_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SolverExtension_markTerm___boxed), 14, 3);
lean_closure_set(v___x_2631_, 0, lean_box(0));
lean_closure_set(v___x_2631_, 1, v___x_2630_);
lean_closure_set(v___x_2631_, 2, v_e_2625_);
v___x_2632_ = lean_apply_2(v_inst_2626_, lean_box(0), v___x_2631_);
v___x_2633_ = lean_apply_4(v_toBind_2627_, lean_box(0), lean_box(0), v___x_2632_, v___f_2628_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3(lean_object* v_inst_2634_, lean_object* v_e_2635_, lean_object* v_toBind_2636_, lean_object* v___f_2637_, lean_object* v_____r_2638_){
_start:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2639_ = lean_apply_1(v_inst_2634_, v_e_2635_);
v___x_2640_ = lean_apply_4(v_toBind_2636_, lean_box(0), lean_box(0), v___x_2639_, v___f_2637_);
return v___x_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4(lean_object* v___f_2641_, lean_object* v___f_2642_, lean_object* v_e_2643_, lean_object* v_toPure_2644_, lean_object* v_inst_2645_, lean_object* v_toBind_2646_, lean_object* v_inst_2647_, lean_object* v_modifyRingState_2648_, lean_object* v_s_2649_){
_start:
{
lean_object* v_vars_2650_; lean_object* v_varMap_2651_; lean_object* v___x_2652_; 
v_vars_2650_ = lean_ctor_get(v_s_2649_, 0);
lean_inc_ref(v_vars_2650_);
v_varMap_2651_ = lean_ctor_get(v_s_2649_, 1);
lean_inc_ref(v_varMap_2651_);
lean_dec_ref(v_s_2649_);
lean_inc_ref(v_e_2643_);
lean_inc_ref(v___f_2642_);
lean_inc_ref(v___f_2641_);
v___x_2652_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2641_, v___f_2642_, v_varMap_2651_, v_e_2643_);
lean_dec_ref(v_varMap_2651_);
if (lean_obj_tag(v___x_2652_) == 1)
{
lean_object* v_val_2653_; lean_object* v___x_2654_; 
lean_dec_ref(v_vars_2650_);
lean_dec(v_modifyRingState_2648_);
lean_dec(v_inst_2647_);
lean_dec(v_toBind_2646_);
lean_dec(v_inst_2645_);
lean_dec_ref(v_e_2643_);
lean_dec_ref(v___f_2642_);
lean_dec_ref(v___f_2641_);
v_val_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_val_2653_);
lean_dec_ref_known(v___x_2652_, 1);
v___x_2654_ = lean_apply_2(v_toPure_2644_, lean_box(0), v_val_2653_);
return v___x_2654_;
}
else
{
lean_object* v_size_2655_; lean_object* v___f_2656_; lean_object* v___f_2657_; lean_object* v___f_2658_; lean_object* v___f_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
lean_dec(v___x_2652_);
v_size_2655_ = lean_ctor_get(v_vars_2650_, 2);
lean_inc_n(v_size_2655_, 2);
lean_dec_ref(v_vars_2650_);
lean_inc_ref_n(v_e_2643_, 2);
v___f_2656_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2656_, 0, v_e_2643_);
lean_closure_set(v___f_2656_, 1, v___f_2641_);
lean_closure_set(v___f_2656_, 2, v___f_2642_);
lean_closure_set(v___f_2656_, 3, v_size_2655_);
v___f_2657_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2657_, 0, v_toPure_2644_);
lean_closure_set(v___f_2657_, 1, v_size_2655_);
lean_inc_n(v_toBind_2646_, 2);
v___f_2658_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2658_, 0, v_e_2643_);
lean_closure_set(v___f_2658_, 1, v_inst_2645_);
lean_closure_set(v___f_2658_, 2, v_toBind_2646_);
lean_closure_set(v___f_2658_, 3, v___f_2657_);
v___f_2659_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2659_, 0, v_inst_2647_);
lean_closure_set(v___f_2659_, 1, v_e_2643_);
lean_closure_set(v___f_2659_, 2, v_toBind_2646_);
lean_closure_set(v___f_2659_, 3, v___f_2658_);
v___x_2660_ = lean_apply_1(v_modifyRingState_2648_, v___f_2656_);
v___x_2661_ = lean_apply_4(v_toBind_2646_, lean_box(0), lean_box(0), v___x_2660_, v___f_2659_);
return v___x_2661_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(lean_object* v_inst_2664_, lean_object* v_inst_2665_, lean_object* v_inst_2666_, lean_object* v_inst_2667_, lean_object* v_e_2668_){
_start:
{
lean_object* v_toApplicative_2669_; lean_object* v_toBind_2670_; lean_object* v_getRingState_2671_; lean_object* v_modifyRingState_2672_; lean_object* v_toPure_2673_; lean_object* v___f_2674_; lean_object* v___f_2675_; lean_object* v___f_2676_; lean_object* v___x_2677_; 
v_toApplicative_2669_ = lean_ctor_get(v_inst_2665_, 0);
lean_inc_ref(v_toApplicative_2669_);
v_toBind_2670_ = lean_ctor_get(v_inst_2665_, 1);
lean_inc_n(v_toBind_2670_, 2);
lean_dec_ref(v_inst_2665_);
v_getRingState_2671_ = lean_ctor_get(v_inst_2666_, 0);
lean_inc(v_getRingState_2671_);
v_modifyRingState_2672_ = lean_ctor_get(v_inst_2666_, 1);
lean_inc(v_modifyRingState_2672_);
lean_dec_ref(v_inst_2666_);
v_toPure_2673_ = lean_ctor_get(v_toApplicative_2669_, 1);
lean_inc(v_toPure_2673_);
lean_dec_ref(v_toApplicative_2669_);
v___f_2674_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0));
v___f_2675_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1));
v___f_2676_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2676_, 0, v___f_2674_);
lean_closure_set(v___f_2676_, 1, v___f_2675_);
lean_closure_set(v___f_2676_, 2, v_e_2668_);
lean_closure_set(v___f_2676_, 3, v_toPure_2673_);
lean_closure_set(v___f_2676_, 4, v_inst_2664_);
lean_closure_set(v___f_2676_, 5, v_toBind_2670_);
lean_closure_set(v___f_2676_, 6, v_inst_2667_);
lean_closure_set(v___f_2676_, 7, v_modifyRingState_2672_);
v___x_2677_ = lean_apply_4(v_toBind_2670_, lean_box(0), lean_box(0), v_getRingState_2671_, v___f_2676_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore(lean_object* v_m_2678_, lean_object* v_inst_2679_, lean_object* v_inst_2680_, lean_object* v_inst_2681_, lean_object* v_inst_2682_, lean_object* v_e_2683_){
_start:
{
lean_object* v___x_2684_; 
v___x_2684_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v_inst_2679_, v_inst_2680_, v_inst_2681_, v_inst_2682_, v_e_2683_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0(lean_object* v_e_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
lean_object* v___x_2698_; 
v___x_2698_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2685_, v___y_2686_, v___y_2687_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0___boxed(lean_object* v_e_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0(v_e_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
return v_res_2712_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2716_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___closed__0));
v___x_2717_ = l_Lean_stringToMessageData(v___x_2716_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0(lean_object* v___x_2718_, lean_object* v___x_2719_, lean_object* v___f_2720_, lean_object* v___x_2721_, lean_object* v___f_2722_, lean_object* v_e_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
lean_object* v___x_2736_; 
v___x_2736_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_2723_, v___y_2725_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; uint8_t v___x_2738_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2737_);
lean_dec_ref_known(v___x_2736_, 1);
v___x_2738_ = lean_unbox(v_a_2737_);
lean_dec(v_a_2737_);
if (v___x_2738_ == 0)
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_1454__overap_2742_; lean_object* v___x_2743_; 
v___x_2739_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___closed__1);
lean_inc_ref(v_e_2723_);
v___x_2740_ = l_Lean_indentExpr(v_e_2723_);
v___x_2741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2739_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
lean_inc_ref(v___x_2718_);
v___x_1454__overap_2742_ = l_Lean_throwError___redArg(v___x_2718_, v___x_2719_, v___x_2741_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
lean_inc(v___y_2730_);
lean_inc_ref(v___y_2729_);
lean_inc(v___y_2728_);
lean_inc_ref(v___y_2727_);
lean_inc(v___y_2726_);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
v___x_2743_ = lean_apply_12(v___x_1454__overap_2742_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, lean_box(0));
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v___x_1457__overap_2744_; lean_object* v___x_2745_; 
lean_dec_ref_known(v___x_2743_, 1);
v___x_1457__overap_2744_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v___f_2720_, v___x_2718_, v___x_2721_, v___f_2722_, v_e_2723_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
lean_inc(v___y_2730_);
lean_inc_ref(v___y_2729_);
lean_inc(v___y_2728_);
lean_inc_ref(v___y_2727_);
lean_inc(v___y_2726_);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
v___x_2745_ = lean_apply_12(v___x_1457__overap_2744_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, lean_box(0));
return v___x_2745_;
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
lean_dec_ref(v_e_2723_);
lean_dec_ref(v___f_2722_);
lean_dec_ref(v___x_2721_);
lean_dec(v___f_2720_);
lean_dec_ref(v___x_2718_);
v_a_2746_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___x_2743_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2743_);
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
lean_object* v___x_1461__overap_2754_; lean_object* v___x_2755_; 
lean_dec_ref(v___x_2719_);
v___x_1461__overap_2754_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v___f_2720_, v___x_2718_, v___x_2721_, v___f_2722_, v_e_2723_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
lean_inc(v___y_2730_);
lean_inc_ref(v___y_2729_);
lean_inc(v___y_2728_);
lean_inc_ref(v___y_2727_);
lean_inc(v___y_2726_);
lean_inc(v___y_2725_);
lean_inc_ref(v___y_2724_);
v___x_2755_ = lean_apply_12(v___x_1461__overap_2754_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, lean_box(0));
return v___x_2755_;
}
}
else
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
lean_dec_ref(v_e_2723_);
lean_dec_ref(v___f_2722_);
lean_dec_ref(v___x_2721_);
lean_dec(v___f_2720_);
lean_dec_ref(v___x_2719_);
lean_dec_ref(v___x_2718_);
v_a_2756_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___x_2736_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2736_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___boxed(lean_object** _args){
lean_object* v___x_2764_ = _args[0];
lean_object* v___x_2765_ = _args[1];
lean_object* v___f_2766_ = _args[2];
lean_object* v___x_2767_ = _args[3];
lean_object* v___f_2768_ = _args[4];
lean_object* v_e_2769_ = _args[5];
lean_object* v___y_2770_ = _args[6];
lean_object* v___y_2771_ = _args[7];
lean_object* v___y_2772_ = _args[8];
lean_object* v___y_2773_ = _args[9];
lean_object* v___y_2774_ = _args[10];
lean_object* v___y_2775_ = _args[11];
lean_object* v___y_2776_ = _args[12];
lean_object* v___y_2777_ = _args[13];
lean_object* v___y_2778_ = _args[14];
lean_object* v___y_2779_ = _args[15];
lean_object* v___y_2780_ = _args[16];
lean_object* v___y_2781_ = _args[17];
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0(v___x_2764_, v___x_2765_, v___f_2766_, v___x_2767_, v___f_2768_, v_e_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
return v_res_2782_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__0(void){
_start:
{
lean_object* v___x_2783_; 
v___x_2783_ = l_instMonadEIO___redArg();
return v___x_2783_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__1(void){
_start:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__0);
v___x_2785_ = l_StateRefT_x27_instMonad___redArg(v___x_2784_);
return v___x_2785_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__7(void){
_start:
{
lean_object* v___x_2791_; lean_object* v___f_2792_; 
v___x_2791_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_2792_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2792_, 0, v___x_2791_);
return v___f_2792_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__8(void){
_start:
{
lean_object* v___x_2793_; lean_object* v___f_2794_; 
v___x_2793_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_2794_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2794_, 0, v___x_2793_);
return v___f_2794_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__9(void){
_start:
{
lean_object* v___f_2795_; lean_object* v___f_2796_; lean_object* v___x_2797_; 
v___f_2795_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__8, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__8_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__8);
v___f_2796_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__7, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__7_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__7);
v___x_2797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2797_, 0, v___f_2796_);
lean_ctor_set(v___x_2797_, 1, v___f_2795_);
return v___x_2797_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__10(void){
_start:
{
lean_object* v___x_2798_; lean_object* v___f_2799_; 
v___x_2798_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__9, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__9_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__9);
v___f_2799_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2799_, 0, v___x_2798_);
return v___f_2799_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__11(void){
_start:
{
lean_object* v___x_2800_; lean_object* v___f_2801_; 
v___x_2800_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__9, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__9_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__9);
v___f_2801_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2801_, 0, v___x_2800_);
return v___f_2801_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__12(void){
_start:
{
lean_object* v___f_2802_; lean_object* v___f_2803_; lean_object* v___x_2804_; 
v___f_2802_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__11, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__11_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__11);
v___f_2803_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__10, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__10_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__10);
v___x_2804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___f_2803_);
lean_ctor_set(v___x_2804_, 1, v___f_2802_);
return v___x_2804_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__13(void){
_start:
{
lean_object* v___x_2805_; lean_object* v___f_2806_; 
v___x_2805_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__12);
v___f_2806_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2806_, 0, v___x_2805_);
return v___f_2806_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__14(void){
_start:
{
lean_object* v___x_2807_; lean_object* v___f_2808_; 
v___x_2807_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__12);
v___f_2808_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2808_, 0, v___x_2807_);
return v___f_2808_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__15(void){
_start:
{
lean_object* v___f_2809_; lean_object* v___f_2810_; lean_object* v___x_2811_; 
v___f_2809_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__14, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__14_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__14);
v___f_2810_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__13, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__13_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__13);
v___x_2811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2811_, 0, v___f_2810_);
lean_ctor_set(v___x_2811_, 1, v___f_2809_);
return v___x_2811_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__16(void){
_start:
{
lean_object* v___x_2812_; lean_object* v___f_2813_; 
v___x_2812_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__15, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__15_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__15);
v___f_2813_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2813_, 0, v___x_2812_);
return v___f_2813_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__17(void){
_start:
{
lean_object* v___x_2814_; lean_object* v___f_2815_; 
v___x_2814_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__15, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__15_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__15);
v___f_2815_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2815_, 0, v___x_2814_);
return v___f_2815_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__18(void){
_start:
{
lean_object* v___f_2816_; lean_object* v___f_2817_; lean_object* v___x_2818_; 
v___f_2816_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__17, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__17_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__17);
v___f_2817_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__16, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__16_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__16);
v___x_2818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2818_, 0, v___f_2817_);
lean_ctor_set(v___x_2818_, 1, v___f_2816_);
return v___x_2818_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__19(void){
_start:
{
lean_object* v___x_2819_; lean_object* v___f_2820_; 
v___x_2819_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__18, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__18_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__18);
v___f_2820_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2820_, 0, v___x_2819_);
return v___f_2820_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__20(void){
_start:
{
lean_object* v___x_2821_; lean_object* v___f_2822_; 
v___x_2821_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__18, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__18_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__18);
v___f_2822_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2822_, 0, v___x_2821_);
return v___f_2822_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__21(void){
_start:
{
lean_object* v___f_2823_; lean_object* v___f_2824_; lean_object* v___x_2825_; 
v___f_2823_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__20, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__20_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__20);
v___f_2824_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__19, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__19_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__19);
v___x_2825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2825_, 0, v___f_2824_);
lean_ctor_set(v___x_2825_, 1, v___f_2823_);
return v___x_2825_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__22(void){
_start:
{
lean_object* v___x_2826_; lean_object* v___f_2827_; 
v___x_2826_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__21, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__21_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__21);
v___f_2827_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2827_, 0, v___x_2826_);
return v___f_2827_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__23(void){
_start:
{
lean_object* v___x_2828_; lean_object* v___f_2829_; 
v___x_2828_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__21, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__21_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__21);
v___f_2829_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2829_, 0, v___x_2828_);
return v___f_2829_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__24(void){
_start:
{
lean_object* v___f_2830_; lean_object* v___f_2831_; lean_object* v___x_2832_; 
v___f_2830_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__23, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__23_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__23);
v___f_2831_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__22, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__22_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__22);
v___x_2832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2832_, 0, v___f_2831_);
lean_ctor_set(v___x_2832_, 1, v___f_2830_);
return v___x_2832_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__25(void){
_start:
{
lean_object* v___x_2833_; lean_object* v___f_2834_; 
v___x_2833_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__24, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__24_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__24);
v___f_2834_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2834_, 0, v___x_2833_);
return v___f_2834_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__26(void){
_start:
{
lean_object* v___x_2835_; lean_object* v___f_2836_; 
v___x_2835_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__24, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__24_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__24);
v___f_2836_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2836_, 0, v___x_2835_);
return v___f_2836_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__27(void){
_start:
{
lean_object* v___f_2837_; lean_object* v___f_2838_; lean_object* v___x_2839_; 
v___f_2837_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__26, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__26_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__26);
v___f_2838_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__25, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__25_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__25);
v___x_2839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2839_, 0, v___f_2838_);
lean_ctor_set(v___x_2839_, 1, v___f_2837_);
return v___x_2839_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__28(void){
_start:
{
lean_object* v___x_2840_; lean_object* v___f_2841_; 
v___x_2840_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__27, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__27_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__27);
v___f_2841_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2841_, 0, v___x_2840_);
return v___f_2841_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__29(void){
_start:
{
lean_object* v___x_2842_; lean_object* v___f_2843_; 
v___x_2842_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__27, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__27_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__27);
v___f_2843_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2843_, 0, v___x_2842_);
return v___f_2843_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__30(void){
_start:
{
lean_object* v___f_2844_; lean_object* v___f_2845_; lean_object* v___x_2846_; 
v___f_2844_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__29, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__29_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__29);
v___f_2845_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__28, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__28_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__28);
v___x_2846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2846_, 0, v___f_2845_);
lean_ctor_set(v___x_2846_, 1, v___f_2844_);
return v___x_2846_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__31(void){
_start:
{
lean_object* v___x_2847_; lean_object* v___f_2848_; 
v___x_2847_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__30, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__30_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__30);
v___f_2848_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2848_, 0, v___x_2847_);
return v___f_2848_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__32(void){
_start:
{
lean_object* v___x_2849_; lean_object* v___f_2850_; 
v___x_2849_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__30, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__30_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__30);
v___f_2850_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2850_, 0, v___x_2849_);
return v___f_2850_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__33(void){
_start:
{
lean_object* v___f_2851_; lean_object* v___f_2852_; lean_object* v___x_2853_; 
v___f_2851_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__32, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__32_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__32);
v___f_2852_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__31, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__31_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__31);
v___x_2853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___f_2852_);
lean_ctor_set(v___x_2853_, 1, v___f_2851_);
return v___x_2853_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__37(void){
_start:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2857_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2858_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__36));
v___x_2859_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__35));
v___x_2860_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2859_, v___x_2858_, v___x_2857_);
return v___x_2860_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__38(void){
_start:
{
lean_object* v___x_2861_; lean_object* v___f_2862_; lean_object* v___f_2863_; lean_object* v___x_2864_; 
v___x_2861_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__37, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__37_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__37);
v___f_2862_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6));
v___f_2863_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__34));
v___x_2864_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2863_, v___f_2862_, v___x_2861_);
return v___x_2864_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__39(void){
_start:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2865_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__38, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__38_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__38);
v___x_2866_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__36));
v___x_2867_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__35));
v___x_2868_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2867_, v___x_2866_, v___x_2865_);
return v___x_2868_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__40(void){
_start:
{
lean_object* v___x_2869_; lean_object* v___f_2870_; lean_object* v___f_2871_; lean_object* v___x_2872_; 
v___x_2869_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__39, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__39_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__39);
v___f_2870_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6));
v___f_2871_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__34));
v___x_2872_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2871_, v___f_2870_, v___x_2869_);
return v___x_2872_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__41(void){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2873_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__40, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__40_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__40);
v___x_2874_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__36));
v___x_2875_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__35));
v___x_2876_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2875_, v___x_2874_, v___x_2873_);
return v___x_2876_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__42(void){
_start:
{
lean_object* v___x_2877_; lean_object* v___f_2878_; lean_object* v___f_2879_; lean_object* v___x_2880_; 
v___x_2877_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__41, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__41_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__41);
v___f_2878_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6));
v___f_2879_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__34));
v___x_2880_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2879_, v___f_2878_, v___x_2877_);
return v___x_2880_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__43(void){
_start:
{
lean_object* v___x_2881_; lean_object* v___f_2882_; lean_object* v___f_2883_; lean_object* v___x_2884_; 
v___x_2881_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__42, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__42_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__42);
v___f_2882_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6));
v___f_2883_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__34));
v___x_2884_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2883_, v___f_2882_, v___x_2881_);
return v___x_2884_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__44(void){
_start:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
v___x_2885_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__43, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__43_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__43);
v___x_2886_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__36));
v___x_2887_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__35));
v___x_2888_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2887_, v___x_2886_, v___x_2885_);
return v___x_2888_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__45(void){
_start:
{
lean_object* v___x_2889_; lean_object* v___f_2890_; lean_object* v___f_2891_; lean_object* v___x_2892_; 
v___x_2889_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__44, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__44_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__44);
v___f_2890_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6));
v___f_2891_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__34));
v___x_2892_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2891_, v___f_2890_, v___x_2889_);
return v___x_2892_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__48(void){
_start:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___f_2899_; 
v___x_2897_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__36));
v___x_2898_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_2899_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2899_, 0, v___x_2898_);
lean_closure_set(v___f_2899_, 1, v___x_2897_);
return v___f_2899_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__49(void){
_start:
{
lean_object* v___f_2900_; lean_object* v___f_2901_; lean_object* v___f_2902_; 
v___f_2900_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6));
v___f_2901_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__48, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__48_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__48);
v___f_2902_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2902_, 0, v___f_2901_);
lean_closure_set(v___f_2902_, 1, v___f_2900_);
return v___f_2902_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__50(void){
_start:
{
lean_object* v___x_2903_; lean_object* v___f_2904_; lean_object* v___f_2905_; 
v___x_2903_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__36));
v___f_2904_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__49, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__49_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__49);
v___f_2905_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2905_, 0, v___f_2904_);
lean_closure_set(v___f_2905_, 1, v___x_2903_);
return v___f_2905_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__51(void){
_start:
{
lean_object* v___f_2906_; lean_object* v___f_2907_; lean_object* v___f_2908_; 
v___f_2906_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6));
v___f_2907_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__50, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__50_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__50);
v___f_2908_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2908_, 0, v___f_2907_);
lean_closure_set(v___f_2908_, 1, v___f_2906_);
return v___f_2908_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__52(void){
_start:
{
lean_object* v___f_2909_; lean_object* v___f_2910_; lean_object* v___f_2911_; 
v___f_2909_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6));
v___f_2910_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__51, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__51_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__51);
v___f_2911_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2911_, 0, v___f_2910_);
lean_closure_set(v___f_2911_, 1, v___f_2909_);
return v___f_2911_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__53(void){
_start:
{
lean_object* v___x_2912_; lean_object* v___f_2913_; lean_object* v___f_2914_; 
v___x_2912_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__36));
v___f_2913_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__52, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__52_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__52);
v___f_2914_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2914_, 0, v___f_2913_);
lean_closure_set(v___f_2914_, 1, v___x_2912_);
return v___f_2914_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__54(void){
_start:
{
lean_object* v___f_2915_; lean_object* v___f_2916_; lean_object* v___f_2917_; 
v___f_2915_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6));
v___f_2916_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__53, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__53_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__53);
v___f_2917_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2917_, 0, v___f_2916_);
lean_closure_set(v___f_2917_, 1, v___f_2915_);
return v___f_2917_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM(void){
_start:
{
lean_object* v___x_2918_; lean_object* v_toApplicative_2919_; lean_object* v_toFunctor_2920_; lean_object* v_toSeq_2921_; lean_object* v_toSeqLeft_2922_; lean_object* v_toSeqRight_2923_; lean_object* v___f_2924_; lean_object* v___f_2925_; lean_object* v___f_2926_; lean_object* v___f_2927_; lean_object* v___x_2928_; lean_object* v___f_2929_; lean_object* v___f_2930_; lean_object* v___f_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v_toApplicative_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2988_; 
v___x_2918_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__1);
v_toApplicative_2919_ = lean_ctor_get(v___x_2918_, 0);
v_toFunctor_2920_ = lean_ctor_get(v_toApplicative_2919_, 0);
v_toSeq_2921_ = lean_ctor_get(v_toApplicative_2919_, 2);
v_toSeqLeft_2922_ = lean_ctor_get(v_toApplicative_2919_, 3);
v_toSeqRight_2923_ = lean_ctor_get(v_toApplicative_2919_, 4);
v___f_2924_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__2));
v___f_2925_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__3));
lean_inc_ref_n(v_toFunctor_2920_, 2);
v___f_2926_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2926_, 0, v_toFunctor_2920_);
v___f_2927_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2927_, 0, v_toFunctor_2920_);
v___x_2928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2928_, 0, v___f_2926_);
lean_ctor_set(v___x_2928_, 1, v___f_2927_);
lean_inc(v_toSeqRight_2923_);
v___f_2929_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2929_, 0, v_toSeqRight_2923_);
lean_inc(v_toSeqLeft_2922_);
v___f_2930_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2930_, 0, v_toSeqLeft_2922_);
lean_inc(v_toSeq_2921_);
v___f_2931_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2931_, 0, v_toSeq_2921_);
v___x_2932_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2928_);
lean_ctor_set(v___x_2932_, 1, v___f_2924_);
lean_ctor_set(v___x_2932_, 2, v___f_2931_);
lean_ctor_set(v___x_2932_, 3, v___f_2930_);
lean_ctor_set(v___x_2932_, 4, v___f_2929_);
v___x_2933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2932_);
lean_ctor_set(v___x_2933_, 1, v___f_2925_);
v___x_2934_ = l_StateRefT_x27_instMonad___redArg(v___x_2933_);
v_toApplicative_2935_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2988_ == 0)
{
lean_object* v_unused_2989_; 
v_unused_2989_ = lean_ctor_get(v___x_2934_, 1);
lean_dec(v_unused_2989_);
v___x_2937_ = v___x_2934_;
v_isShared_2938_ = v_isSharedCheck_2988_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_toApplicative_2935_);
lean_dec(v___x_2934_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2988_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v_toFunctor_2939_; lean_object* v_toSeq_2940_; lean_object* v_toSeqLeft_2941_; lean_object* v_toSeqRight_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2986_; 
v_toFunctor_2939_ = lean_ctor_get(v_toApplicative_2935_, 0);
v_toSeq_2940_ = lean_ctor_get(v_toApplicative_2935_, 2);
v_toSeqLeft_2941_ = lean_ctor_get(v_toApplicative_2935_, 3);
v_toSeqRight_2942_ = lean_ctor_get(v_toApplicative_2935_, 4);
v_isSharedCheck_2986_ = !lean_is_exclusive(v_toApplicative_2935_);
if (v_isSharedCheck_2986_ == 0)
{
lean_object* v_unused_2987_; 
v_unused_2987_ = lean_ctor_get(v_toApplicative_2935_, 1);
lean_dec(v_unused_2987_);
v___x_2944_ = v_toApplicative_2935_;
v_isShared_2945_ = v_isSharedCheck_2986_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_toSeqRight_2942_);
lean_inc(v_toSeqLeft_2941_);
lean_inc(v_toSeq_2940_);
lean_inc(v_toFunctor_2939_);
lean_dec(v_toApplicative_2935_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2986_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___f_2946_; lean_object* v___f_2947_; lean_object* v___f_2948_; lean_object* v___f_2949_; lean_object* v___x_2950_; lean_object* v___f_2951_; lean_object* v___f_2952_; lean_object* v___f_2953_; lean_object* v___x_2955_; 
v___f_2946_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__4));
v___f_2947_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__5));
lean_inc_ref(v_toFunctor_2939_);
v___f_2948_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2948_, 0, v_toFunctor_2939_);
v___f_2949_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2949_, 0, v_toFunctor_2939_);
v___x_2950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___f_2948_);
lean_ctor_set(v___x_2950_, 1, v___f_2949_);
v___f_2951_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2951_, 0, v_toSeqRight_2942_);
v___f_2952_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2952_, 0, v_toSeqLeft_2941_);
v___f_2953_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2953_, 0, v_toSeq_2940_);
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 4, v___f_2951_);
lean_ctor_set(v___x_2944_, 3, v___f_2952_);
lean_ctor_set(v___x_2944_, 2, v___f_2953_);
lean_ctor_set(v___x_2944_, 1, v___f_2946_);
lean_ctor_set(v___x_2944_, 0, v___x_2950_);
v___x_2955_ = v___x_2944_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v___x_2950_);
lean_ctor_set(v_reuseFailAlloc_2985_, 1, v___f_2946_);
lean_ctor_set(v_reuseFailAlloc_2985_, 2, v___f_2953_);
lean_ctor_set(v_reuseFailAlloc_2985_, 3, v___f_2952_);
lean_ctor_set(v_reuseFailAlloc_2985_, 4, v___f_2951_);
v___x_2955_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
lean_object* v___x_2957_; 
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 1, v___f_2947_);
lean_ctor_set(v___x_2937_, 0, v___x_2955_);
v___x_2957_ = v___x_2937_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2955_);
lean_ctor_set(v_reuseFailAlloc_2984_, 1, v___f_2947_);
v___x_2957_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v_toApplicative_2966_; lean_object* v_toBind_2967_; lean_object* v_getCommRingState_2968_; lean_object* v_modifyCommRingState_2969_; lean_object* v_toPure_2970_; lean_object* v___f_2971_; lean_object* v___f_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v_toMonadRef_2977_; lean_object* v___f_2978_; lean_object* v___f_2979_; lean_object* v___f_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___f_2983_; 
v___x_2958_ = l_StateRefT_x27_instMonad___redArg(v___x_2957_);
v___x_2959_ = l_ReaderT_instMonad___redArg(v___x_2958_);
v___x_2960_ = l_StateRefT_x27_instMonad___redArg(v___x_2959_);
v___x_2961_ = l_ReaderT_instMonad___redArg(v___x_2960_);
v___x_2962_ = l_ReaderT_instMonad___redArg(v___x_2961_);
v___x_2963_ = l_StateRefT_x27_instMonad___redArg(v___x_2962_);
v___x_2964_ = l_ReaderT_instMonad___redArg(v___x_2963_);
v___x_2965_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM;
v_toApplicative_2966_ = lean_ctor_get(v___x_2964_, 0);
v_toBind_2967_ = lean_ctor_get(v___x_2964_, 1);
v_getCommRingState_2968_ = lean_ctor_get(v___x_2965_, 0);
v_modifyCommRingState_2969_ = lean_ctor_get(v___x_2965_, 1);
v_toPure_2970_ = lean_ctor_get(v_toApplicative_2966_, 1);
lean_inc(v_modifyCommRingState_2969_);
v___f_2971_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2971_, 0, v_modifyCommRingState_2969_);
lean_inc(v_toPure_2970_);
v___f_2972_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2972_, 0, v_toPure_2970_);
lean_inc(v_toBind_2967_);
lean_inc(v_getCommRingState_2968_);
v___x_2973_ = lean_apply_4(v_toBind_2967_, lean_box(0), lean_box(0), v_getCommRingState_2968_, v___f_2972_);
v___x_2974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2973_);
lean_ctor_set(v___x_2974_, 1, v___f_2971_);
v___x_2975_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__33, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__33_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__33);
v___x_2976_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__45, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__45_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__45);
v_toMonadRef_2977_ = lean_ctor_get(v___x_2976_, 0);
v___f_2978_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__47));
v___f_2979_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___closed__0));
v___f_2980_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__54, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__54_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__54);
lean_inc_ref(v___x_2964_);
v___x_2981_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_2980_, v___x_2964_);
lean_inc_ref(v_toMonadRef_2977_);
v___x_2982_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2975_);
lean_ctor_set(v___x_2982_, 1, v_toMonadRef_2977_);
lean_ctor_set(v___x_2982_, 2, v___x_2981_);
v___f_2983_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___boxed), 18, 5);
lean_closure_set(v___f_2983_, 0, v___x_2964_);
lean_closure_set(v___f_2983_, 1, v___x_2982_);
lean_closure_set(v___f_2983_, 2, v___f_2978_);
lean_closure_set(v___f_2983_, 3, v___x_2974_);
lean_closure_set(v___f_2983_, 4, v___f_2979_);
return v___f_2983_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0(void){
_start:
{
lean_object* v___x_2990_; lean_object* v_n_2991_; 
v___x_2990_ = lean_unsigned_to_nat(1u);
v_n_2991_ = l_Lean_mkRawNatLit(v___x_2990_);
return v_n_2991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(lean_object* v_u_3005_, lean_object* v_type_3006_, lean_object* v_semiringInst_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_){
_start:
{
lean_object* v_n_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v_ofNatInst_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v_n_3015_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0);
v___x_3016_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__5));
v___x_3017_ = lean_box(0);
v___x_3018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3018_, 0, v_u_3005_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
lean_inc_ref(v___x_3018_);
v___x_3019_ = l_Lean_mkConst(v___x_3016_, v___x_3018_);
lean_inc_ref(v_type_3006_);
v_ofNatInst_3020_ = l_Lean_mkApp3(v___x_3019_, v_type_3006_, v_semiringInst_3007_, v_n_3015_);
v___x_3021_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__7));
v___x_3022_ = l_Lean_mkConst(v___x_3021_, v___x_3018_);
v___x_3023_ = l_Lean_mkApp3(v___x_3022_, v_type_3006_, v_n_3015_, v_ofNatInst_3020_);
v___x_3024_ = l_Lean_Meta_Sym_canon(v___x_3023_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v___x_3026_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref_known(v___x_3024_, 1);
v___x_3026_ = l_Lean_Meta_Sym_shareCommon(v_a_3025_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_);
return v___x_3026_;
}
else
{
return v___x_3024_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___boxed(lean_object* v_u_3027_, lean_object* v_type_3028_, lean_object* v_semiringInst_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(v_u_3027_, v_type_3028_, v_semiringInst_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_);
lean_dec(v_a_3035_);
lean_dec_ref(v_a_3034_);
lean_dec(v_a_3033_);
lean_dec_ref(v_a_3032_);
lean_dec(v_a_3031_);
lean_dec_ref(v_a_3030_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne(lean_object* v_u_3038_, lean_object* v_type_3039_, lean_object* v_semiringInst_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_){
_start:
{
lean_object* v___x_3053_; 
v___x_3053_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(v_u_3038_, v_type_3039_, v_semiringInst_3040_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___boxed(lean_object* v_u_3054_, lean_object* v_type_3055_, lean_object* v_semiringInst_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne(v_u_3054_, v_type_3055_, v_semiringInst_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
lean_dec(v_a_3065_);
lean_dec_ref(v_a_3064_);
lean_dec(v_a_3063_);
lean_dec_ref(v_a_3062_);
lean_dec(v_a_3061_);
lean_dec_ref(v_a_3060_);
lean_dec(v_a_3059_);
lean_dec(v_a_3058_);
lean_dec_ref(v_a_3057_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___lam__0(lean_object* v_a_3070_, lean_object* v_s_3071_){
_start:
{
lean_object* v_toRing_3072_; lean_object* v_invFn_x3f_3073_; lean_object* v_divFn_x3f_3074_; lean_object* v_semiringId_x3f_3075_; lean_object* v_commSemiringInst_3076_; lean_object* v_commRingInst_3077_; lean_object* v_noZeroDivInst_x3f_3078_; lean_object* v_fieldInst_x3f_3079_; lean_object* v_powIdentityInst_x3f_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3112_; 
v_toRing_3072_ = lean_ctor_get(v_s_3071_, 0);
v_invFn_x3f_3073_ = lean_ctor_get(v_s_3071_, 1);
v_divFn_x3f_3074_ = lean_ctor_get(v_s_3071_, 2);
v_semiringId_x3f_3075_ = lean_ctor_get(v_s_3071_, 3);
v_commSemiringInst_3076_ = lean_ctor_get(v_s_3071_, 4);
v_commRingInst_3077_ = lean_ctor_get(v_s_3071_, 5);
v_noZeroDivInst_x3f_3078_ = lean_ctor_get(v_s_3071_, 6);
v_fieldInst_x3f_3079_ = lean_ctor_get(v_s_3071_, 7);
v_powIdentityInst_x3f_3080_ = lean_ctor_get(v_s_3071_, 8);
v_isSharedCheck_3112_ = !lean_is_exclusive(v_s_3071_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3082_ = v_s_3071_;
v_isShared_3083_ = v_isSharedCheck_3112_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_powIdentityInst_x3f_3080_);
lean_inc(v_fieldInst_x3f_3079_);
lean_inc(v_noZeroDivInst_x3f_3078_);
lean_inc(v_commRingInst_3077_);
lean_inc(v_commSemiringInst_3076_);
lean_inc(v_semiringId_x3f_3075_);
lean_inc(v_divFn_x3f_3074_);
lean_inc(v_invFn_x3f_3073_);
lean_inc(v_toRing_3072_);
lean_dec(v_s_3071_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3112_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v_id_3084_; lean_object* v_type_3085_; lean_object* v_u_3086_; lean_object* v_ringInst_3087_; lean_object* v_semiringInst_3088_; lean_object* v_charInst_x3f_3089_; uint8_t v_symbolicChar_3090_; lean_object* v_addFn_x3f_3091_; lean_object* v_mulFn_x3f_3092_; lean_object* v_subFn_x3f_3093_; lean_object* v_negFn_x3f_3094_; lean_object* v_powFn_x3f_3095_; lean_object* v_intCastFn_x3f_3096_; lean_object* v_natCastFn_x3f_3097_; lean_object* v_natSMulFn_x3f_3098_; lean_object* v_intSMulFn_x3f_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3110_; 
v_id_3084_ = lean_ctor_get(v_toRing_3072_, 0);
v_type_3085_ = lean_ctor_get(v_toRing_3072_, 1);
v_u_3086_ = lean_ctor_get(v_toRing_3072_, 2);
v_ringInst_3087_ = lean_ctor_get(v_toRing_3072_, 3);
v_semiringInst_3088_ = lean_ctor_get(v_toRing_3072_, 4);
v_charInst_x3f_3089_ = lean_ctor_get(v_toRing_3072_, 5);
v_symbolicChar_3090_ = lean_ctor_get_uint8(v_toRing_3072_, sizeof(void*)*16);
v_addFn_x3f_3091_ = lean_ctor_get(v_toRing_3072_, 6);
v_mulFn_x3f_3092_ = lean_ctor_get(v_toRing_3072_, 7);
v_subFn_x3f_3093_ = lean_ctor_get(v_toRing_3072_, 8);
v_negFn_x3f_3094_ = lean_ctor_get(v_toRing_3072_, 9);
v_powFn_x3f_3095_ = lean_ctor_get(v_toRing_3072_, 10);
v_intCastFn_x3f_3096_ = lean_ctor_get(v_toRing_3072_, 11);
v_natCastFn_x3f_3097_ = lean_ctor_get(v_toRing_3072_, 12);
v_natSMulFn_x3f_3098_ = lean_ctor_get(v_toRing_3072_, 13);
v_intSMulFn_x3f_3099_ = lean_ctor_get(v_toRing_3072_, 14);
v_isSharedCheck_3110_ = !lean_is_exclusive(v_toRing_3072_);
if (v_isSharedCheck_3110_ == 0)
{
lean_object* v_unused_3111_; 
v_unused_3111_ = lean_ctor_get(v_toRing_3072_, 15);
lean_dec(v_unused_3111_);
v___x_3101_ = v_toRing_3072_;
v_isShared_3102_ = v_isSharedCheck_3110_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_intSMulFn_x3f_3099_);
lean_inc(v_natSMulFn_x3f_3098_);
lean_inc(v_natCastFn_x3f_3097_);
lean_inc(v_intCastFn_x3f_3096_);
lean_inc(v_powFn_x3f_3095_);
lean_inc(v_negFn_x3f_3094_);
lean_inc(v_subFn_x3f_3093_);
lean_inc(v_mulFn_x3f_3092_);
lean_inc(v_addFn_x3f_3091_);
lean_inc(v_charInst_x3f_3089_);
lean_inc(v_semiringInst_3088_);
lean_inc(v_ringInst_3087_);
lean_inc(v_u_3086_);
lean_inc(v_type_3085_);
lean_inc(v_id_3084_);
lean_dec(v_toRing_3072_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3110_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3103_; lean_object* v___x_3105_; 
v___x_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3103_, 0, v_a_3070_);
if (v_isShared_3102_ == 0)
{
lean_ctor_set(v___x_3101_, 15, v___x_3103_);
v___x_3105_ = v___x_3101_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_id_3084_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v_type_3085_);
lean_ctor_set(v_reuseFailAlloc_3109_, 2, v_u_3086_);
lean_ctor_set(v_reuseFailAlloc_3109_, 3, v_ringInst_3087_);
lean_ctor_set(v_reuseFailAlloc_3109_, 4, v_semiringInst_3088_);
lean_ctor_set(v_reuseFailAlloc_3109_, 5, v_charInst_x3f_3089_);
lean_ctor_set(v_reuseFailAlloc_3109_, 6, v_addFn_x3f_3091_);
lean_ctor_set(v_reuseFailAlloc_3109_, 7, v_mulFn_x3f_3092_);
lean_ctor_set(v_reuseFailAlloc_3109_, 8, v_subFn_x3f_3093_);
lean_ctor_set(v_reuseFailAlloc_3109_, 9, v_negFn_x3f_3094_);
lean_ctor_set(v_reuseFailAlloc_3109_, 10, v_powFn_x3f_3095_);
lean_ctor_set(v_reuseFailAlloc_3109_, 11, v_intCastFn_x3f_3096_);
lean_ctor_set(v_reuseFailAlloc_3109_, 12, v_natCastFn_x3f_3097_);
lean_ctor_set(v_reuseFailAlloc_3109_, 13, v_natSMulFn_x3f_3098_);
lean_ctor_set(v_reuseFailAlloc_3109_, 14, v_intSMulFn_x3f_3099_);
lean_ctor_set(v_reuseFailAlloc_3109_, 15, v___x_3103_);
lean_ctor_set_uint8(v_reuseFailAlloc_3109_, sizeof(void*)*16, v_symbolicChar_3090_);
v___x_3105_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
lean_object* v___x_3107_; 
if (v_isShared_3083_ == 0)
{
lean_ctor_set(v___x_3082_, 0, v___x_3105_);
v___x_3107_ = v___x_3082_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v___x_3105_);
lean_ctor_set(v_reuseFailAlloc_3108_, 1, v_invFn_x3f_3073_);
lean_ctor_set(v_reuseFailAlloc_3108_, 2, v_divFn_x3f_3074_);
lean_ctor_set(v_reuseFailAlloc_3108_, 3, v_semiringId_x3f_3075_);
lean_ctor_set(v_reuseFailAlloc_3108_, 4, v_commSemiringInst_3076_);
lean_ctor_set(v_reuseFailAlloc_3108_, 5, v_commRingInst_3077_);
lean_ctor_set(v_reuseFailAlloc_3108_, 6, v_noZeroDivInst_x3f_3078_);
lean_ctor_set(v_reuseFailAlloc_3108_, 7, v_fieldInst_x3f_3079_);
lean_ctor_set(v_reuseFailAlloc_3108_, 8, v_powIdentityInst_x3f_3080_);
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
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3113_, lean_object* v_i_3114_, lean_object* v_k_3115_){
_start:
{
lean_object* v___x_3116_; uint8_t v___x_3117_; 
v___x_3116_ = lean_array_get_size(v_keys_3113_);
v___x_3117_ = lean_nat_dec_lt(v_i_3114_, v___x_3116_);
if (v___x_3117_ == 0)
{
lean_dec(v_i_3114_);
return v___x_3117_;
}
else
{
lean_object* v_k_x27_3118_; size_t v___x_3119_; size_t v___x_3120_; uint8_t v___x_3121_; 
v_k_x27_3118_ = lean_array_fget_borrowed(v_keys_3113_, v_i_3114_);
v___x_3119_ = lean_ptr_addr(v_k_3115_);
v___x_3120_ = lean_ptr_addr(v_k_x27_3118_);
v___x_3121_ = lean_usize_dec_eq(v___x_3119_, v___x_3120_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3122_ = lean_unsigned_to_nat(1u);
v___x_3123_ = lean_nat_add(v_i_3114_, v___x_3122_);
lean_dec(v_i_3114_);
v_i_3114_ = v___x_3123_;
goto _start;
}
else
{
lean_dec(v_i_3114_);
return v___x_3117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3125_, lean_object* v_i_3126_, lean_object* v_k_3127_){
_start:
{
uint8_t v_res_3128_; lean_object* v_r_3129_; 
v_res_3128_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg(v_keys_3125_, v_i_3126_, v_k_3127_);
lean_dec_ref(v_k_3127_);
lean_dec_ref(v_keys_3125_);
v_r_3129_ = lean_box(v_res_3128_);
return v_r_3129_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg(lean_object* v_x_3130_, size_t v_x_3131_, lean_object* v_x_3132_){
_start:
{
if (lean_obj_tag(v_x_3130_) == 0)
{
lean_object* v_es_3133_; lean_object* v___x_3134_; size_t v___x_3135_; size_t v___x_3136_; lean_object* v_j_3137_; lean_object* v___x_3138_; 
v_es_3133_ = lean_ctor_get(v_x_3130_, 0);
v___x_3134_ = lean_box(2);
v___x_3135_ = ((size_t)31ULL);
v___x_3136_ = lean_usize_land(v_x_3131_, v___x_3135_);
v_j_3137_ = lean_usize_to_nat(v___x_3136_);
v___x_3138_ = lean_array_get_borrowed(v___x_3134_, v_es_3133_, v_j_3137_);
lean_dec(v_j_3137_);
switch(lean_obj_tag(v___x_3138_))
{
case 0:
{
lean_object* v_key_3139_; size_t v___x_3140_; size_t v___x_3141_; uint8_t v___x_3142_; 
v_key_3139_ = lean_ctor_get(v___x_3138_, 0);
v___x_3140_ = lean_ptr_addr(v_x_3132_);
v___x_3141_ = lean_ptr_addr(v_key_3139_);
v___x_3142_ = lean_usize_dec_eq(v___x_3140_, v___x_3141_);
return v___x_3142_;
}
case 1:
{
lean_object* v_node_3143_; size_t v___x_3144_; size_t v___x_3145_; 
v_node_3143_ = lean_ctor_get(v___x_3138_, 0);
v___x_3144_ = ((size_t)5ULL);
v___x_3145_ = lean_usize_shift_right(v_x_3131_, v___x_3144_);
v_x_3130_ = v_node_3143_;
v_x_3131_ = v___x_3145_;
goto _start;
}
default: 
{
uint8_t v___x_3147_; 
v___x_3147_ = 0;
return v___x_3147_;
}
}
}
else
{
lean_object* v_ks_3148_; lean_object* v___x_3149_; uint8_t v___x_3150_; 
v_ks_3148_ = lean_ctor_get(v_x_3130_, 0);
v___x_3149_ = lean_unsigned_to_nat(0u);
v___x_3150_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg(v_ks_3148_, v___x_3149_, v_x_3132_);
return v___x_3150_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg___boxed(lean_object* v_x_3151_, lean_object* v_x_3152_, lean_object* v_x_3153_){
_start:
{
size_t v_x_9714__boxed_3154_; uint8_t v_res_3155_; lean_object* v_r_3156_; 
v_x_9714__boxed_3154_ = lean_unbox_usize(v_x_3152_);
lean_dec(v_x_3152_);
v_res_3155_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg(v_x_3151_, v_x_9714__boxed_3154_, v_x_3153_);
lean_dec_ref(v_x_3153_);
lean_dec_ref(v_x_3151_);
v_r_3156_ = lean_box(v_res_3155_);
return v_r_3156_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg(lean_object* v_x_3157_, lean_object* v_x_3158_){
_start:
{
size_t v___x_3159_; size_t v___x_3160_; size_t v___x_3161_; uint64_t v___x_3162_; size_t v___x_3163_; uint8_t v___x_3164_; 
v___x_3159_ = lean_ptr_addr(v_x_3158_);
v___x_3160_ = ((size_t)3ULL);
v___x_3161_ = lean_usize_shift_right(v___x_3159_, v___x_3160_);
v___x_3162_ = lean_usize_to_uint64(v___x_3161_);
v___x_3163_ = lean_uint64_to_usize(v___x_3162_);
v___x_3164_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg(v_x_3157_, v___x_3163_, v_x_3158_);
return v___x_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg___boxed(lean_object* v_x_3165_, lean_object* v_x_3166_){
_start:
{
uint8_t v_res_3167_; lean_object* v_r_3168_; 
v_res_3167_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg(v_x_3165_, v_x_3166_);
lean_dec_ref(v_x_3166_);
lean_dec_ref(v_x_3165_);
v_r_3168_ = lean_box(v_res_3167_);
return v_r_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne(lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_){
_start:
{
lean_object* v_one_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___x_3233_; 
v___x_3233_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_object* v_a_3234_; lean_object* v_toRing_3235_; lean_object* v_one_x3f_3236_; 
v_a_3234_ = lean_ctor_get(v___x_3233_, 0);
lean_inc(v_a_3234_);
lean_dec_ref_known(v___x_3233_, 1);
v_toRing_3235_ = lean_ctor_get(v_a_3234_, 0);
lean_inc_ref(v_toRing_3235_);
lean_dec(v_a_3234_);
v_one_x3f_3236_ = lean_ctor_get(v_toRing_3235_, 15);
if (lean_obj_tag(v_one_x3f_3236_) == 1)
{
lean_object* v_val_3237_; 
lean_inc_ref(v_one_x3f_3236_);
lean_dec_ref(v_toRing_3235_);
v_val_3237_ = lean_ctor_get(v_one_x3f_3236_, 0);
lean_inc(v_val_3237_);
lean_dec_ref_known(v_one_x3f_3236_, 1);
v_one_3182_ = v_val_3237_;
v___y_3183_ = v_a_3169_;
v___y_3184_ = v_a_3170_;
v___y_3185_ = v_a_3171_;
v___y_3186_ = v_a_3172_;
v___y_3187_ = v_a_3173_;
v___y_3188_ = v_a_3174_;
v___y_3189_ = v_a_3175_;
v___y_3190_ = v_a_3176_;
v___y_3191_ = v_a_3177_;
v___y_3192_ = v_a_3178_;
v___y_3193_ = v_a_3179_;
goto v___jp_3181_;
}
else
{
lean_object* v_type_3238_; lean_object* v_u_3239_; lean_object* v_semiringInst_3240_; lean_object* v___x_3241_; 
v_type_3238_ = lean_ctor_get(v_toRing_3235_, 1);
lean_inc_ref(v_type_3238_);
v_u_3239_ = lean_ctor_get(v_toRing_3235_, 2);
lean_inc(v_u_3239_);
v_semiringInst_3240_ = lean_ctor_get(v_toRing_3235_, 4);
lean_inc_ref(v_semiringInst_3240_);
lean_dec_ref(v_toRing_3235_);
v___x_3241_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(v_u_3239_, v_type_3238_, v_semiringInst_3240_, v_a_3174_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v_a_3242_; lean_object* v___f_3243_; lean_object* v___x_3244_; 
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
lean_inc_n(v_a_3242_, 2);
lean_dec_ref_known(v___x_3241_, 1);
v___f_3243_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getOne___lam__0), 2, 1);
lean_closure_set(v___f_3243_, 0, v_a_3242_);
v___x_3244_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_3243_, v_a_3169_, v_a_3175_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_dec_ref_known(v___x_3244_, 1);
v_one_3182_ = v_a_3242_;
v___y_3183_ = v_a_3169_;
v___y_3184_ = v_a_3170_;
v___y_3185_ = v_a_3171_;
v___y_3186_ = v_a_3172_;
v___y_3187_ = v_a_3173_;
v___y_3188_ = v_a_3174_;
v___y_3189_ = v_a_3175_;
v___y_3190_ = v_a_3176_;
v___y_3191_ = v_a_3177_;
v___y_3192_ = v_a_3178_;
v___y_3193_ = v_a_3179_;
goto v___jp_3181_;
}
else
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
lean_dec(v_a_3242_);
v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3247_ = v___x_3244_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3244_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3250_; 
if (v_isShared_3248_ == 0)
{
v___x_3250_ = v___x_3247_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3245_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
else
{
return v___x_3241_;
}
}
}
else
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
v_a_3253_ = lean_ctor_get(v___x_3233_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3255_ = v___x_3233_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3233_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
v___jp_3181_:
{
lean_object* v___x_3194_; 
v___x_3194_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v___y_3183_, v___y_3184_, v___y_3192_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3224_; 
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3197_ = v___x_3194_;
v_isShared_3198_ = v_isSharedCheck_3224_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3194_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3224_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v_toRingState_3199_; lean_object* v_denote_3200_; uint8_t v___x_3201_; 
v_toRingState_3199_ = lean_ctor_get(v_a_3195_, 0);
lean_inc_ref(v_toRingState_3199_);
lean_dec(v_a_3195_);
v_denote_3200_ = lean_ctor_get(v_toRingState_3199_, 2);
lean_inc_ref(v_denote_3200_);
lean_dec_ref(v_toRingState_3199_);
v___x_3201_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg(v_denote_3200_, v_one_3182_);
lean_dec_ref(v_denote_3200_);
if (v___x_3201_ == 0)
{
lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
lean_del_object(v___x_3197_);
v___x_3202_ = lean_unsigned_to_nat(0u);
v___x_3203_ = lean_box(0);
lean_inc(v___y_3193_);
lean_inc_ref(v___y_3192_);
lean_inc(v___y_3191_);
lean_inc_ref(v___y_3190_);
lean_inc(v___y_3189_);
lean_inc_ref(v___y_3188_);
lean_inc(v___y_3187_);
lean_inc_ref(v___y_3186_);
lean_inc(v___y_3185_);
lean_inc(v___y_3184_);
lean_inc_ref(v_one_3182_);
v___x_3204_ = lean_grind_internalize(v_one_3182_, v___x_3202_, v___x_3203_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3211_; 
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3211_ == 0)
{
lean_object* v_unused_3212_; 
v_unused_3212_ = lean_ctor_get(v___x_3204_, 0);
lean_dec(v_unused_3212_);
v___x_3206_ = v___x_3204_;
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
else
{
lean_dec(v___x_3204_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3209_; 
if (v_isShared_3207_ == 0)
{
lean_ctor_set(v___x_3206_, 0, v_one_3182_);
v___x_3209_ = v___x_3206_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_one_3182_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
else
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
lean_dec_ref(v_one_3182_);
v_a_3213_ = lean_ctor_get(v___x_3204_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3215_ = v___x_3204_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3204_);
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
lean_object* v___x_3222_; 
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 0, v_one_3182_);
v___x_3222_ = v___x_3197_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_one_3182_);
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
lean_dec_ref(v_one_3182_);
v_a_3225_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3232_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3227_ = v___x_3194_;
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___x_3194_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___boxed(lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_){
_start:
{
lean_object* v_res_3273_; 
v_res_3273_ = l_Lean_Meta_Grind_Arith_CommRing_getOne(v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_);
lean_dec(v_a_3271_);
lean_dec_ref(v_a_3270_);
lean_dec(v_a_3269_);
lean_dec_ref(v_a_3268_);
lean_dec(v_a_3267_);
lean_dec_ref(v_a_3266_);
lean_dec(v_a_3265_);
lean_dec_ref(v_a_3264_);
lean_dec(v_a_3263_);
lean_dec(v_a_3262_);
lean_dec_ref(v_a_3261_);
return v_res_3273_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0(lean_object* v_00_u03b2_3274_, lean_object* v_x_3275_, lean_object* v_x_3276_){
_start:
{
uint8_t v___x_3277_; 
v___x_3277_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg(v_x_3275_, v_x_3276_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___boxed(lean_object* v_00_u03b2_3278_, lean_object* v_x_3279_, lean_object* v_x_3280_){
_start:
{
uint8_t v_res_3281_; lean_object* v_r_3282_; 
v_res_3281_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0(v_00_u03b2_3278_, v_x_3279_, v_x_3280_);
lean_dec_ref(v_x_3280_);
lean_dec_ref(v_x_3279_);
v_r_3282_ = lean_box(v_res_3281_);
return v_r_3282_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0(lean_object* v_00_u03b2_3283_, lean_object* v_x_3284_, size_t v_x_3285_, lean_object* v_x_3286_){
_start:
{
uint8_t v___x_3287_; 
v___x_3287_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg(v_x_3284_, v_x_3285_, v_x_3286_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3288_, lean_object* v_x_3289_, lean_object* v_x_3290_, lean_object* v_x_3291_){
_start:
{
size_t v_x_9935__boxed_3292_; uint8_t v_res_3293_; lean_object* v_r_3294_; 
v_x_9935__boxed_3292_ = lean_unbox_usize(v_x_3290_);
lean_dec(v_x_3290_);
v_res_3293_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0(v_00_u03b2_3288_, v_x_3289_, v_x_9935__boxed_3292_, v_x_3291_);
lean_dec_ref(v_x_3291_);
lean_dec_ref(v_x_3289_);
v_r_3294_ = lean_box(v_res_3293_);
return v_r_3294_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3295_, lean_object* v_keys_3296_, lean_object* v_vals_3297_, lean_object* v_heq_3298_, lean_object* v_i_3299_, lean_object* v_k_3300_){
_start:
{
uint8_t v___x_3301_; 
v___x_3301_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg(v_keys_3296_, v_i_3299_, v_k_3300_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3302_, lean_object* v_keys_3303_, lean_object* v_vals_3304_, lean_object* v_heq_3305_, lean_object* v_i_3306_, lean_object* v_k_3307_){
_start:
{
uint8_t v_res_3308_; lean_object* v_r_3309_; 
v_res_3308_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1(v_00_u03b2_3302_, v_keys_3303_, v_vals_3304_, v_heq_3305_, v_i_3306_, v_k_3307_);
lean_dec_ref(v_k_3307_);
lean_dec_ref(v_vals_3304_);
lean_dec_ref(v_keys_3303_);
v_r_3309_ = lean_box(v_res_3308_);
return v_r_3309_;
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
