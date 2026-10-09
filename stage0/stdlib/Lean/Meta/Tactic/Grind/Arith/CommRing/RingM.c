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
v_ringMaxDegree_111_ = lean_ctor_get(v_a_107_, 7);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1192_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1186_ = v___x_1183_;
v_isShared_1187_ = v_isSharedCheck_1192_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1183_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1192_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v_noZeroDivInst_x3f_1188_; lean_object* v___x_1190_; 
v_noZeroDivInst_x3f_1188_ = lean_ctor_get(v_a_1184_, 6);
lean_inc(v_noZeroDivInst_x3f_1188_);
lean_dec(v_a_1184_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 0, v_noZeroDivInst_x3f_1188_);
v___x_1190_ = v___x_1186_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_noZeroDivInst_x3f_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
v_a_1193_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1183_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1183_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f___boxed(lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
lean_dec(v_a_1205_);
lean_dec_ref(v_a_1204_);
lean_dec(v_a_1203_);
lean_dec(v_a_1202_);
lean_dec_ref(v_a_1201_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1242_; 
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1229_ = v___x_1226_;
v_isShared_1230_ = v_isSharedCheck_1242_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1226_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1242_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v_noZeroDivInst_x3f_1231_; 
v_noZeroDivInst_x3f_1231_ = lean_ctor_get(v_a_1227_, 6);
lean_inc(v_noZeroDivInst_x3f_1231_);
lean_dec(v_a_1227_);
if (lean_obj_tag(v_noZeroDivInst_x3f_1231_) == 0)
{
uint8_t v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1232_ = 0;
v___x_1233_ = lean_box(v___x_1232_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v___x_1233_);
v___x_1235_ = v___x_1229_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1233_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
else
{
uint8_t v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1240_; 
lean_dec_ref_known(v_noZeroDivInst_x3f_1231_, 1);
v___x_1237_ = 1;
v___x_1238_ = lean_box(v___x_1237_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v___x_1238_);
v___x_1240_ = v___x_1229_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
v_a_1243_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1226_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1226_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors___boxed(lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
lean_dec(v_a_1261_);
lean_dec_ref(v_a_1260_);
lean_dec(v_a_1259_);
lean_dec_ref(v_a_1258_);
lean_dec(v_a_1257_);
lean_dec_ref(v_a_1256_);
lean_dec(v_a_1255_);
lean_dec_ref(v_a_1254_);
lean_dec(v_a_1253_);
lean_dec(v_a_1252_);
lean_dec_ref(v_a_1251_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar(lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1293_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1279_ = v___x_1276_;
v_isShared_1280_ = v_isSharedCheck_1293_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1276_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1293_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v_toRing_1281_; lean_object* v_charInst_x3f_1282_; 
v_toRing_1281_ = lean_ctor_get(v_a_1277_, 0);
lean_inc_ref(v_toRing_1281_);
lean_dec(v_a_1277_);
v_charInst_x3f_1282_ = lean_ctor_get(v_toRing_1281_, 5);
lean_inc(v_charInst_x3f_1282_);
lean_dec_ref(v_toRing_1281_);
if (lean_obj_tag(v_charInst_x3f_1282_) == 0)
{
uint8_t v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1286_; 
v___x_1283_ = 0;
v___x_1284_ = lean_box(v___x_1283_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v___x_1284_);
v___x_1286_ = v___x_1279_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
else
{
uint8_t v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1291_; 
lean_dec_ref_known(v_charInst_x3f_1282_, 1);
v___x_1288_ = 1;
v___x_1289_ = lean_box(v___x_1288_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v___x_1289_);
v___x_1291_ = v___x_1279_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
v_a_1294_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1276_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1276_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar___boxed(lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Lean_Meta_Grind_Arith_CommRing_hasChar(v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_);
lean_dec(v_a_1312_);
lean_dec_ref(v_a_1311_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
lean_dec(v_a_1304_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
return v_res_1314_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0));
v___x_1317_ = l_Lean_stringToMessageData(v___x_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst(lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1343_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1343_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1343_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v_toRing_1335_; lean_object* v_charInst_x3f_1336_; 
v_toRing_1335_ = lean_ctor_get(v_a_1331_, 0);
lean_inc_ref(v_toRing_1335_);
lean_dec(v_a_1331_);
v_charInst_x3f_1336_ = lean_ctor_get(v_toRing_1335_, 5);
lean_inc(v_charInst_x3f_1336_);
lean_dec_ref(v_toRing_1335_);
if (lean_obj_tag(v_charInst_x3f_1336_) == 1)
{
lean_object* v_val_1337_; lean_object* v___x_1339_; 
v_val_1337_ = lean_ctor_get(v_charInst_x3f_1336_, 0);
lean_inc(v_val_1337_);
lean_dec_ref_known(v_charInst_x3f_1336_, 1);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v_val_1337_);
v___x_1339_ = v___x_1333_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_val_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
else
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
lean_dec(v_charInst_x3f_1336_);
lean_del_object(v___x_1333_);
v___x_1341_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1);
v___x_1342_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v___x_1341_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
return v___x_1342_;
}
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
v_a_1344_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1330_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1330_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst___boxed(lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_Meta_Grind_Arith_CommRing_getCharInst(v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
lean_dec(v_a_1360_);
lean_dec_ref(v_a_1359_);
lean_dec(v_a_1358_);
lean_dec_ref(v_a_1357_);
lean_dec(v_a_1356_);
lean_dec_ref(v_a_1355_);
lean_dec(v_a_1354_);
lean_dec(v_a_1353_);
lean_dec_ref(v_a_1352_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField(lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_){
_start:
{
lean_object* v___x_1377_; 
v___x_1377_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1393_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1380_ = v___x_1377_;
v_isShared_1381_ = v_isSharedCheck_1393_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1377_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1393_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v_fieldInst_x3f_1382_; 
v_fieldInst_x3f_1382_ = lean_ctor_get(v_a_1378_, 7);
lean_inc(v_fieldInst_x3f_1382_);
lean_dec(v_a_1378_);
if (lean_obj_tag(v_fieldInst_x3f_1382_) == 0)
{
uint8_t v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1386_; 
v___x_1383_ = 0;
v___x_1384_ = lean_box(v___x_1383_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 0, v___x_1384_);
v___x_1386_ = v___x_1380_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1384_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
else
{
uint8_t v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
lean_dec_ref_known(v_fieldInst_x3f_1382_, 1);
v___x_1388_ = 1;
v___x_1389_ = lean_box(v___x_1388_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 0, v___x_1389_);
v___x_1391_ = v___x_1380_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
v_a_1394_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1377_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1377_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField___boxed(lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_Lean_Meta_Grind_Arith_CommRing_isField(v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_);
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
lean_dec_ref(v_a_1402_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___redArg(lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_1415_, v_a_1416_, v_a_1417_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1435_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1422_ = v___x_1419_;
v_isShared_1423_ = v_isSharedCheck_1435_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1419_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1435_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v_queue_1424_; 
v_queue_1424_ = lean_ctor_get(v_a_1420_, 4);
lean_inc(v_queue_1424_);
lean_dec(v_a_1420_);
if (lean_obj_tag(v_queue_1424_) == 0)
{
uint8_t v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1428_; 
lean_dec_ref_known(v_queue_1424_, 5);
v___x_1425_ = 0;
v___x_1426_ = lean_box(v___x_1425_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 0, v___x_1426_);
v___x_1428_ = v___x_1422_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1426_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
else
{
uint8_t v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1433_; 
v___x_1430_ = 1;
v___x_1431_ = lean_box(v___x_1430_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 0, v___x_1431_);
v___x_1433_ = v___x_1422_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
v_a_1436_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1419_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1419_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___redArg___boxed(lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___redArg(v_a_1444_, v_a_1445_, v_a_1446_);
lean_dec_ref(v_a_1446_);
lean_dec(v_a_1445_);
lean_dec_ref(v_a_1444_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___redArg(v_a_1449_, v_a_1450_, v_a_1458_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___boxed(lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
lean_dec(v_a_1464_);
lean_dec(v_a_1463_);
lean_dec_ref(v_a_1462_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(lean_object* v_k_1475_, lean_object* v_t_1476_){
_start:
{
if (lean_obj_tag(v_t_1476_) == 0)
{
lean_object* v_k_1477_; lean_object* v_v_1478_; lean_object* v_l_1479_; lean_object* v_r_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_2134_; 
v_k_1477_ = lean_ctor_get(v_t_1476_, 1);
v_v_1478_ = lean_ctor_get(v_t_1476_, 2);
v_l_1479_ = lean_ctor_get(v_t_1476_, 3);
v_r_1480_ = lean_ctor_get(v_t_1476_, 4);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_t_1476_);
if (v_isSharedCheck_2134_ == 0)
{
lean_object* v_unused_2135_; 
v_unused_2135_ = lean_ctor_get(v_t_1476_, 0);
lean_dec(v_unused_2135_);
v___x_1482_ = v_t_1476_;
v_isShared_1483_ = v_isSharedCheck_2134_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_r_1480_);
lean_inc(v_l_1479_);
lean_inc(v_v_1478_);
lean_inc(v_k_1477_);
lean_dec(v_t_1476_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_2134_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
uint8_t v___x_1484_; 
v___x_1484_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(v_k_1475_, v_k_1477_);
switch(v___x_1484_)
{
case 0:
{
lean_object* v_impl_1485_; lean_object* v___x_1486_; 
v_impl_1485_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1475_, v_l_1479_);
v___x_1486_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1485_) == 0)
{
if (lean_obj_tag(v_r_1480_) == 0)
{
lean_object* v_size_1487_; lean_object* v_size_1488_; lean_object* v_k_1489_; lean_object* v_v_1490_; lean_object* v_l_1491_; lean_object* v_r_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; uint8_t v___x_1495_; 
v_size_1487_ = lean_ctor_get(v_impl_1485_, 0);
v_size_1488_ = lean_ctor_get(v_r_1480_, 0);
v_k_1489_ = lean_ctor_get(v_r_1480_, 1);
v_v_1490_ = lean_ctor_get(v_r_1480_, 2);
v_l_1491_ = lean_ctor_get(v_r_1480_, 3);
lean_inc(v_l_1491_);
v_r_1492_ = lean_ctor_get(v_r_1480_, 4);
v___x_1493_ = lean_unsigned_to_nat(3u);
v___x_1494_ = lean_nat_mul(v___x_1493_, v_size_1487_);
v___x_1495_ = lean_nat_dec_lt(v___x_1494_, v_size_1488_);
lean_dec(v___x_1494_);
if (v___x_1495_ == 0)
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1499_; 
lean_dec(v_l_1491_);
v___x_1496_ = lean_nat_add(v___x_1486_, v_size_1487_);
v___x_1497_ = lean_nat_add(v___x_1496_, v_size_1488_);
lean_dec(v___x_1496_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 3, v_impl_1485_);
lean_ctor_set(v___x_1482_, 0, v___x_1497_);
v___x_1499_ = v___x_1482_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_k_1477_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_v_1478_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_impl_1485_);
lean_ctor_set(v_reuseFailAlloc_1500_, 4, v_r_1480_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
else
{
lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1564_; 
lean_inc(v_r_1492_);
lean_inc(v_v_1490_);
lean_inc(v_k_1489_);
lean_inc(v_size_1488_);
v_isSharedCheck_1564_ = !lean_is_exclusive(v_r_1480_);
if (v_isSharedCheck_1564_ == 0)
{
lean_object* v_unused_1565_; lean_object* v_unused_1566_; lean_object* v_unused_1567_; lean_object* v_unused_1568_; lean_object* v_unused_1569_; 
v_unused_1565_ = lean_ctor_get(v_r_1480_, 4);
lean_dec(v_unused_1565_);
v_unused_1566_ = lean_ctor_get(v_r_1480_, 3);
lean_dec(v_unused_1566_);
v_unused_1567_ = lean_ctor_get(v_r_1480_, 2);
lean_dec(v_unused_1567_);
v_unused_1568_ = lean_ctor_get(v_r_1480_, 1);
lean_dec(v_unused_1568_);
v_unused_1569_ = lean_ctor_get(v_r_1480_, 0);
lean_dec(v_unused_1569_);
v___x_1502_ = v_r_1480_;
v_isShared_1503_ = v_isSharedCheck_1564_;
goto v_resetjp_1501_;
}
else
{
lean_dec(v_r_1480_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1564_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v_size_1504_; lean_object* v_k_1505_; lean_object* v_v_1506_; lean_object* v_l_1507_; lean_object* v_r_1508_; lean_object* v_size_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; uint8_t v___x_1512_; 
v_size_1504_ = lean_ctor_get(v_l_1491_, 0);
v_k_1505_ = lean_ctor_get(v_l_1491_, 1);
v_v_1506_ = lean_ctor_get(v_l_1491_, 2);
v_l_1507_ = lean_ctor_get(v_l_1491_, 3);
v_r_1508_ = lean_ctor_get(v_l_1491_, 4);
v_size_1509_ = lean_ctor_get(v_r_1492_, 0);
v___x_1510_ = lean_unsigned_to_nat(2u);
v___x_1511_ = lean_nat_mul(v___x_1510_, v_size_1509_);
v___x_1512_ = lean_nat_dec_lt(v_size_1504_, v___x_1511_);
lean_dec(v___x_1511_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1540_; 
lean_inc(v_r_1508_);
lean_inc(v_l_1507_);
lean_inc(v_v_1506_);
lean_inc(v_k_1505_);
v_isSharedCheck_1540_ = !lean_is_exclusive(v_l_1491_);
if (v_isSharedCheck_1540_ == 0)
{
lean_object* v_unused_1541_; lean_object* v_unused_1542_; lean_object* v_unused_1543_; lean_object* v_unused_1544_; lean_object* v_unused_1545_; 
v_unused_1541_ = lean_ctor_get(v_l_1491_, 4);
lean_dec(v_unused_1541_);
v_unused_1542_ = lean_ctor_get(v_l_1491_, 3);
lean_dec(v_unused_1542_);
v_unused_1543_ = lean_ctor_get(v_l_1491_, 2);
lean_dec(v_unused_1543_);
v_unused_1544_ = lean_ctor_get(v_l_1491_, 1);
lean_dec(v_unused_1544_);
v_unused_1545_ = lean_ctor_get(v_l_1491_, 0);
lean_dec(v_unused_1545_);
v___x_1514_ = v_l_1491_;
v_isShared_1515_ = v_isSharedCheck_1540_;
goto v_resetjp_1513_;
}
else
{
lean_dec(v_l_1491_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1540_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1530_; 
v___x_1516_ = lean_nat_add(v___x_1486_, v_size_1487_);
v___x_1517_ = lean_nat_add(v___x_1516_, v_size_1488_);
lean_dec(v_size_1488_);
if (lean_obj_tag(v_l_1507_) == 0)
{
lean_object* v_size_1538_; 
v_size_1538_ = lean_ctor_get(v_l_1507_, 0);
lean_inc(v_size_1538_);
v___y_1530_ = v_size_1538_;
goto v___jp_1529_;
}
else
{
lean_object* v___x_1539_; 
v___x_1539_ = lean_unsigned_to_nat(0u);
v___y_1530_ = v___x_1539_;
goto v___jp_1529_;
}
v___jp_1518_:
{
lean_object* v___x_1522_; lean_object* v___x_1524_; 
v___x_1522_ = lean_nat_add(v___y_1520_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec(v___y_1520_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 4, v_r_1492_);
lean_ctor_set(v___x_1514_, 3, v_r_1508_);
lean_ctor_set(v___x_1514_, 2, v_v_1490_);
lean_ctor_set(v___x_1514_, 1, v_k_1489_);
lean_ctor_set(v___x_1514_, 0, v___x_1522_);
v___x_1524_ = v___x_1514_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_k_1489_);
lean_ctor_set(v_reuseFailAlloc_1528_, 2, v_v_1490_);
lean_ctor_set(v_reuseFailAlloc_1528_, 3, v_r_1508_);
lean_ctor_set(v_reuseFailAlloc_1528_, 4, v_r_1492_);
v___x_1524_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
lean_object* v___x_1526_; 
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 4, v___x_1524_);
lean_ctor_set(v___x_1502_, 3, v___y_1519_);
lean_ctor_set(v___x_1502_, 2, v_v_1506_);
lean_ctor_set(v___x_1502_, 1, v_k_1505_);
lean_ctor_set(v___x_1502_, 0, v___x_1517_);
v___x_1526_ = v___x_1502_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_k_1505_);
lean_ctor_set(v_reuseFailAlloc_1527_, 2, v_v_1506_);
lean_ctor_set(v_reuseFailAlloc_1527_, 3, v___y_1519_);
lean_ctor_set(v_reuseFailAlloc_1527_, 4, v___x_1524_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
v___jp_1529_:
{
lean_object* v___x_1531_; lean_object* v___x_1533_; 
v___x_1531_ = lean_nat_add(v___x_1516_, v___y_1530_);
lean_dec(v___y_1530_);
lean_dec(v___x_1516_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 4, v_l_1507_);
lean_ctor_set(v___x_1482_, 3, v_impl_1485_);
lean_ctor_set(v___x_1482_, 0, v___x_1531_);
v___x_1533_ = v___x_1482_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1531_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_k_1477_);
lean_ctor_set(v_reuseFailAlloc_1537_, 2, v_v_1478_);
lean_ctor_set(v_reuseFailAlloc_1537_, 3, v_impl_1485_);
lean_ctor_set(v_reuseFailAlloc_1537_, 4, v_l_1507_);
v___x_1533_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_nat_add(v___x_1486_, v_size_1509_);
if (lean_obj_tag(v_r_1508_) == 0)
{
lean_object* v_size_1535_; 
v_size_1535_ = lean_ctor_get(v_r_1508_, 0);
lean_inc(v_size_1535_);
v___y_1519_ = v___x_1533_;
v___y_1520_ = v___x_1534_;
v___y_1521_ = v_size_1535_;
goto v___jp_1518_;
}
else
{
lean_object* v___x_1536_; 
v___x_1536_ = lean_unsigned_to_nat(0u);
v___y_1519_ = v___x_1533_;
v___y_1520_ = v___x_1534_;
v___y_1521_ = v___x_1536_;
goto v___jp_1518_;
}
}
}
}
}
else
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1550_; 
lean_del_object(v___x_1482_);
v___x_1546_ = lean_nat_add(v___x_1486_, v_size_1487_);
v___x_1547_ = lean_nat_add(v___x_1546_, v_size_1488_);
lean_dec(v_size_1488_);
v___x_1548_ = lean_nat_add(v___x_1546_, v_size_1504_);
lean_dec(v___x_1546_);
lean_inc_ref(v_impl_1485_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 4, v_l_1491_);
lean_ctor_set(v___x_1502_, 3, v_impl_1485_);
lean_ctor_set(v___x_1502_, 2, v_v_1478_);
lean_ctor_set(v___x_1502_, 1, v_k_1477_);
lean_ctor_set(v___x_1502_, 0, v___x_1548_);
v___x_1550_ = v___x_1502_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1548_);
lean_ctor_set(v_reuseFailAlloc_1563_, 1, v_k_1477_);
lean_ctor_set(v_reuseFailAlloc_1563_, 2, v_v_1478_);
lean_ctor_set(v_reuseFailAlloc_1563_, 3, v_impl_1485_);
lean_ctor_set(v_reuseFailAlloc_1563_, 4, v_l_1491_);
v___x_1550_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
v_isSharedCheck_1557_ = !lean_is_exclusive(v_impl_1485_);
if (v_isSharedCheck_1557_ == 0)
{
lean_object* v_unused_1558_; lean_object* v_unused_1559_; lean_object* v_unused_1560_; lean_object* v_unused_1561_; lean_object* v_unused_1562_; 
v_unused_1558_ = lean_ctor_get(v_impl_1485_, 4);
lean_dec(v_unused_1558_);
v_unused_1559_ = lean_ctor_get(v_impl_1485_, 3);
lean_dec(v_unused_1559_);
v_unused_1560_ = lean_ctor_get(v_impl_1485_, 2);
lean_dec(v_unused_1560_);
v_unused_1561_ = lean_ctor_get(v_impl_1485_, 1);
lean_dec(v_unused_1561_);
v_unused_1562_ = lean_ctor_get(v_impl_1485_, 0);
lean_dec(v_unused_1562_);
v___x_1552_ = v_impl_1485_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_dec(v_impl_1485_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 4, v_r_1492_);
lean_ctor_set(v___x_1552_, 3, v___x_1550_);
lean_ctor_set(v___x_1552_, 2, v_v_1490_);
lean_ctor_set(v___x_1552_, 1, v_k_1489_);
lean_ctor_set(v___x_1552_, 0, v___x_1547_);
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v_k_1489_);
lean_ctor_set(v_reuseFailAlloc_1556_, 2, v_v_1490_);
lean_ctor_set(v_reuseFailAlloc_1556_, 3, v___x_1550_);
lean_ctor_set(v_reuseFailAlloc_1556_, 4, v_r_1492_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
v_size_1570_ = lean_ctor_get(v_impl_1485_, 0);
v___x_1571_ = lean_nat_add(v___x_1486_, v_size_1570_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 3, v_impl_1485_);
lean_ctor_set(v___x_1482_, 0, v___x_1571_);
v___x_1573_ = v___x_1482_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v_k_1477_);
lean_ctor_set(v_reuseFailAlloc_1574_, 2, v_v_1478_);
lean_ctor_set(v_reuseFailAlloc_1574_, 3, v_impl_1485_);
lean_ctor_set(v_reuseFailAlloc_1574_, 4, v_r_1480_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
else
{
if (lean_obj_tag(v_r_1480_) == 0)
{
lean_object* v_l_1575_; 
v_l_1575_ = lean_ctor_get(v_r_1480_, 3);
lean_inc(v_l_1575_);
if (lean_obj_tag(v_l_1575_) == 0)
{
lean_object* v_r_1576_; 
v_r_1576_ = lean_ctor_get(v_r_1480_, 4);
lean_inc(v_r_1576_);
if (lean_obj_tag(v_r_1576_) == 0)
{
lean_object* v_size_1577_; lean_object* v_k_1578_; lean_object* v_v_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1592_; 
v_size_1577_ = lean_ctor_get(v_r_1480_, 0);
v_k_1578_ = lean_ctor_get(v_r_1480_, 1);
v_v_1579_ = lean_ctor_get(v_r_1480_, 2);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_r_1480_);
if (v_isSharedCheck_1592_ == 0)
{
lean_object* v_unused_1593_; lean_object* v_unused_1594_; 
v_unused_1593_ = lean_ctor_get(v_r_1480_, 4);
lean_dec(v_unused_1593_);
v_unused_1594_ = lean_ctor_get(v_r_1480_, 3);
lean_dec(v_unused_1594_);
v___x_1581_ = v_r_1480_;
v_isShared_1582_ = v_isSharedCheck_1592_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_v_1579_);
lean_inc(v_k_1578_);
lean_inc(v_size_1577_);
lean_dec(v_r_1480_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1592_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v_size_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1587_; 
v_size_1583_ = lean_ctor_get(v_l_1575_, 0);
v___x_1584_ = lean_nat_add(v___x_1486_, v_size_1577_);
lean_dec(v_size_1577_);
v___x_1585_ = lean_nat_add(v___x_1486_, v_size_1583_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 4, v_l_1575_);
lean_ctor_set(v___x_1581_, 3, v_impl_1485_);
lean_ctor_set(v___x_1581_, 2, v_v_1478_);
lean_ctor_set(v___x_1581_, 1, v_k_1477_);
lean_ctor_set(v___x_1581_, 0, v___x_1585_);
v___x_1587_ = v___x_1581_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1585_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v_k_1477_);
lean_ctor_set(v_reuseFailAlloc_1591_, 2, v_v_1478_);
lean_ctor_set(v_reuseFailAlloc_1591_, 3, v_impl_1485_);
lean_ctor_set(v_reuseFailAlloc_1591_, 4, v_l_1575_);
v___x_1587_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
lean_object* v___x_1589_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 4, v_r_1576_);
lean_ctor_set(v___x_1482_, 3, v___x_1587_);
lean_ctor_set(v___x_1482_, 2, v_v_1579_);
lean_ctor_set(v___x_1482_, 1, v_k_1578_);
lean_ctor_set(v___x_1482_, 0, v___x_1584_);
v___x_1589_ = v___x_1482_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1584_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_k_1578_);
lean_ctor_set(v_reuseFailAlloc_1590_, 2, v_v_1579_);
lean_ctor_set(v_reuseFailAlloc_1590_, 3, v___x_1587_);
lean_ctor_set(v_reuseFailAlloc_1590_, 4, v_r_1576_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
else
{
lean_object* v_k_1595_; lean_object* v_v_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1619_; 
v_k_1595_ = lean_ctor_get(v_r_1480_, 1);
v_v_1596_ = lean_ctor_get(v_r_1480_, 2);
v_isSharedCheck_1619_ = !lean_is_exclusive(v_r_1480_);
if (v_isSharedCheck_1619_ == 0)
{
lean_object* v_unused_1620_; lean_object* v_unused_1621_; lean_object* v_unused_1622_; 
v_unused_1620_ = lean_ctor_get(v_r_1480_, 4);
lean_dec(v_unused_1620_);
v_unused_1621_ = lean_ctor_get(v_r_1480_, 3);
lean_dec(v_unused_1621_);
v_unused_1622_ = lean_ctor_get(v_r_1480_, 0);
lean_dec(v_unused_1622_);
v___x_1598_ = v_r_1480_;
v_isShared_1599_ = v_isSharedCheck_1619_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_v_1596_);
lean_inc(v_k_1595_);
lean_dec(v_r_1480_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1619_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v_k_1600_; lean_object* v_v_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1615_; 
v_k_1600_ = lean_ctor_get(v_l_1575_, 1);
v_v_1601_ = lean_ctor_get(v_l_1575_, 2);
v_isSharedCheck_1615_ = !lean_is_exclusive(v_l_1575_);
if (v_isSharedCheck_1615_ == 0)
{
lean_object* v_unused_1616_; lean_object* v_unused_1617_; lean_object* v_unused_1618_; 
v_unused_1616_ = lean_ctor_get(v_l_1575_, 4);
lean_dec(v_unused_1616_);
v_unused_1617_ = lean_ctor_get(v_l_1575_, 3);
lean_dec(v_unused_1617_);
v_unused_1618_ = lean_ctor_get(v_l_1575_, 0);
lean_dec(v_unused_1618_);
v___x_1603_ = v_l_1575_;
v_isShared_1604_ = v_isSharedCheck_1615_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_v_1601_);
lean_inc(v_k_1600_);
lean_dec(v_l_1575_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1615_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1605_; lean_object* v___x_1607_; 
v___x_1605_ = lean_unsigned_to_nat(3u);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 4, v_r_1576_);
lean_ctor_set(v___x_1603_, 3, v_r_1576_);
lean_ctor_set(v___x_1603_, 2, v_v_1478_);
lean_ctor_set(v___x_1603_, 1, v_k_1477_);
lean_ctor_set(v___x_1603_, 0, v___x_1486_);
v___x_1607_ = v___x_1603_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_k_1477_);
lean_ctor_set(v_reuseFailAlloc_1614_, 2, v_v_1478_);
lean_ctor_set(v_reuseFailAlloc_1614_, 3, v_r_1576_);
lean_ctor_set(v_reuseFailAlloc_1614_, 4, v_r_1576_);
v___x_1607_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
lean_object* v___x_1609_; 
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 3, v_r_1576_);
lean_ctor_set(v___x_1598_, 0, v___x_1486_);
v___x_1609_ = v___x_1598_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_k_1595_);
lean_ctor_set(v_reuseFailAlloc_1613_, 2, v_v_1596_);
lean_ctor_set(v_reuseFailAlloc_1613_, 3, v_r_1576_);
lean_ctor_set(v_reuseFailAlloc_1613_, 4, v_r_1576_);
v___x_1609_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1611_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 4, v___x_1609_);
lean_ctor_set(v___x_1482_, 3, v___x_1607_);
lean_ctor_set(v___x_1482_, 2, v_v_1601_);
lean_ctor_set(v___x_1482_, 1, v_k_1600_);
lean_ctor_set(v___x_1482_, 0, v___x_1605_);
v___x_1611_ = v___x_1482_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1605_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v_k_1600_);
lean_ctor_set(v_reuseFailAlloc_1612_, 2, v_v_1601_);
lean_ctor_set(v_reuseFailAlloc_1612_, 3, v___x_1607_);
lean_ctor_set(v_reuseFailAlloc_1612_, 4, v___x_1609_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1623_; 
v_r_1623_ = lean_ctor_get(v_r_1480_, 4);
lean_inc(v_r_1623_);
if (lean_obj_tag(v_r_1623_) == 0)
{
lean_object* v_k_1624_; lean_object* v_v_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1636_; 
v_k_1624_ = lean_ctor_get(v_r_1480_, 1);
v_v_1625_ = lean_ctor_get(v_r_1480_, 2);
v_isSharedCheck_1636_ = !lean_is_exclusive(v_r_1480_);
if (v_isSharedCheck_1636_ == 0)
{
lean_object* v_unused_1637_; lean_object* v_unused_1638_; lean_object* v_unused_1639_; 
v_unused_1637_ = lean_ctor_get(v_r_1480_, 4);
lean_dec(v_unused_1637_);
v_unused_1638_ = lean_ctor_get(v_r_1480_, 3);
lean_dec(v_unused_1638_);
v_unused_1639_ = lean_ctor_get(v_r_1480_, 0);
lean_dec(v_unused_1639_);
v___x_1627_ = v_r_1480_;
v_isShared_1628_ = v_isSharedCheck_1636_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_v_1625_);
lean_inc(v_k_1624_);
lean_dec(v_r_1480_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1636_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; lean_object* v___x_1631_; 
v___x_1629_ = lean_unsigned_to_nat(3u);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 4, v_l_1575_);
lean_ctor_set(v___x_1627_, 2, v_v_1478_);
lean_ctor_set(v___x_1627_, 1, v_k_1477_);
lean_ctor_set(v___x_1627_, 0, v___x_1486_);
v___x_1631_ = v___x_1627_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v_k_1477_);
lean_ctor_set(v_reuseFailAlloc_1635_, 2, v_v_1478_);
lean_ctor_set(v_reuseFailAlloc_1635_, 3, v_l_1575_);
lean_ctor_set(v_reuseFailAlloc_1635_, 4, v_l_1575_);
v___x_1631_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
lean_object* v___x_1633_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 4, v_r_1623_);
lean_ctor_set(v___x_1482_, 3, v___x_1631_);
lean_ctor_set(v___x_1482_, 2, v_v_1625_);
lean_ctor_set(v___x_1482_, 1, v_k_1624_);
lean_ctor_set(v___x_1482_, 0, v___x_1629_);
v___x_1633_ = v___x_1482_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1629_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v_k_1624_);
lean_ctor_set(v_reuseFailAlloc_1634_, 2, v_v_1625_);
lean_ctor_set(v_reuseFailAlloc_1634_, 3, v___x_1631_);
lean_ctor_set(v_reuseFailAlloc_1634_, 4, v_r_1623_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
else
{
lean_object* v_size_1640_; lean_object* v_k_1641_; lean_object* v_v_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1653_; 
v_size_1640_ = lean_ctor_get(v_r_1480_, 0);
v_k_1641_ = lean_ctor_get(v_r_1480_, 1);
v_v_1642_ = lean_ctor_get(v_r_1480_, 2);
v_isSharedCheck_1653_ = !lean_is_exclusive(v_r_1480_);
if (v_isSharedCheck_1653_ == 0)
{
lean_object* v_unused_1654_; lean_object* v_unused_1655_; 
v_unused_1654_ = lean_ctor_get(v_r_1480_, 4);
lean_dec(v_unused_1654_);
v_unused_1655_ = lean_ctor_get(v_r_1480_, 3);
lean_dec(v_unused_1655_);
v___x_1644_ = v_r_1480_;
v_isShared_1645_ = v_isSharedCheck_1653_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_v_1642_);
lean_inc(v_k_1641_);
lean_inc(v_size_1640_);
lean_dec(v_r_1480_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1653_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 3, v_r_1623_);
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_size_1640_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v_k_1641_);
lean_ctor_set(v_reuseFailAlloc_1652_, 2, v_v_1642_);
lean_ctor_set(v_reuseFailAlloc_1652_, 3, v_r_1623_);
lean_ctor_set(v_reuseFailAlloc_1652_, 4, v_r_1623_);
v___x_1647_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
lean_object* v___x_1648_; lean_object* v___x_1650_; 
v___x_1648_ = lean_unsigned_to_nat(2u);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 4, v___x_1647_);
lean_ctor_set(v___x_1482_, 3, v_r_1623_);
lean_ctor_set(v___x_1482_, 0, v___x_1648_);
v___x_1650_ = v___x_1482_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1648_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v_k_1477_);
lean_ctor_set(v_reuseFailAlloc_1651_, 2, v_v_1478_);
lean_ctor_set(v_reuseFailAlloc_1651_, 3, v_r_1623_);
lean_ctor_set(v_reuseFailAlloc_1651_, 4, v___x_1647_);
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
else
{
lean_object* v___x_1657_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 3, v_r_1480_);
lean_ctor_set(v___x_1482_, 0, v___x_1486_);
v___x_1657_ = v___x_1482_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v_k_1477_);
lean_ctor_set(v_reuseFailAlloc_1658_, 2, v_v_1478_);
lean_ctor_set(v_reuseFailAlloc_1658_, 3, v_r_1480_);
lean_ctor_set(v_reuseFailAlloc_1658_, 4, v_r_1480_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1482_);
lean_dec(v_v_1478_);
lean_dec(v_k_1477_);
if (lean_obj_tag(v_l_1479_) == 0)
{
if (lean_obj_tag(v_r_1480_) == 0)
{
lean_object* v_size_1659_; lean_object* v_k_1660_; lean_object* v_v_1661_; lean_object* v_l_1662_; lean_object* v_r_1663_; lean_object* v_size_1664_; lean_object* v_k_1665_; lean_object* v_v_1666_; lean_object* v_l_1667_; lean_object* v_r_1668_; lean_object* v___x_1669_; uint8_t v___x_1670_; 
v_size_1659_ = lean_ctor_get(v_l_1479_, 0);
v_k_1660_ = lean_ctor_get(v_l_1479_, 1);
v_v_1661_ = lean_ctor_get(v_l_1479_, 2);
v_l_1662_ = lean_ctor_get(v_l_1479_, 3);
v_r_1663_ = lean_ctor_get(v_l_1479_, 4);
lean_inc(v_r_1663_);
v_size_1664_ = lean_ctor_get(v_r_1480_, 0);
v_k_1665_ = lean_ctor_get(v_r_1480_, 1);
v_v_1666_ = lean_ctor_get(v_r_1480_, 2);
v_l_1667_ = lean_ctor_get(v_r_1480_, 3);
lean_inc(v_l_1667_);
v_r_1668_ = lean_ctor_get(v_r_1480_, 4);
v___x_1669_ = lean_unsigned_to_nat(1u);
v___x_1670_ = lean_nat_dec_lt(v_size_1659_, v_size_1664_);
if (v___x_1670_ == 0)
{
lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1806_; 
lean_inc(v_l_1662_);
lean_inc(v_v_1661_);
lean_inc(v_k_1660_);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_l_1479_);
if (v_isSharedCheck_1806_ == 0)
{
lean_object* v_unused_1807_; lean_object* v_unused_1808_; lean_object* v_unused_1809_; lean_object* v_unused_1810_; lean_object* v_unused_1811_; 
v_unused_1807_ = lean_ctor_get(v_l_1479_, 4);
lean_dec(v_unused_1807_);
v_unused_1808_ = lean_ctor_get(v_l_1479_, 3);
lean_dec(v_unused_1808_);
v_unused_1809_ = lean_ctor_get(v_l_1479_, 2);
lean_dec(v_unused_1809_);
v_unused_1810_ = lean_ctor_get(v_l_1479_, 1);
lean_dec(v_unused_1810_);
v_unused_1811_ = lean_ctor_get(v_l_1479_, 0);
lean_dec(v_unused_1811_);
v___x_1672_ = v_l_1479_;
v_isShared_1673_ = v_isSharedCheck_1806_;
goto v_resetjp_1671_;
}
else
{
lean_dec(v_l_1479_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1806_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1674_; lean_object* v_tree_1675_; 
v___x_1674_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1660_, v_v_1661_, v_l_1662_, v_r_1663_);
v_tree_1675_ = lean_ctor_get(v___x_1674_, 2);
if (lean_obj_tag(v_tree_1675_) == 0)
{
lean_object* v_k_1676_; lean_object* v_v_1677_; lean_object* v_size_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; uint8_t v___x_1681_; 
lean_inc_ref(v_tree_1675_);
v_k_1676_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_k_1676_);
v_v_1677_ = lean_ctor_get(v___x_1674_, 1);
lean_inc(v_v_1677_);
lean_dec_ref(v___x_1674_);
v_size_1678_ = lean_ctor_get(v_tree_1675_, 0);
v___x_1679_ = lean_unsigned_to_nat(3u);
v___x_1680_ = lean_nat_mul(v___x_1679_, v_size_1678_);
v___x_1681_ = lean_nat_dec_lt(v___x_1680_, v_size_1664_);
lean_dec(v___x_1680_);
if (v___x_1681_ == 0)
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1685_; 
lean_dec(v_l_1667_);
v___x_1682_ = lean_nat_add(v___x_1669_, v_size_1678_);
v___x_1683_ = lean_nat_add(v___x_1682_, v_size_1664_);
lean_dec(v___x_1682_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 4, v_r_1480_);
lean_ctor_set(v___x_1672_, 3, v_tree_1675_);
lean_ctor_set(v___x_1672_, 2, v_v_1677_);
lean_ctor_set(v___x_1672_, 1, v_k_1676_);
lean_ctor_set(v___x_1672_, 0, v___x_1683_);
v___x_1685_ = v___x_1672_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1683_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_k_1676_);
lean_ctor_set(v_reuseFailAlloc_1686_, 2, v_v_1677_);
lean_ctor_set(v_reuseFailAlloc_1686_, 3, v_tree_1675_);
lean_ctor_set(v_reuseFailAlloc_1686_, 4, v_r_1480_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
else
{
lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1741_; 
lean_inc(v_r_1668_);
lean_inc(v_v_1666_);
lean_inc(v_k_1665_);
lean_inc(v_size_1664_);
v_isSharedCheck_1741_ = !lean_is_exclusive(v_r_1480_);
if (v_isSharedCheck_1741_ == 0)
{
lean_object* v_unused_1742_; lean_object* v_unused_1743_; lean_object* v_unused_1744_; lean_object* v_unused_1745_; lean_object* v_unused_1746_; 
v_unused_1742_ = lean_ctor_get(v_r_1480_, 4);
lean_dec(v_unused_1742_);
v_unused_1743_ = lean_ctor_get(v_r_1480_, 3);
lean_dec(v_unused_1743_);
v_unused_1744_ = lean_ctor_get(v_r_1480_, 2);
lean_dec(v_unused_1744_);
v_unused_1745_ = lean_ctor_get(v_r_1480_, 1);
lean_dec(v_unused_1745_);
v_unused_1746_ = lean_ctor_get(v_r_1480_, 0);
lean_dec(v_unused_1746_);
v___x_1688_ = v_r_1480_;
v_isShared_1689_ = v_isSharedCheck_1741_;
goto v_resetjp_1687_;
}
else
{
lean_dec(v_r_1480_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1741_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v_size_1690_; lean_object* v_k_1691_; lean_object* v_v_1692_; lean_object* v_l_1693_; lean_object* v_r_1694_; lean_object* v_size_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; uint8_t v___x_1698_; 
v_size_1690_ = lean_ctor_get(v_l_1667_, 0);
v_k_1691_ = lean_ctor_get(v_l_1667_, 1);
v_v_1692_ = lean_ctor_get(v_l_1667_, 2);
v_l_1693_ = lean_ctor_get(v_l_1667_, 3);
v_r_1694_ = lean_ctor_get(v_l_1667_, 4);
v_size_1695_ = lean_ctor_get(v_r_1668_, 0);
v___x_1696_ = lean_unsigned_to_nat(2u);
v___x_1697_ = lean_nat_mul(v___x_1696_, v_size_1695_);
v___x_1698_ = lean_nat_dec_lt(v_size_1690_, v___x_1697_);
lean_dec(v___x_1697_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1726_; 
lean_inc(v_r_1694_);
lean_inc(v_l_1693_);
lean_inc(v_v_1692_);
lean_inc(v_k_1691_);
v_isSharedCheck_1726_ = !lean_is_exclusive(v_l_1667_);
if (v_isSharedCheck_1726_ == 0)
{
lean_object* v_unused_1727_; lean_object* v_unused_1728_; lean_object* v_unused_1729_; lean_object* v_unused_1730_; lean_object* v_unused_1731_; 
v_unused_1727_ = lean_ctor_get(v_l_1667_, 4);
lean_dec(v_unused_1727_);
v_unused_1728_ = lean_ctor_get(v_l_1667_, 3);
lean_dec(v_unused_1728_);
v_unused_1729_ = lean_ctor_get(v_l_1667_, 2);
lean_dec(v_unused_1729_);
v_unused_1730_ = lean_ctor_get(v_l_1667_, 1);
lean_dec(v_unused_1730_);
v_unused_1731_ = lean_ctor_get(v_l_1667_, 0);
lean_dec(v_unused_1731_);
v___x_1700_ = v_l_1667_;
v_isShared_1701_ = v_isSharedCheck_1726_;
goto v_resetjp_1699_;
}
else
{
lean_dec(v_l_1667_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1726_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1716_; 
v___x_1702_ = lean_nat_add(v___x_1669_, v_size_1678_);
v___x_1703_ = lean_nat_add(v___x_1702_, v_size_1664_);
lean_dec(v_size_1664_);
if (lean_obj_tag(v_l_1693_) == 0)
{
lean_object* v_size_1724_; 
v_size_1724_ = lean_ctor_get(v_l_1693_, 0);
lean_inc(v_size_1724_);
v___y_1716_ = v_size_1724_;
goto v___jp_1715_;
}
else
{
lean_object* v___x_1725_; 
v___x_1725_ = lean_unsigned_to_nat(0u);
v___y_1716_ = v___x_1725_;
goto v___jp_1715_;
}
v___jp_1704_:
{
lean_object* v___x_1708_; lean_object* v___x_1710_; 
v___x_1708_ = lean_nat_add(v___y_1705_, v___y_1707_);
lean_dec(v___y_1707_);
lean_dec(v___y_1705_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 4, v_r_1668_);
lean_ctor_set(v___x_1700_, 3, v_r_1694_);
lean_ctor_set(v___x_1700_, 2, v_v_1666_);
lean_ctor_set(v___x_1700_, 1, v_k_1665_);
lean_ctor_set(v___x_1700_, 0, v___x_1708_);
v___x_1710_ = v___x_1700_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1708_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v_k_1665_);
lean_ctor_set(v_reuseFailAlloc_1714_, 2, v_v_1666_);
lean_ctor_set(v_reuseFailAlloc_1714_, 3, v_r_1694_);
lean_ctor_set(v_reuseFailAlloc_1714_, 4, v_r_1668_);
v___x_1710_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
lean_object* v___x_1712_; 
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 4, v___x_1710_);
lean_ctor_set(v___x_1688_, 3, v___y_1706_);
lean_ctor_set(v___x_1688_, 2, v_v_1692_);
lean_ctor_set(v___x_1688_, 1, v_k_1691_);
lean_ctor_set(v___x_1688_, 0, v___x_1703_);
v___x_1712_ = v___x_1688_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1703_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_k_1691_);
lean_ctor_set(v_reuseFailAlloc_1713_, 2, v_v_1692_);
lean_ctor_set(v_reuseFailAlloc_1713_, 3, v___y_1706_);
lean_ctor_set(v_reuseFailAlloc_1713_, 4, v___x_1710_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
v___jp_1715_:
{
lean_object* v___x_1717_; lean_object* v___x_1719_; 
v___x_1717_ = lean_nat_add(v___x_1702_, v___y_1716_);
lean_dec(v___y_1716_);
lean_dec(v___x_1702_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 4, v_l_1693_);
lean_ctor_set(v___x_1672_, 3, v_tree_1675_);
lean_ctor_set(v___x_1672_, 2, v_v_1677_);
lean_ctor_set(v___x_1672_, 1, v_k_1676_);
lean_ctor_set(v___x_1672_, 0, v___x_1717_);
v___x_1719_ = v___x_1672_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1717_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_k_1676_);
lean_ctor_set(v_reuseFailAlloc_1723_, 2, v_v_1677_);
lean_ctor_set(v_reuseFailAlloc_1723_, 3, v_tree_1675_);
lean_ctor_set(v_reuseFailAlloc_1723_, 4, v_l_1693_);
v___x_1719_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
lean_object* v___x_1720_; 
v___x_1720_ = lean_nat_add(v___x_1669_, v_size_1695_);
if (lean_obj_tag(v_r_1694_) == 0)
{
lean_object* v_size_1721_; 
v_size_1721_ = lean_ctor_get(v_r_1694_, 0);
lean_inc(v_size_1721_);
v___y_1705_ = v___x_1720_;
v___y_1706_ = v___x_1719_;
v___y_1707_ = v_size_1721_;
goto v___jp_1704_;
}
else
{
lean_object* v___x_1722_; 
v___x_1722_ = lean_unsigned_to_nat(0u);
v___y_1705_ = v___x_1720_;
v___y_1706_ = v___x_1719_;
v___y_1707_ = v___x_1722_;
goto v___jp_1704_;
}
}
}
}
}
else
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1736_; 
v___x_1732_ = lean_nat_add(v___x_1669_, v_size_1678_);
v___x_1733_ = lean_nat_add(v___x_1732_, v_size_1664_);
lean_dec(v_size_1664_);
v___x_1734_ = lean_nat_add(v___x_1732_, v_size_1690_);
lean_dec(v___x_1732_);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 4, v_l_1667_);
lean_ctor_set(v___x_1688_, 3, v_tree_1675_);
lean_ctor_set(v___x_1688_, 2, v_v_1677_);
lean_ctor_set(v___x_1688_, 1, v_k_1676_);
lean_ctor_set(v___x_1688_, 0, v___x_1734_);
v___x_1736_ = v___x_1688_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1734_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_k_1676_);
lean_ctor_set(v_reuseFailAlloc_1740_, 2, v_v_1677_);
lean_ctor_set(v_reuseFailAlloc_1740_, 3, v_tree_1675_);
lean_ctor_set(v_reuseFailAlloc_1740_, 4, v_l_1667_);
v___x_1736_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
lean_object* v___x_1738_; 
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 4, v_r_1668_);
lean_ctor_set(v___x_1672_, 3, v___x_1736_);
lean_ctor_set(v___x_1672_, 2, v_v_1666_);
lean_ctor_set(v___x_1672_, 1, v_k_1665_);
lean_ctor_set(v___x_1672_, 0, v___x_1733_);
v___x_1738_ = v___x_1672_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1733_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_k_1665_);
lean_ctor_set(v_reuseFailAlloc_1739_, 2, v_v_1666_);
lean_ctor_set(v_reuseFailAlloc_1739_, 3, v___x_1736_);
lean_ctor_set(v_reuseFailAlloc_1739_, 4, v_r_1668_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
}
}
else
{
lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1800_; 
lean_inc(v_r_1668_);
lean_inc(v_v_1666_);
lean_inc(v_k_1665_);
lean_inc(v_size_1664_);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_r_1480_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; lean_object* v_unused_1802_; lean_object* v_unused_1803_; lean_object* v_unused_1804_; lean_object* v_unused_1805_; 
v_unused_1801_ = lean_ctor_get(v_r_1480_, 4);
lean_dec(v_unused_1801_);
v_unused_1802_ = lean_ctor_get(v_r_1480_, 3);
lean_dec(v_unused_1802_);
v_unused_1803_ = lean_ctor_get(v_r_1480_, 2);
lean_dec(v_unused_1803_);
v_unused_1804_ = lean_ctor_get(v_r_1480_, 1);
lean_dec(v_unused_1804_);
v_unused_1805_ = lean_ctor_get(v_r_1480_, 0);
lean_dec(v_unused_1805_);
v___x_1748_ = v_r_1480_;
v_isShared_1749_ = v_isSharedCheck_1800_;
goto v_resetjp_1747_;
}
else
{
lean_dec(v_r_1480_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1800_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
if (lean_obj_tag(v_l_1667_) == 0)
{
if (lean_obj_tag(v_r_1668_) == 0)
{
lean_object* v_k_1750_; lean_object* v_v_1751_; lean_object* v_size_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1756_; 
lean_inc(v_tree_1675_);
v_k_1750_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_k_1750_);
v_v_1751_ = lean_ctor_get(v___x_1674_, 1);
lean_inc(v_v_1751_);
lean_dec_ref(v___x_1674_);
v_size_1752_ = lean_ctor_get(v_l_1667_, 0);
v___x_1753_ = lean_nat_add(v___x_1669_, v_size_1664_);
lean_dec(v_size_1664_);
v___x_1754_ = lean_nat_add(v___x_1669_, v_size_1752_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 4, v_l_1667_);
lean_ctor_set(v___x_1748_, 3, v_tree_1675_);
lean_ctor_set(v___x_1748_, 2, v_v_1751_);
lean_ctor_set(v___x_1748_, 1, v_k_1750_);
lean_ctor_set(v___x_1748_, 0, v___x_1754_);
v___x_1756_ = v___x_1748_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1754_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_k_1750_);
lean_ctor_set(v_reuseFailAlloc_1760_, 2, v_v_1751_);
lean_ctor_set(v_reuseFailAlloc_1760_, 3, v_tree_1675_);
lean_ctor_set(v_reuseFailAlloc_1760_, 4, v_l_1667_);
v___x_1756_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
lean_object* v___x_1758_; 
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 4, v_r_1668_);
lean_ctor_set(v___x_1672_, 3, v___x_1756_);
lean_ctor_set(v___x_1672_, 2, v_v_1666_);
lean_ctor_set(v___x_1672_, 1, v_k_1665_);
lean_ctor_set(v___x_1672_, 0, v___x_1753_);
v___x_1758_ = v___x_1672_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1753_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_k_1665_);
lean_ctor_set(v_reuseFailAlloc_1759_, 2, v_v_1666_);
lean_ctor_set(v_reuseFailAlloc_1759_, 3, v___x_1756_);
lean_ctor_set(v_reuseFailAlloc_1759_, 4, v_r_1668_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
else
{
lean_object* v_k_1761_; lean_object* v_v_1762_; lean_object* v_k_1763_; lean_object* v_v_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1778_; 
lean_dec(v_size_1664_);
v_k_1761_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_k_1761_);
v_v_1762_ = lean_ctor_get(v___x_1674_, 1);
lean_inc(v_v_1762_);
lean_dec_ref(v___x_1674_);
v_k_1763_ = lean_ctor_get(v_l_1667_, 1);
v_v_1764_ = lean_ctor_get(v_l_1667_, 2);
v_isSharedCheck_1778_ = !lean_is_exclusive(v_l_1667_);
if (v_isSharedCheck_1778_ == 0)
{
lean_object* v_unused_1779_; lean_object* v_unused_1780_; lean_object* v_unused_1781_; 
v_unused_1779_ = lean_ctor_get(v_l_1667_, 4);
lean_dec(v_unused_1779_);
v_unused_1780_ = lean_ctor_get(v_l_1667_, 3);
lean_dec(v_unused_1780_);
v_unused_1781_ = lean_ctor_get(v_l_1667_, 0);
lean_dec(v_unused_1781_);
v___x_1766_ = v_l_1667_;
v_isShared_1767_ = v_isSharedCheck_1778_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_v_1764_);
lean_inc(v_k_1763_);
lean_dec(v_l_1667_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1778_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1768_; lean_object* v___x_1770_; 
v___x_1768_ = lean_unsigned_to_nat(3u);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 4, v_r_1668_);
lean_ctor_set(v___x_1766_, 3, v_r_1668_);
lean_ctor_set(v___x_1766_, 2, v_v_1762_);
lean_ctor_set(v___x_1766_, 1, v_k_1761_);
lean_ctor_set(v___x_1766_, 0, v___x_1669_);
v___x_1770_ = v___x_1766_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1669_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_k_1761_);
lean_ctor_set(v_reuseFailAlloc_1777_, 2, v_v_1762_);
lean_ctor_set(v_reuseFailAlloc_1777_, 3, v_r_1668_);
lean_ctor_set(v_reuseFailAlloc_1777_, 4, v_r_1668_);
v___x_1770_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
lean_object* v___x_1772_; 
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 3, v_r_1668_);
lean_ctor_set(v___x_1748_, 0, v___x_1669_);
v___x_1772_ = v___x_1748_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1669_);
lean_ctor_set(v_reuseFailAlloc_1776_, 1, v_k_1665_);
lean_ctor_set(v_reuseFailAlloc_1776_, 2, v_v_1666_);
lean_ctor_set(v_reuseFailAlloc_1776_, 3, v_r_1668_);
lean_ctor_set(v_reuseFailAlloc_1776_, 4, v_r_1668_);
v___x_1772_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1774_; 
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 4, v___x_1772_);
lean_ctor_set(v___x_1672_, 3, v___x_1770_);
lean_ctor_set(v___x_1672_, 2, v_v_1764_);
lean_ctor_set(v___x_1672_, 1, v_k_1763_);
lean_ctor_set(v___x_1672_, 0, v___x_1768_);
v___x_1774_ = v___x_1672_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1768_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v_k_1763_);
lean_ctor_set(v_reuseFailAlloc_1775_, 2, v_v_1764_);
lean_ctor_set(v_reuseFailAlloc_1775_, 3, v___x_1770_);
lean_ctor_set(v_reuseFailAlloc_1775_, 4, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1668_) == 0)
{
lean_object* v_k_1782_; lean_object* v_v_1783_; lean_object* v___x_1784_; lean_object* v___x_1786_; 
lean_dec(v_size_1664_);
v_k_1782_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_k_1782_);
v_v_1783_ = lean_ctor_get(v___x_1674_, 1);
lean_inc(v_v_1783_);
lean_dec_ref(v___x_1674_);
v___x_1784_ = lean_unsigned_to_nat(3u);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 4, v_l_1667_);
lean_ctor_set(v___x_1748_, 2, v_v_1783_);
lean_ctor_set(v___x_1748_, 1, v_k_1782_);
lean_ctor_set(v___x_1748_, 0, v___x_1669_);
v___x_1786_ = v___x_1748_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1669_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_k_1782_);
lean_ctor_set(v_reuseFailAlloc_1790_, 2, v_v_1783_);
lean_ctor_set(v_reuseFailAlloc_1790_, 3, v_l_1667_);
lean_ctor_set(v_reuseFailAlloc_1790_, 4, v_l_1667_);
v___x_1786_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
lean_object* v___x_1788_; 
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 4, v_r_1668_);
lean_ctor_set(v___x_1672_, 3, v___x_1786_);
lean_ctor_set(v___x_1672_, 2, v_v_1666_);
lean_ctor_set(v___x_1672_, 1, v_k_1665_);
lean_ctor_set(v___x_1672_, 0, v___x_1784_);
v___x_1788_ = v___x_1672_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1784_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v_k_1665_);
lean_ctor_set(v_reuseFailAlloc_1789_, 2, v_v_1666_);
lean_ctor_set(v_reuseFailAlloc_1789_, 3, v___x_1786_);
lean_ctor_set(v_reuseFailAlloc_1789_, 4, v_r_1668_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
else
{
lean_object* v_k_1791_; lean_object* v_v_1792_; lean_object* v___x_1794_; 
v_k_1791_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_k_1791_);
v_v_1792_ = lean_ctor_get(v___x_1674_, 1);
lean_inc(v_v_1792_);
lean_dec_ref(v___x_1674_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 3, v_r_1668_);
v___x_1794_ = v___x_1748_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_size_1664_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v_k_1665_);
lean_ctor_set(v_reuseFailAlloc_1799_, 2, v_v_1666_);
lean_ctor_set(v_reuseFailAlloc_1799_, 3, v_r_1668_);
lean_ctor_set(v_reuseFailAlloc_1799_, 4, v_r_1668_);
v___x_1794_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
lean_object* v___x_1795_; lean_object* v___x_1797_; 
v___x_1795_ = lean_unsigned_to_nat(2u);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 4, v___x_1794_);
lean_ctor_set(v___x_1672_, 3, v_r_1668_);
lean_ctor_set(v___x_1672_, 2, v_v_1792_);
lean_ctor_set(v___x_1672_, 1, v_k_1791_);
lean_ctor_set(v___x_1672_, 0, v___x_1795_);
v___x_1797_ = v___x_1672_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1795_);
lean_ctor_set(v_reuseFailAlloc_1798_, 1, v_k_1791_);
lean_ctor_set(v_reuseFailAlloc_1798_, 2, v_v_1792_);
lean_ctor_set(v_reuseFailAlloc_1798_, 3, v_r_1668_);
lean_ctor_set(v_reuseFailAlloc_1798_, 4, v___x_1794_);
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
}
}
}
}
else
{
lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1964_; 
lean_inc(v_r_1668_);
lean_inc(v_v_1666_);
lean_inc(v_k_1665_);
v_isSharedCheck_1964_ = !lean_is_exclusive(v_r_1480_);
if (v_isSharedCheck_1964_ == 0)
{
lean_object* v_unused_1965_; lean_object* v_unused_1966_; lean_object* v_unused_1967_; lean_object* v_unused_1968_; lean_object* v_unused_1969_; 
v_unused_1965_ = lean_ctor_get(v_r_1480_, 4);
lean_dec(v_unused_1965_);
v_unused_1966_ = lean_ctor_get(v_r_1480_, 3);
lean_dec(v_unused_1966_);
v_unused_1967_ = lean_ctor_get(v_r_1480_, 2);
lean_dec(v_unused_1967_);
v_unused_1968_ = lean_ctor_get(v_r_1480_, 1);
lean_dec(v_unused_1968_);
v_unused_1969_ = lean_ctor_get(v_r_1480_, 0);
lean_dec(v_unused_1969_);
v___x_1813_ = v_r_1480_;
v_isShared_1814_ = v_isSharedCheck_1964_;
goto v_resetjp_1812_;
}
else
{
lean_dec(v_r_1480_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1964_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; lean_object* v_tree_1816_; 
v___x_1815_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1665_, v_v_1666_, v_l_1667_, v_r_1668_);
v_tree_1816_ = lean_ctor_get(v___x_1815_, 2);
lean_inc(v_tree_1816_);
if (lean_obj_tag(v_tree_1816_) == 0)
{
lean_object* v_k_1817_; lean_object* v_v_1818_; lean_object* v_size_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; uint8_t v___x_1822_; 
v_k_1817_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_k_1817_);
v_v_1818_ = lean_ctor_get(v___x_1815_, 1);
lean_inc(v_v_1818_);
lean_dec_ref(v___x_1815_);
v_size_1819_ = lean_ctor_get(v_tree_1816_, 0);
v___x_1820_ = lean_unsigned_to_nat(3u);
v___x_1821_ = lean_nat_mul(v___x_1820_, v_size_1819_);
v___x_1822_ = lean_nat_dec_lt(v___x_1821_, v_size_1659_);
lean_dec(v___x_1821_);
if (v___x_1822_ == 0)
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1826_; 
lean_dec(v_r_1663_);
v___x_1823_ = lean_nat_add(v___x_1669_, v_size_1659_);
v___x_1824_ = lean_nat_add(v___x_1823_, v_size_1819_);
lean_dec(v___x_1823_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 4, v_tree_1816_);
lean_ctor_set(v___x_1813_, 3, v_l_1479_);
lean_ctor_set(v___x_1813_, 2, v_v_1818_);
lean_ctor_set(v___x_1813_, 1, v_k_1817_);
lean_ctor_set(v___x_1813_, 0, v___x_1824_);
v___x_1826_ = v___x_1813_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1824_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_k_1817_);
lean_ctor_set(v_reuseFailAlloc_1827_, 2, v_v_1818_);
lean_ctor_set(v_reuseFailAlloc_1827_, 3, v_l_1479_);
lean_ctor_set(v_reuseFailAlloc_1827_, 4, v_tree_1816_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
else
{
lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1893_; 
lean_inc(v_l_1662_);
lean_inc(v_v_1661_);
lean_inc(v_k_1660_);
lean_inc(v_size_1659_);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_l_1479_);
if (v_isSharedCheck_1893_ == 0)
{
lean_object* v_unused_1894_; lean_object* v_unused_1895_; lean_object* v_unused_1896_; lean_object* v_unused_1897_; lean_object* v_unused_1898_; 
v_unused_1894_ = lean_ctor_get(v_l_1479_, 4);
lean_dec(v_unused_1894_);
v_unused_1895_ = lean_ctor_get(v_l_1479_, 3);
lean_dec(v_unused_1895_);
v_unused_1896_ = lean_ctor_get(v_l_1479_, 2);
lean_dec(v_unused_1896_);
v_unused_1897_ = lean_ctor_get(v_l_1479_, 1);
lean_dec(v_unused_1897_);
v_unused_1898_ = lean_ctor_get(v_l_1479_, 0);
lean_dec(v_unused_1898_);
v___x_1829_ = v_l_1479_;
v_isShared_1830_ = v_isSharedCheck_1893_;
goto v_resetjp_1828_;
}
else
{
lean_dec(v_l_1479_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1893_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v_size_1831_; lean_object* v_size_1832_; lean_object* v_k_1833_; lean_object* v_v_1834_; lean_object* v_l_1835_; lean_object* v_r_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; uint8_t v___x_1839_; 
v_size_1831_ = lean_ctor_get(v_l_1662_, 0);
v_size_1832_ = lean_ctor_get(v_r_1663_, 0);
v_k_1833_ = lean_ctor_get(v_r_1663_, 1);
v_v_1834_ = lean_ctor_get(v_r_1663_, 2);
v_l_1835_ = lean_ctor_get(v_r_1663_, 3);
v_r_1836_ = lean_ctor_get(v_r_1663_, 4);
v___x_1837_ = lean_unsigned_to_nat(2u);
v___x_1838_ = lean_nat_mul(v___x_1837_, v_size_1831_);
v___x_1839_ = lean_nat_dec_lt(v_size_1832_, v___x_1838_);
lean_dec(v___x_1838_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1877_; 
lean_inc(v_r_1836_);
lean_inc(v_l_1835_);
lean_inc(v_v_1834_);
lean_inc(v_k_1833_);
lean_del_object(v___x_1829_);
v_isSharedCheck_1877_ = !lean_is_exclusive(v_r_1663_);
if (v_isSharedCheck_1877_ == 0)
{
lean_object* v_unused_1878_; lean_object* v_unused_1879_; lean_object* v_unused_1880_; lean_object* v_unused_1881_; lean_object* v_unused_1882_; 
v_unused_1878_ = lean_ctor_get(v_r_1663_, 4);
lean_dec(v_unused_1878_);
v_unused_1879_ = lean_ctor_get(v_r_1663_, 3);
lean_dec(v_unused_1879_);
v_unused_1880_ = lean_ctor_get(v_r_1663_, 2);
lean_dec(v_unused_1880_);
v_unused_1881_ = lean_ctor_get(v_r_1663_, 1);
lean_dec(v_unused_1881_);
v_unused_1882_ = lean_ctor_get(v_r_1663_, 0);
lean_dec(v_unused_1882_);
v___x_1841_ = v_r_1663_;
v_isShared_1842_ = v_isSharedCheck_1877_;
goto v_resetjp_1840_;
}
else
{
lean_dec(v_r_1663_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1877_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___x_1865_; lean_object* v___y_1867_; 
v___x_1843_ = lean_nat_add(v___x_1669_, v_size_1659_);
lean_dec(v_size_1659_);
v___x_1844_ = lean_nat_add(v___x_1843_, v_size_1819_);
lean_dec(v___x_1843_);
v___x_1865_ = lean_nat_add(v___x_1669_, v_size_1831_);
if (lean_obj_tag(v_l_1835_) == 0)
{
lean_object* v_size_1875_; 
v_size_1875_ = lean_ctor_get(v_l_1835_, 0);
lean_inc(v_size_1875_);
v___y_1867_ = v_size_1875_;
goto v___jp_1866_;
}
else
{
lean_object* v___x_1876_; 
v___x_1876_ = lean_unsigned_to_nat(0u);
v___y_1867_ = v___x_1876_;
goto v___jp_1866_;
}
v___jp_1845_:
{
lean_object* v___x_1849_; lean_object* v___x_1851_; 
v___x_1849_ = lean_nat_add(v___y_1847_, v___y_1848_);
lean_dec(v___y_1848_);
lean_dec(v___y_1847_);
lean_inc_ref(v_tree_1816_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 4, v_tree_1816_);
lean_ctor_set(v___x_1841_, 3, v_r_1836_);
lean_ctor_set(v___x_1841_, 2, v_v_1818_);
lean_ctor_set(v___x_1841_, 1, v_k_1817_);
lean_ctor_set(v___x_1841_, 0, v___x_1849_);
v___x_1851_ = v___x_1841_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1849_);
lean_ctor_set(v_reuseFailAlloc_1864_, 1, v_k_1817_);
lean_ctor_set(v_reuseFailAlloc_1864_, 2, v_v_1818_);
lean_ctor_set(v_reuseFailAlloc_1864_, 3, v_r_1836_);
lean_ctor_set(v_reuseFailAlloc_1864_, 4, v_tree_1816_);
v___x_1851_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
v_isSharedCheck_1858_ = !lean_is_exclusive(v_tree_1816_);
if (v_isSharedCheck_1858_ == 0)
{
lean_object* v_unused_1859_; lean_object* v_unused_1860_; lean_object* v_unused_1861_; lean_object* v_unused_1862_; lean_object* v_unused_1863_; 
v_unused_1859_ = lean_ctor_get(v_tree_1816_, 4);
lean_dec(v_unused_1859_);
v_unused_1860_ = lean_ctor_get(v_tree_1816_, 3);
lean_dec(v_unused_1860_);
v_unused_1861_ = lean_ctor_get(v_tree_1816_, 2);
lean_dec(v_unused_1861_);
v_unused_1862_ = lean_ctor_get(v_tree_1816_, 1);
lean_dec(v_unused_1862_);
v_unused_1863_ = lean_ctor_get(v_tree_1816_, 0);
lean_dec(v_unused_1863_);
v___x_1853_ = v_tree_1816_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_dec(v_tree_1816_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 4, v___x_1851_);
lean_ctor_set(v___x_1853_, 3, v___y_1846_);
lean_ctor_set(v___x_1853_, 2, v_v_1834_);
lean_ctor_set(v___x_1853_, 1, v_k_1833_);
lean_ctor_set(v___x_1853_, 0, v___x_1844_);
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1844_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_k_1833_);
lean_ctor_set(v_reuseFailAlloc_1857_, 2, v_v_1834_);
lean_ctor_set(v_reuseFailAlloc_1857_, 3, v___y_1846_);
lean_ctor_set(v_reuseFailAlloc_1857_, 4, v___x_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
v___jp_1866_:
{
lean_object* v___x_1868_; lean_object* v___x_1870_; 
v___x_1868_ = lean_nat_add(v___x_1865_, v___y_1867_);
lean_dec(v___y_1867_);
lean_dec(v___x_1865_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 4, v_l_1835_);
lean_ctor_set(v___x_1813_, 3, v_l_1662_);
lean_ctor_set(v___x_1813_, 2, v_v_1661_);
lean_ctor_set(v___x_1813_, 1, v_k_1660_);
lean_ctor_set(v___x_1813_, 0, v___x_1868_);
v___x_1870_ = v___x_1813_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___x_1868_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v_k_1660_);
lean_ctor_set(v_reuseFailAlloc_1874_, 2, v_v_1661_);
lean_ctor_set(v_reuseFailAlloc_1874_, 3, v_l_1662_);
lean_ctor_set(v_reuseFailAlloc_1874_, 4, v_l_1835_);
v___x_1870_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
lean_object* v___x_1871_; 
v___x_1871_ = lean_nat_add(v___x_1669_, v_size_1819_);
if (lean_obj_tag(v_r_1836_) == 0)
{
lean_object* v_size_1872_; 
v_size_1872_ = lean_ctor_get(v_r_1836_, 0);
lean_inc(v_size_1872_);
v___y_1846_ = v___x_1870_;
v___y_1847_ = v___x_1871_;
v___y_1848_ = v_size_1872_;
goto v___jp_1845_;
}
else
{
lean_object* v___x_1873_; 
v___x_1873_ = lean_unsigned_to_nat(0u);
v___y_1846_ = v___x_1870_;
v___y_1847_ = v___x_1871_;
v___y_1848_ = v___x_1873_;
goto v___jp_1845_;
}
}
}
}
}
else
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1888_; 
v___x_1883_ = lean_nat_add(v___x_1669_, v_size_1659_);
lean_dec(v_size_1659_);
v___x_1884_ = lean_nat_add(v___x_1883_, v_size_1819_);
lean_dec(v___x_1883_);
v___x_1885_ = lean_nat_add(v___x_1669_, v_size_1819_);
v___x_1886_ = lean_nat_add(v___x_1885_, v_size_1832_);
lean_dec(v___x_1885_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 4, v_tree_1816_);
lean_ctor_set(v___x_1813_, 3, v_r_1663_);
lean_ctor_set(v___x_1813_, 2, v_v_1818_);
lean_ctor_set(v___x_1813_, 1, v_k_1817_);
lean_ctor_set(v___x_1813_, 0, v___x_1886_);
v___x_1888_ = v___x_1813_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1886_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_k_1817_);
lean_ctor_set(v_reuseFailAlloc_1892_, 2, v_v_1818_);
lean_ctor_set(v_reuseFailAlloc_1892_, 3, v_r_1663_);
lean_ctor_set(v_reuseFailAlloc_1892_, 4, v_tree_1816_);
v___x_1888_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1890_; 
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 4, v___x_1888_);
lean_ctor_set(v___x_1829_, 0, v___x_1884_);
v___x_1890_ = v___x_1829_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1884_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_k_1660_);
lean_ctor_set(v_reuseFailAlloc_1891_, 2, v_v_1661_);
lean_ctor_set(v_reuseFailAlloc_1891_, 3, v_l_1662_);
lean_ctor_set(v_reuseFailAlloc_1891_, 4, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1662_) == 0)
{
lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1922_; 
lean_inc_ref(v_l_1662_);
lean_inc(v_v_1661_);
lean_inc(v_k_1660_);
lean_inc(v_size_1659_);
v_isSharedCheck_1922_ = !lean_is_exclusive(v_l_1479_);
if (v_isSharedCheck_1922_ == 0)
{
lean_object* v_unused_1923_; lean_object* v_unused_1924_; lean_object* v_unused_1925_; lean_object* v_unused_1926_; lean_object* v_unused_1927_; 
v_unused_1923_ = lean_ctor_get(v_l_1479_, 4);
lean_dec(v_unused_1923_);
v_unused_1924_ = lean_ctor_get(v_l_1479_, 3);
lean_dec(v_unused_1924_);
v_unused_1925_ = lean_ctor_get(v_l_1479_, 2);
lean_dec(v_unused_1925_);
v_unused_1926_ = lean_ctor_get(v_l_1479_, 1);
lean_dec(v_unused_1926_);
v_unused_1927_ = lean_ctor_get(v_l_1479_, 0);
lean_dec(v_unused_1927_);
v___x_1900_ = v_l_1479_;
v_isShared_1901_ = v_isSharedCheck_1922_;
goto v_resetjp_1899_;
}
else
{
lean_dec(v_l_1479_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1922_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
if (lean_obj_tag(v_r_1663_) == 0)
{
lean_object* v_k_1902_; lean_object* v_v_1903_; lean_object* v_size_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1908_; 
v_k_1902_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_k_1902_);
v_v_1903_ = lean_ctor_get(v___x_1815_, 1);
lean_inc(v_v_1903_);
lean_dec_ref(v___x_1815_);
v_size_1904_ = lean_ctor_get(v_r_1663_, 0);
v___x_1905_ = lean_nat_add(v___x_1669_, v_size_1659_);
lean_dec(v_size_1659_);
v___x_1906_ = lean_nat_add(v___x_1669_, v_size_1904_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 4, v_tree_1816_);
lean_ctor_set(v___x_1813_, 3, v_r_1663_);
lean_ctor_set(v___x_1813_, 2, v_v_1903_);
lean_ctor_set(v___x_1813_, 1, v_k_1902_);
lean_ctor_set(v___x_1813_, 0, v___x_1906_);
v___x_1908_ = v___x_1813_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1906_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v_k_1902_);
lean_ctor_set(v_reuseFailAlloc_1912_, 2, v_v_1903_);
lean_ctor_set(v_reuseFailAlloc_1912_, 3, v_r_1663_);
lean_ctor_set(v_reuseFailAlloc_1912_, 4, v_tree_1816_);
v___x_1908_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
lean_object* v___x_1910_; 
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 4, v___x_1908_);
lean_ctor_set(v___x_1900_, 0, v___x_1905_);
v___x_1910_ = v___x_1900_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1905_);
lean_ctor_set(v_reuseFailAlloc_1911_, 1, v_k_1660_);
lean_ctor_set(v_reuseFailAlloc_1911_, 2, v_v_1661_);
lean_ctor_set(v_reuseFailAlloc_1911_, 3, v_l_1662_);
lean_ctor_set(v_reuseFailAlloc_1911_, 4, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
else
{
lean_object* v_k_1913_; lean_object* v_v_1914_; lean_object* v___x_1915_; lean_object* v___x_1917_; 
lean_dec(v_size_1659_);
v_k_1913_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_k_1913_);
v_v_1914_ = lean_ctor_get(v___x_1815_, 1);
lean_inc(v_v_1914_);
lean_dec_ref(v___x_1815_);
v___x_1915_ = lean_unsigned_to_nat(3u);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 4, v_r_1663_);
lean_ctor_set(v___x_1813_, 3, v_r_1663_);
lean_ctor_set(v___x_1813_, 2, v_v_1914_);
lean_ctor_set(v___x_1813_, 1, v_k_1913_);
lean_ctor_set(v___x_1813_, 0, v___x_1669_);
v___x_1917_ = v___x_1813_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1669_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v_k_1913_);
lean_ctor_set(v_reuseFailAlloc_1921_, 2, v_v_1914_);
lean_ctor_set(v_reuseFailAlloc_1921_, 3, v_r_1663_);
lean_ctor_set(v_reuseFailAlloc_1921_, 4, v_r_1663_);
v___x_1917_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
lean_object* v___x_1919_; 
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 4, v___x_1917_);
lean_ctor_set(v___x_1900_, 0, v___x_1915_);
v___x_1919_ = v___x_1900_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1915_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v_k_1660_);
lean_ctor_set(v_reuseFailAlloc_1920_, 2, v_v_1661_);
lean_ctor_set(v_reuseFailAlloc_1920_, 3, v_l_1662_);
lean_ctor_set(v_reuseFailAlloc_1920_, 4, v___x_1917_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1663_) == 0)
{
lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1952_; 
lean_inc(v_l_1662_);
lean_inc(v_v_1661_);
lean_inc(v_k_1660_);
v_isSharedCheck_1952_ = !lean_is_exclusive(v_l_1479_);
if (v_isSharedCheck_1952_ == 0)
{
lean_object* v_unused_1953_; lean_object* v_unused_1954_; lean_object* v_unused_1955_; lean_object* v_unused_1956_; lean_object* v_unused_1957_; 
v_unused_1953_ = lean_ctor_get(v_l_1479_, 4);
lean_dec(v_unused_1953_);
v_unused_1954_ = lean_ctor_get(v_l_1479_, 3);
lean_dec(v_unused_1954_);
v_unused_1955_ = lean_ctor_get(v_l_1479_, 2);
lean_dec(v_unused_1955_);
v_unused_1956_ = lean_ctor_get(v_l_1479_, 1);
lean_dec(v_unused_1956_);
v_unused_1957_ = lean_ctor_get(v_l_1479_, 0);
lean_dec(v_unused_1957_);
v___x_1929_ = v_l_1479_;
v_isShared_1930_ = v_isSharedCheck_1952_;
goto v_resetjp_1928_;
}
else
{
lean_dec(v_l_1479_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1952_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v_k_1931_; lean_object* v_v_1932_; lean_object* v_k_1933_; lean_object* v_v_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1948_; 
v_k_1931_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_k_1931_);
v_v_1932_ = lean_ctor_get(v___x_1815_, 1);
lean_inc(v_v_1932_);
lean_dec_ref(v___x_1815_);
v_k_1933_ = lean_ctor_get(v_r_1663_, 1);
v_v_1934_ = lean_ctor_get(v_r_1663_, 2);
v_isSharedCheck_1948_ = !lean_is_exclusive(v_r_1663_);
if (v_isSharedCheck_1948_ == 0)
{
lean_object* v_unused_1949_; lean_object* v_unused_1950_; lean_object* v_unused_1951_; 
v_unused_1949_ = lean_ctor_get(v_r_1663_, 4);
lean_dec(v_unused_1949_);
v_unused_1950_ = lean_ctor_get(v_r_1663_, 3);
lean_dec(v_unused_1950_);
v_unused_1951_ = lean_ctor_get(v_r_1663_, 0);
lean_dec(v_unused_1951_);
v___x_1936_ = v_r_1663_;
v_isShared_1937_ = v_isSharedCheck_1948_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_v_1934_);
lean_inc(v_k_1933_);
lean_dec(v_r_1663_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1948_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1938_; lean_object* v___x_1940_; 
v___x_1938_ = lean_unsigned_to_nat(3u);
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 4, v_l_1662_);
lean_ctor_set(v___x_1936_, 3, v_l_1662_);
lean_ctor_set(v___x_1936_, 2, v_v_1661_);
lean_ctor_set(v___x_1936_, 1, v_k_1660_);
lean_ctor_set(v___x_1936_, 0, v___x_1669_);
v___x_1940_ = v___x_1936_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1669_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v_k_1660_);
lean_ctor_set(v_reuseFailAlloc_1947_, 2, v_v_1661_);
lean_ctor_set(v_reuseFailAlloc_1947_, 3, v_l_1662_);
lean_ctor_set(v_reuseFailAlloc_1947_, 4, v_l_1662_);
v___x_1940_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
lean_object* v___x_1942_; 
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 4, v_l_1662_);
lean_ctor_set(v___x_1813_, 3, v_l_1662_);
lean_ctor_set(v___x_1813_, 2, v_v_1932_);
lean_ctor_set(v___x_1813_, 1, v_k_1931_);
lean_ctor_set(v___x_1813_, 0, v___x_1669_);
v___x_1942_ = v___x_1813_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1669_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v_k_1931_);
lean_ctor_set(v_reuseFailAlloc_1946_, 2, v_v_1932_);
lean_ctor_set(v_reuseFailAlloc_1946_, 3, v_l_1662_);
lean_ctor_set(v_reuseFailAlloc_1946_, 4, v_l_1662_);
v___x_1942_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
lean_object* v___x_1944_; 
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 4, v___x_1942_);
lean_ctor_set(v___x_1929_, 3, v___x_1940_);
lean_ctor_set(v___x_1929_, 2, v_v_1934_);
lean_ctor_set(v___x_1929_, 1, v_k_1933_);
lean_ctor_set(v___x_1929_, 0, v___x_1938_);
v___x_1944_ = v___x_1929_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1938_);
lean_ctor_set(v_reuseFailAlloc_1945_, 1, v_k_1933_);
lean_ctor_set(v_reuseFailAlloc_1945_, 2, v_v_1934_);
lean_ctor_set(v_reuseFailAlloc_1945_, 3, v___x_1940_);
lean_ctor_set(v_reuseFailAlloc_1945_, 4, v___x_1942_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
}
}
else
{
lean_object* v_k_1958_; lean_object* v_v_1959_; lean_object* v___x_1960_; lean_object* v___x_1962_; 
v_k_1958_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_k_1958_);
v_v_1959_ = lean_ctor_get(v___x_1815_, 1);
lean_inc(v_v_1959_);
lean_dec_ref(v___x_1815_);
v___x_1960_ = lean_unsigned_to_nat(2u);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 4, v_r_1663_);
lean_ctor_set(v___x_1813_, 3, v_l_1479_);
lean_ctor_set(v___x_1813_, 2, v_v_1959_);
lean_ctor_set(v___x_1813_, 1, v_k_1958_);
lean_ctor_set(v___x_1813_, 0, v___x_1960_);
v___x_1962_ = v___x_1813_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1960_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v_k_1958_);
lean_ctor_set(v_reuseFailAlloc_1963_, 2, v_v_1959_);
lean_ctor_set(v_reuseFailAlloc_1963_, 3, v_l_1479_);
lean_ctor_set(v_reuseFailAlloc_1963_, 4, v_r_1663_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
}
}
}
else
{
return v_l_1479_;
}
}
else
{
return v_r_1480_;
}
}
default: 
{
lean_object* v_impl_1970_; lean_object* v___x_1971_; 
v_impl_1970_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1475_, v_r_1480_);
v___x_1971_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1970_) == 0)
{
if (lean_obj_tag(v_l_1479_) == 0)
{
lean_object* v_size_1972_; lean_object* v_size_1973_; lean_object* v_k_1974_; lean_object* v_v_1975_; lean_object* v_l_1976_; lean_object* v_r_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; uint8_t v___x_1980_; 
v_size_1972_ = lean_ctor_get(v_impl_1970_, 0);
v_size_1973_ = lean_ctor_get(v_l_1479_, 0);
v_k_1974_ = lean_ctor_get(v_l_1479_, 1);
v_v_1975_ = lean_ctor_get(v_l_1479_, 2);
v_l_1976_ = lean_ctor_get(v_l_1479_, 3);
v_r_1977_ = lean_ctor_get(v_l_1479_, 4);
lean_inc(v_r_1977_);
v___x_1978_ = lean_unsigned_to_nat(3u);
v___x_1979_ = lean_nat_mul(v___x_1978_, v_size_1972_);
v___x_1980_ = lean_nat_dec_lt(v___x_1979_, v_size_1973_);
lean_dec(v___x_1979_);
if (v___x_1980_ == 0)
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1984_; 
lean_dec(v_r_1977_);
v___x_1981_ = lean_nat_add(v___x_1971_, v_size_1973_);
v___x_1982_ = lean_nat_add(v___x_1981_, v_size_1972_);
lean_dec(v___x_1981_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 4, v_impl_1970_);
lean_ctor_set(v___x_1482_, 0, v___x_1982_);
v___x_1984_ = v___x_1482_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1982_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v_k_1477_);
lean_ctor_set(v_reuseFailAlloc_1985_, 2, v_v_1478_);
lean_ctor_set(v_reuseFailAlloc_1985_, 3, v_l_1479_);
lean_ctor_set(v_reuseFailAlloc_1985_, 4, v_impl_1970_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
else
{
lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_2051_; 
lean_inc(v_l_1976_);
lean_inc(v_v_1975_);
lean_inc(v_k_1974_);
lean_inc(v_size_1973_);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_l_1479_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; lean_object* v_unused_2053_; lean_object* v_unused_2054_; lean_object* v_unused_2055_; lean_object* v_unused_2056_; 
v_unused_2052_ = lean_ctor_get(v_l_1479_, 4);
lean_dec(v_unused_2052_);
v_unused_2053_ = lean_ctor_get(v_l_1479_, 3);
lean_dec(v_unused_2053_);
v_unused_2054_ = lean_ctor_get(v_l_1479_, 2);
lean_dec(v_unused_2054_);
v_unused_2055_ = lean_ctor_get(v_l_1479_, 1);
lean_dec(v_unused_2055_);
v_unused_2056_ = lean_ctor_get(v_l_1479_, 0);
lean_dec(v_unused_2056_);
v___x_1987_ = v_l_1479_;
v_isShared_1988_ = v_isSharedCheck_2051_;
goto v_resetjp_1986_;
}
else
{
lean_dec(v_l_1479_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_2051_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v_size_1989_; lean_object* v_size_1990_; lean_object* v_k_1991_; lean_object* v_v_1992_; lean_object* v_l_1993_; lean_object* v_r_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; uint8_t v___x_1997_; 
v_size_1989_ = lean_ctor_get(v_l_1976_, 0);
v_size_1990_ = lean_ctor_get(v_r_1977_, 0);
v_k_1991_ = lean_ctor_get(v_r_1977_, 1);
v_v_1992_ = lean_ctor_get(v_r_1977_, 2);
v_l_1993_ = lean_ctor_get(v_r_1977_, 3);
v_r_1994_ = lean_ctor_get(v_r_1977_, 4);
v___x_1995_ = lean_unsigned_to_nat(2u);
v___x_1996_ = lean_nat_mul(v___x_1995_, v_size_1989_);
v___x_1997_ = lean_nat_dec_lt(v_size_1990_, v___x_1996_);
lean_dec(v___x_1996_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2026_; 
lean_inc(v_r_1994_);
lean_inc(v_l_1993_);
lean_inc(v_v_1992_);
lean_inc(v_k_1991_);
v_isSharedCheck_2026_ = !lean_is_exclusive(v_r_1977_);
if (v_isSharedCheck_2026_ == 0)
{
lean_object* v_unused_2027_; lean_object* v_unused_2028_; lean_object* v_unused_2029_; lean_object* v_unused_2030_; lean_object* v_unused_2031_; 
v_unused_2027_ = lean_ctor_get(v_r_1977_, 4);
lean_dec(v_unused_2027_);
v_unused_2028_ = lean_ctor_get(v_r_1977_, 3);
lean_dec(v_unused_2028_);
v_unused_2029_ = lean_ctor_get(v_r_1977_, 2);
lean_dec(v_unused_2029_);
v_unused_2030_ = lean_ctor_get(v_r_1977_, 1);
lean_dec(v_unused_2030_);
v_unused_2031_ = lean_ctor_get(v_r_1977_, 0);
lean_dec(v_unused_2031_);
v___x_1999_ = v_r_1977_;
v_isShared_2000_ = v_isSharedCheck_2026_;
goto v_resetjp_1998_;
}
else
{
lean_dec(v_r_1977_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2026_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___x_2014_; lean_object* v___y_2016_; 
v___x_2001_ = lean_nat_add(v___x_1971_, v_size_1973_);
lean_dec(v_size_1973_);
v___x_2002_ = lean_nat_add(v___x_2001_, v_size_1972_);
lean_dec(v___x_2001_);
v___x_2014_ = lean_nat_add(v___x_1971_, v_size_1989_);
if (lean_obj_tag(v_l_1993_) == 0)
{
lean_object* v_size_2024_; 
v_size_2024_ = lean_ctor_get(v_l_1993_, 0);
lean_inc(v_size_2024_);
v___y_2016_ = v_size_2024_;
goto v___jp_2015_;
}
else
{
lean_object* v___x_2025_; 
v___x_2025_ = lean_unsigned_to_nat(0u);
v___y_2016_ = v___x_2025_;
goto v___jp_2015_;
}
v___jp_2003_:
{
lean_object* v___x_2007_; lean_object* v___x_2009_; 
v___x_2007_ = lean_nat_add(v___y_2005_, v___y_2006_);
lean_dec(v___y_2006_);
lean_dec(v___y_2005_);
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 4, v_impl_1970_);
lean_ctor_set(v___x_1999_, 3, v_r_1994_);
lean_ctor_set(v___x_1999_, 2, v_v_1478_);
lean_ctor_set(v___x_1999_, 1, v_k_1477_);
lean_ctor_set(v___x_1999_, 0, v___x_2007_);
v___x_2009_ = v___x_1999_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2007_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v_k_1477_);
lean_ctor_set(v_reuseFailAlloc_2013_, 2, v_v_1478_);
lean_ctor_set(v_reuseFailAlloc_2013_, 3, v_r_1994_);
lean_ctor_set(v_reuseFailAlloc_2013_, 4, v_impl_1970_);
v___x_2009_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
lean_object* v___x_2011_; 
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 4, v___x_2009_);
lean_ctor_set(v___x_1987_, 3, v___y_2004_);
lean_ctor_set(v___x_1987_, 2, v_v_1992_);
lean_ctor_set(v___x_1987_, 1, v_k_1991_);
lean_ctor_set(v___x_1987_, 0, v___x_2002_);
v___x_2011_ = v___x_1987_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_2002_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v_k_1991_);
lean_ctor_set(v_reuseFailAlloc_2012_, 2, v_v_1992_);
lean_ctor_set(v_reuseFailAlloc_2012_, 3, v___y_2004_);
lean_ctor_set(v_reuseFailAlloc_2012_, 4, v___x_2009_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
v___jp_2015_:
{
lean_object* v___x_2017_; lean_object* v___x_2019_; 
v___x_2017_ = lean_nat_add(v___x_2014_, v___y_2016_);
lean_dec(v___y_2016_);
lean_dec(v___x_2014_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 4, v_l_1993_);
lean_ctor_set(v___x_1482_, 3, v_l_1976_);
lean_ctor_set(v___x_1482_, 2, v_v_1975_);
lean_ctor_set(v___x_1482_, 1, v_k_1974_);
lean_ctor_set(v___x_1482_, 0, v___x_2017_);
v___x_2019_ = v___x_1482_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2017_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_k_1974_);
lean_ctor_set(v_reuseFailAlloc_2023_, 2, v_v_1975_);
lean_ctor_set(v_reuseFailAlloc_2023_, 3, v_l_1976_);
lean_ctor_set(v_reuseFailAlloc_2023_, 4, v_l_1993_);
v___x_2019_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
lean_object* v___x_2020_; 
v___x_2020_ = lean_nat_add(v___x_1971_, v_size_1972_);
if (lean_obj_tag(v_r_1994_) == 0)
{
lean_object* v_size_2021_; 
v_size_2021_ = lean_ctor_get(v_r_1994_, 0);
lean_inc(v_size_2021_);
v___y_2004_ = v___x_2019_;
v___y_2005_ = v___x_2020_;
v___y_2006_ = v_size_2021_;
goto v___jp_2003_;
}
else
{
lean_object* v___x_2022_; 
v___x_2022_ = lean_unsigned_to_nat(0u);
v___y_2004_ = v___x_2019_;
v___y_2005_ = v___x_2020_;
v___y_2006_ = v___x_2022_;
goto v___jp_2003_;
}
}
}
}
}
else
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2037_; 
lean_del_object(v___x_1482_);
v___x_2032_ = lean_nat_add(v___x_1971_, v_size_1973_);
lean_dec(v_size_1973_);
v___x_2033_ = lean_nat_add(v___x_2032_, v_size_1972_);
lean_dec(v___x_2032_);
v___x_2034_ = lean_nat_add(v___x_1971_, v_size_1972_);
v___x_2035_ = lean_nat_add(v___x_2034_, v_size_1990_);
lean_dec(v___x_2034_);
lean_inc_ref(v_impl_1970_);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 4, v_impl_1970_);
lean_ctor_set(v___x_1987_, 3, v_r_1977_);
lean_ctor_set(v___x_1987_, 2, v_v_1478_);
lean_ctor_set(v___x_1987_, 1, v_k_1477_);
lean_ctor_set(v___x_1987_, 0, v___x_2035_);
v___x_2037_ = v___x_1987_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v_k_1477_);
lean_ctor_set(v_reuseFailAlloc_2050_, 2, v_v_1478_);
lean_ctor_set(v_reuseFailAlloc_2050_, 3, v_r_1977_);
lean_ctor_set(v_reuseFailAlloc_2050_, 4, v_impl_1970_);
v___x_2037_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
v_isSharedCheck_2044_ = !lean_is_exclusive(v_impl_1970_);
if (v_isSharedCheck_2044_ == 0)
{
lean_object* v_unused_2045_; lean_object* v_unused_2046_; lean_object* v_unused_2047_; lean_object* v_unused_2048_; lean_object* v_unused_2049_; 
v_unused_2045_ = lean_ctor_get(v_impl_1970_, 4);
lean_dec(v_unused_2045_);
v_unused_2046_ = lean_ctor_get(v_impl_1970_, 3);
lean_dec(v_unused_2046_);
v_unused_2047_ = lean_ctor_get(v_impl_1970_, 2);
lean_dec(v_unused_2047_);
v_unused_2048_ = lean_ctor_get(v_impl_1970_, 1);
lean_dec(v_unused_2048_);
v_unused_2049_ = lean_ctor_get(v_impl_1970_, 0);
lean_dec(v_unused_2049_);
v___x_2039_ = v_impl_1970_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_dec(v_impl_1970_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 4, v___x_2037_);
lean_ctor_set(v___x_2039_, 3, v_l_1976_);
lean_ctor_set(v___x_2039_, 2, v_v_1975_);
lean_ctor_set(v___x_2039_, 1, v_k_1974_);
lean_ctor_set(v___x_2039_, 0, v___x_2033_);
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2033_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_k_1974_);
lean_ctor_set(v_reuseFailAlloc_2043_, 2, v_v_1975_);
lean_ctor_set(v_reuseFailAlloc_2043_, 3, v_l_1976_);
lean_ctor_set(v_reuseFailAlloc_2043_, 4, v___x_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2057_; lean_object* v___x_2058_; lean_object* v___x_2060_; 
v_size_2057_ = lean_ctor_get(v_impl_1970_, 0);
v___x_2058_ = lean_nat_add(v___x_1971_, v_size_2057_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 4, v_impl_1970_);
lean_ctor_set(v___x_1482_, 0, v___x_2058_);
v___x_2060_ = v___x_1482_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2058_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v_k_1477_);
lean_ctor_set(v_reuseFailAlloc_2061_, 2, v_v_1478_);
lean_ctor_set(v_reuseFailAlloc_2061_, 3, v_l_1479_);
lean_ctor_set(v_reuseFailAlloc_2061_, 4, v_impl_1970_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
else
{
if (lean_obj_tag(v_l_1479_) == 0)
{
lean_object* v_l_2062_; 
v_l_2062_ = lean_ctor_get(v_l_1479_, 3);
if (lean_obj_tag(v_l_2062_) == 0)
{
lean_object* v_r_2063_; 
lean_inc_ref(v_l_2062_);
v_r_2063_ = lean_ctor_get(v_l_1479_, 4);
lean_inc(v_r_2063_);
if (lean_obj_tag(v_r_2063_) == 0)
{
lean_object* v_size_2064_; lean_object* v_k_2065_; lean_object* v_v_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2079_; 
v_size_2064_ = lean_ctor_get(v_l_1479_, 0);
v_k_2065_ = lean_ctor_get(v_l_1479_, 1);
v_v_2066_ = lean_ctor_get(v_l_1479_, 2);
v_isSharedCheck_2079_ = !lean_is_exclusive(v_l_1479_);
if (v_isSharedCheck_2079_ == 0)
{
lean_object* v_unused_2080_; lean_object* v_unused_2081_; 
v_unused_2080_ = lean_ctor_get(v_l_1479_, 4);
lean_dec(v_unused_2080_);
v_unused_2081_ = lean_ctor_get(v_l_1479_, 3);
lean_dec(v_unused_2081_);
v___x_2068_ = v_l_1479_;
v_isShared_2069_ = v_isSharedCheck_2079_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_v_2066_);
lean_inc(v_k_2065_);
lean_inc(v_size_2064_);
lean_dec(v_l_1479_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2079_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v_size_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2074_; 
v_size_2070_ = lean_ctor_get(v_r_2063_, 0);
v___x_2071_ = lean_nat_add(v___x_1971_, v_size_2064_);
lean_dec(v_size_2064_);
v___x_2072_ = lean_nat_add(v___x_1971_, v_size_2070_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 4, v_impl_1970_);
lean_ctor_set(v___x_2068_, 3, v_r_2063_);
lean_ctor_set(v___x_2068_, 2, v_v_1478_);
lean_ctor_set(v___x_2068_, 1, v_k_1477_);
lean_ctor_set(v___x_2068_, 0, v___x_2072_);
v___x_2074_ = v___x_2068_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2072_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_k_1477_);
lean_ctor_set(v_reuseFailAlloc_2078_, 2, v_v_1478_);
lean_ctor_set(v_reuseFailAlloc_2078_, 3, v_r_2063_);
lean_ctor_set(v_reuseFailAlloc_2078_, 4, v_impl_1970_);
v___x_2074_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
lean_object* v___x_2076_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 4, v___x_2074_);
lean_ctor_set(v___x_1482_, 3, v_l_2062_);
lean_ctor_set(v___x_1482_, 2, v_v_2066_);
lean_ctor_set(v___x_1482_, 1, v_k_2065_);
lean_ctor_set(v___x_1482_, 0, v___x_2071_);
v___x_2076_ = v___x_1482_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2071_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2077_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2077_, 3, v_l_2062_);
lean_ctor_set(v_reuseFailAlloc_2077_, 4, v___x_2074_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
else
{
lean_object* v_k_2082_; lean_object* v_v_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2094_; 
v_k_2082_ = lean_ctor_get(v_l_1479_, 1);
v_v_2083_ = lean_ctor_get(v_l_1479_, 2);
v_isSharedCheck_2094_ = !lean_is_exclusive(v_l_1479_);
if (v_isSharedCheck_2094_ == 0)
{
lean_object* v_unused_2095_; lean_object* v_unused_2096_; lean_object* v_unused_2097_; 
v_unused_2095_ = lean_ctor_get(v_l_1479_, 4);
lean_dec(v_unused_2095_);
v_unused_2096_ = lean_ctor_get(v_l_1479_, 3);
lean_dec(v_unused_2096_);
v_unused_2097_ = lean_ctor_get(v_l_1479_, 0);
lean_dec(v_unused_2097_);
v___x_2085_ = v_l_1479_;
v_isShared_2086_ = v_isSharedCheck_2094_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_v_2083_);
lean_inc(v_k_2082_);
lean_dec(v_l_1479_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2094_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2087_; lean_object* v___x_2089_; 
v___x_2087_ = lean_unsigned_to_nat(3u);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 3, v_r_2063_);
lean_ctor_set(v___x_2085_, 2, v_v_1478_);
lean_ctor_set(v___x_2085_, 1, v_k_1477_);
lean_ctor_set(v___x_2085_, 0, v___x_1971_);
v___x_2089_ = v___x_2085_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_1971_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v_k_1477_);
lean_ctor_set(v_reuseFailAlloc_2093_, 2, v_v_1478_);
lean_ctor_set(v_reuseFailAlloc_2093_, 3, v_r_2063_);
lean_ctor_set(v_reuseFailAlloc_2093_, 4, v_r_2063_);
v___x_2089_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
lean_object* v___x_2091_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 4, v___x_2089_);
lean_ctor_set(v___x_1482_, 3, v_l_2062_);
lean_ctor_set(v___x_1482_, 2, v_v_2083_);
lean_ctor_set(v___x_1482_, 1, v_k_2082_);
lean_ctor_set(v___x_1482_, 0, v___x_2087_);
v___x_2091_ = v___x_1482_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2087_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v_k_2082_);
lean_ctor_set(v_reuseFailAlloc_2092_, 2, v_v_2083_);
lean_ctor_set(v_reuseFailAlloc_2092_, 3, v_l_2062_);
lean_ctor_set(v_reuseFailAlloc_2092_, 4, v___x_2089_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
}
else
{
lean_object* v_r_2098_; 
v_r_2098_ = lean_ctor_get(v_l_1479_, 4);
lean_inc(v_r_2098_);
if (lean_obj_tag(v_r_2098_) == 0)
{
lean_object* v_k_2099_; lean_object* v_v_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2123_; 
lean_inc(v_l_2062_);
v_k_2099_ = lean_ctor_get(v_l_1479_, 1);
v_v_2100_ = lean_ctor_get(v_l_1479_, 2);
v_isSharedCheck_2123_ = !lean_is_exclusive(v_l_1479_);
if (v_isSharedCheck_2123_ == 0)
{
lean_object* v_unused_2124_; lean_object* v_unused_2125_; lean_object* v_unused_2126_; 
v_unused_2124_ = lean_ctor_get(v_l_1479_, 4);
lean_dec(v_unused_2124_);
v_unused_2125_ = lean_ctor_get(v_l_1479_, 3);
lean_dec(v_unused_2125_);
v_unused_2126_ = lean_ctor_get(v_l_1479_, 0);
lean_dec(v_unused_2126_);
v___x_2102_ = v_l_1479_;
v_isShared_2103_ = v_isSharedCheck_2123_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_v_2100_);
lean_inc(v_k_2099_);
lean_dec(v_l_1479_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2123_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v_k_2104_; lean_object* v_v_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2119_; 
v_k_2104_ = lean_ctor_get(v_r_2098_, 1);
v_v_2105_ = lean_ctor_get(v_r_2098_, 2);
v_isSharedCheck_2119_ = !lean_is_exclusive(v_r_2098_);
if (v_isSharedCheck_2119_ == 0)
{
lean_object* v_unused_2120_; lean_object* v_unused_2121_; lean_object* v_unused_2122_; 
v_unused_2120_ = lean_ctor_get(v_r_2098_, 4);
lean_dec(v_unused_2120_);
v_unused_2121_ = lean_ctor_get(v_r_2098_, 3);
lean_dec(v_unused_2121_);
v_unused_2122_ = lean_ctor_get(v_r_2098_, 0);
lean_dec(v_unused_2122_);
v___x_2107_ = v_r_2098_;
v_isShared_2108_ = v_isSharedCheck_2119_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_v_2105_);
lean_inc(v_k_2104_);
lean_dec(v_r_2098_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2119_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2109_; lean_object* v___x_2111_; 
v___x_2109_ = lean_unsigned_to_nat(3u);
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 4, v_l_2062_);
lean_ctor_set(v___x_2107_, 3, v_l_2062_);
lean_ctor_set(v___x_2107_, 2, v_v_2100_);
lean_ctor_set(v___x_2107_, 1, v_k_2099_);
lean_ctor_set(v___x_2107_, 0, v___x_1971_);
v___x_2111_ = v___x_2107_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_1971_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v_k_2099_);
lean_ctor_set(v_reuseFailAlloc_2118_, 2, v_v_2100_);
lean_ctor_set(v_reuseFailAlloc_2118_, 3, v_l_2062_);
lean_ctor_set(v_reuseFailAlloc_2118_, 4, v_l_2062_);
v___x_2111_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
lean_object* v___x_2113_; 
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 4, v_l_2062_);
lean_ctor_set(v___x_2102_, 2, v_v_1478_);
lean_ctor_set(v___x_2102_, 1, v_k_1477_);
lean_ctor_set(v___x_2102_, 0, v___x_1971_);
v___x_2113_ = v___x_2102_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_1971_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_k_1477_);
lean_ctor_set(v_reuseFailAlloc_2117_, 2, v_v_1478_);
lean_ctor_set(v_reuseFailAlloc_2117_, 3, v_l_2062_);
lean_ctor_set(v_reuseFailAlloc_2117_, 4, v_l_2062_);
v___x_2113_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v___x_2115_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 4, v___x_2113_);
lean_ctor_set(v___x_1482_, 3, v___x_2111_);
lean_ctor_set(v___x_1482_, 2, v_v_2105_);
lean_ctor_set(v___x_1482_, 1, v_k_2104_);
lean_ctor_set(v___x_1482_, 0, v___x_2109_);
v___x_2115_ = v___x_1482_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2109_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_k_2104_);
lean_ctor_set(v_reuseFailAlloc_2116_, 2, v_v_2105_);
lean_ctor_set(v_reuseFailAlloc_2116_, 3, v___x_2111_);
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
}
}
else
{
lean_object* v___x_2127_; lean_object* v___x_2129_; 
v___x_2127_ = lean_unsigned_to_nat(2u);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 4, v_r_2098_);
lean_ctor_set(v___x_1482_, 0, v___x_2127_);
v___x_2129_ = v___x_1482_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2127_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_k_1477_);
lean_ctor_set(v_reuseFailAlloc_2130_, 2, v_v_1478_);
lean_ctor_set(v_reuseFailAlloc_2130_, 3, v_l_1479_);
lean_ctor_set(v_reuseFailAlloc_2130_, 4, v_r_2098_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
else
{
lean_object* v___x_2132_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 4, v_l_1479_);
lean_ctor_set(v___x_1482_, 0, v___x_1971_);
v___x_2132_ = v___x_1482_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v___x_1971_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_k_1477_);
lean_ctor_set(v_reuseFailAlloc_2133_, 2, v_v_1478_);
lean_ctor_set(v_reuseFailAlloc_2133_, 3, v_l_1479_);
lean_ctor_set(v_reuseFailAlloc_2133_, 4, v_l_1479_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
}
}
}
else
{
return v_t_1476_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg___boxed(lean_object* v_k_2136_, lean_object* v_t_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_2136_, v_t_2137_);
lean_dec_ref(v_k_2136_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___lam__0(lean_object* v_val_2139_, lean_object* v_s_2140_){
_start:
{
lean_object* v_toRingState_2141_; lean_object* v_denoteEntries_2142_; lean_object* v_nextId_2143_; lean_object* v_steps_2144_; lean_object* v_queue_2145_; lean_object* v_basis_2146_; lean_object* v_diseqs_2147_; uint8_t v_recheck_2148_; lean_object* v_invSet_2149_; lean_object* v_powIdentityVarCount_2150_; lean_object* v_numEq0_x3f_2151_; uint8_t v_numEq0Updated_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2160_; 
v_toRingState_2141_ = lean_ctor_get(v_s_2140_, 0);
v_denoteEntries_2142_ = lean_ctor_get(v_s_2140_, 1);
v_nextId_2143_ = lean_ctor_get(v_s_2140_, 2);
v_steps_2144_ = lean_ctor_get(v_s_2140_, 3);
v_queue_2145_ = lean_ctor_get(v_s_2140_, 4);
v_basis_2146_ = lean_ctor_get(v_s_2140_, 5);
v_diseqs_2147_ = lean_ctor_get(v_s_2140_, 6);
v_recheck_2148_ = lean_ctor_get_uint8(v_s_2140_, sizeof(void*)*10);
v_invSet_2149_ = lean_ctor_get(v_s_2140_, 7);
v_powIdentityVarCount_2150_ = lean_ctor_get(v_s_2140_, 8);
v_numEq0_x3f_2151_ = lean_ctor_get(v_s_2140_, 9);
v_numEq0Updated_2152_ = lean_ctor_get_uint8(v_s_2140_, sizeof(void*)*10 + 1);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_s_2140_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2154_ = v_s_2140_;
v_isShared_2155_ = v_isSharedCheck_2160_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_numEq0_x3f_2151_);
lean_inc(v_powIdentityVarCount_2150_);
lean_inc(v_invSet_2149_);
lean_inc(v_diseqs_2147_);
lean_inc(v_basis_2146_);
lean_inc(v_queue_2145_);
lean_inc(v_steps_2144_);
lean_inc(v_nextId_2143_);
lean_inc(v_denoteEntries_2142_);
lean_inc(v_toRingState_2141_);
lean_dec(v_s_2140_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2160_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2156_; lean_object* v___x_2158_; 
v___x_2156_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_val_2139_, v_queue_2145_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 4, v___x_2156_);
v___x_2158_ = v___x_2154_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_toRingState_2141_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_denoteEntries_2142_);
lean_ctor_set(v_reuseFailAlloc_2159_, 2, v_nextId_2143_);
lean_ctor_set(v_reuseFailAlloc_2159_, 3, v_steps_2144_);
lean_ctor_set(v_reuseFailAlloc_2159_, 4, v___x_2156_);
lean_ctor_set(v_reuseFailAlloc_2159_, 5, v_basis_2146_);
lean_ctor_set(v_reuseFailAlloc_2159_, 6, v_diseqs_2147_);
lean_ctor_set(v_reuseFailAlloc_2159_, 7, v_invSet_2149_);
lean_ctor_set(v_reuseFailAlloc_2159_, 8, v_powIdentityVarCount_2150_);
lean_ctor_set(v_reuseFailAlloc_2159_, 9, v_numEq0_x3f_2151_);
lean_ctor_set_uint8(v_reuseFailAlloc_2159_, sizeof(void*)*10, v_recheck_2148_);
lean_ctor_set_uint8(v_reuseFailAlloc_2159_, sizeof(void*)*10 + 1, v_numEq0Updated_2152_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___lam__0___boxed(lean_object* v_val_2161_, lean_object* v_s_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___lam__0(v_val_2161_, v_s_2162_);
lean_dec_ref(v_val_2161_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg(lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_){
_start:
{
lean_object* v___x_2168_; 
v___x_2168_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_2164_, v_a_2165_, v_a_2166_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2208_; 
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2171_ = v___x_2168_;
v_isShared_2172_ = v_isSharedCheck_2208_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2168_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2208_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v_queue_2173_; lean_object* v___x_2174_; 
v_queue_2173_ = lean_ctor_get(v_a_2169_, 4);
lean_inc(v_queue_2173_);
lean_dec(v_a_2169_);
v___x_2174_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_queue_2173_);
lean_dec(v_queue_2173_);
if (lean_obj_tag(v___x_2174_) == 1)
{
lean_object* v_val_2175_; lean_object* v___f_2176_; lean_object* v___x_2177_; 
lean_del_object(v___x_2171_);
v_val_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_val_2175_);
v___f_2176_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2176_, 0, v_val_2175_);
v___x_2177_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(v___f_2176_, v_a_2164_, v_a_2165_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
lean_dec_ref_known(v___x_2177_, 1);
v___x_2178_ = lean_unsigned_to_nat(1u);
v___x_2179_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v___x_2178_, v_a_2165_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2186_ == 0)
{
lean_object* v_unused_2187_; 
v_unused_2187_ = lean_ctor_get(v___x_2179_, 0);
lean_dec(v_unused_2187_);
v___x_2181_ = v___x_2179_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_dec(v___x_2179_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 0, v___x_2174_);
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2174_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_dec_ref_known(v___x_2174_, 1);
v_a_2188_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2179_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2179_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
else
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
lean_dec_ref_known(v___x_2174_, 1);
v_a_2196_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2198_ = v___x_2177_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___x_2177_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2196_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
else
{
lean_object* v___x_2204_; lean_object* v___x_2206_; 
lean_dec(v___x_2174_);
v___x_2204_ = lean_box(0);
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 0, v___x_2204_);
v___x_2206_ = v___x_2171_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_2204_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
v_a_2209_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2168_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2168_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___boxed(lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg(v_a_2217_, v_a_2218_, v_a_2219_);
lean_dec_ref(v_a_2219_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_){
_start:
{
lean_object* v___x_2234_; 
v___x_2234_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg(v_a_2222_, v_a_2223_, v_a_2231_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___boxed(lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_);
lean_dec(v_a_2245_);
lean_dec_ref(v_a_2244_);
lean_dec(v_a_2243_);
lean_dec_ref(v_a_2242_);
lean_dec(v_a_2241_);
lean_dec_ref(v_a_2240_);
lean_dec(v_a_2239_);
lean_dec_ref(v_a_2238_);
lean_dec(v_a_2237_);
lean_dec(v_a_2236_);
lean_dec_ref(v_a_2235_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(lean_object* v_00_u03b2_2248_, lean_object* v_k_2249_, lean_object* v_t_2250_, lean_object* v_h_2251_){
_start:
{
lean_object* v___x_2252_; 
v___x_2252_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_2249_, v_t_2250_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___boxed(lean_object* v_00_u03b2_2253_, lean_object* v_k_2254_, lean_object* v_t_2255_, lean_object* v_h_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(v_00_u03b2_2253_, v_k_2254_, v_t_2255_, v_h_2256_);
lean_dec_ref(v_k_2254_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2258_, lean_object* v_x_2259_, lean_object* v_x_2260_, lean_object* v_x_2261_){
_start:
{
lean_object* v_ks_2262_; lean_object* v_vs_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2289_; 
v_ks_2262_ = lean_ctor_get(v_x_2258_, 0);
v_vs_2263_ = lean_ctor_get(v_x_2258_, 1);
v_isSharedCheck_2289_ = !lean_is_exclusive(v_x_2258_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2265_ = v_x_2258_;
v_isShared_2266_ = v_isSharedCheck_2289_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_vs_2263_);
lean_inc(v_ks_2262_);
lean_dec(v_x_2258_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2289_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2267_; uint8_t v___x_2268_; 
v___x_2267_ = lean_array_get_size(v_ks_2262_);
v___x_2268_ = lean_nat_dec_lt(v_x_2259_, v___x_2267_);
if (v___x_2268_ == 0)
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2272_; 
lean_dec(v_x_2259_);
v___x_2269_ = lean_array_push(v_ks_2262_, v_x_2260_);
v___x_2270_ = lean_array_push(v_vs_2263_, v_x_2261_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 1, v___x_2270_);
lean_ctor_set(v___x_2265_, 0, v___x_2269_);
v___x_2272_ = v___x_2265_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2269_);
lean_ctor_set(v_reuseFailAlloc_2273_, 1, v___x_2270_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
else
{
lean_object* v_k_x27_2274_; size_t v___x_2275_; size_t v___x_2276_; uint8_t v___x_2277_; 
v_k_x27_2274_ = lean_array_fget_borrowed(v_ks_2262_, v_x_2259_);
v___x_2275_ = lean_ptr_addr(v_x_2260_);
v___x_2276_ = lean_ptr_addr(v_k_x27_2274_);
v___x_2277_ = lean_usize_dec_eq(v___x_2275_, v___x_2276_);
if (v___x_2277_ == 0)
{
lean_object* v___x_2279_; 
if (v_isShared_2266_ == 0)
{
v___x_2279_ = v___x_2265_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_ks_2262_);
lean_ctor_set(v_reuseFailAlloc_2283_, 1, v_vs_2263_);
v___x_2279_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2280_ = lean_unsigned_to_nat(1u);
v___x_2281_ = lean_nat_add(v_x_2259_, v___x_2280_);
lean_dec(v_x_2259_);
v_x_2258_ = v___x_2279_;
v_x_2259_ = v___x_2281_;
goto _start;
}
}
else
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2287_; 
v___x_2284_ = lean_array_fset(v_ks_2262_, v_x_2259_, v_x_2260_);
v___x_2285_ = lean_array_fset(v_vs_2263_, v_x_2259_, v_x_2261_);
lean_dec(v_x_2259_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 1, v___x_2285_);
lean_ctor_set(v___x_2265_, 0, v___x_2284_);
v___x_2287_ = v___x_2265_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2284_);
lean_ctor_set(v_reuseFailAlloc_2288_, 1, v___x_2285_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2290_, lean_object* v_k_2291_, lean_object* v_v_2292_){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = lean_unsigned_to_nat(0u);
v___x_2294_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2290_, v___x_2293_, v_k_2291_, v_v_2292_);
return v___x_2294_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(lean_object* v_x_2296_, size_t v_x_2297_, size_t v_x_2298_, lean_object* v_x_2299_, lean_object* v_x_2300_){
_start:
{
if (lean_obj_tag(v_x_2296_) == 0)
{
lean_object* v_es_2301_; size_t v___x_2302_; size_t v___x_2303_; lean_object* v_j_2304_; lean_object* v___x_2305_; uint8_t v___x_2306_; 
v_es_2301_ = lean_ctor_get(v_x_2296_, 0);
v___x_2302_ = ((size_t)31ULL);
v___x_2303_ = lean_usize_land(v_x_2297_, v___x_2302_);
v_j_2304_ = lean_usize_to_nat(v___x_2303_);
v___x_2305_ = lean_array_get_size(v_es_2301_);
v___x_2306_ = lean_nat_dec_lt(v_j_2304_, v___x_2305_);
if (v___x_2306_ == 0)
{
lean_dec(v_j_2304_);
lean_dec(v_x_2300_);
lean_dec_ref(v_x_2299_);
return v_x_2296_;
}
else
{
lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2347_; 
lean_inc_ref(v_es_2301_);
v_isSharedCheck_2347_ = !lean_is_exclusive(v_x_2296_);
if (v_isSharedCheck_2347_ == 0)
{
lean_object* v_unused_2348_; 
v_unused_2348_ = lean_ctor_get(v_x_2296_, 0);
lean_dec(v_unused_2348_);
v___x_2308_ = v_x_2296_;
v_isShared_2309_ = v_isSharedCheck_2347_;
goto v_resetjp_2307_;
}
else
{
lean_dec(v_x_2296_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2347_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v_v_2310_; lean_object* v___x_2311_; lean_object* v_xs_x27_2312_; lean_object* v___y_2314_; 
v_v_2310_ = lean_array_fget(v_es_2301_, v_j_2304_);
v___x_2311_ = lean_box(0);
v_xs_x27_2312_ = lean_array_fset(v_es_2301_, v_j_2304_, v___x_2311_);
switch(lean_obj_tag(v_v_2310_))
{
case 0:
{
lean_object* v_key_2319_; lean_object* v_val_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2332_; 
v_key_2319_ = lean_ctor_get(v_v_2310_, 0);
v_val_2320_ = lean_ctor_get(v_v_2310_, 1);
v_isSharedCheck_2332_ = !lean_is_exclusive(v_v_2310_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2322_ = v_v_2310_;
v_isShared_2323_ = v_isSharedCheck_2332_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_val_2320_);
lean_inc(v_key_2319_);
lean_dec(v_v_2310_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2332_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
size_t v___x_2324_; size_t v___x_2325_; uint8_t v___x_2326_; 
v___x_2324_ = lean_ptr_addr(v_x_2299_);
v___x_2325_ = lean_ptr_addr(v_key_2319_);
v___x_2326_ = lean_usize_dec_eq(v___x_2324_, v___x_2325_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
lean_del_object(v___x_2322_);
v___x_2327_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2319_, v_val_2320_, v_x_2299_, v_x_2300_);
v___x_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2327_);
v___y_2314_ = v___x_2328_;
goto v___jp_2313_;
}
else
{
lean_object* v___x_2330_; 
lean_dec(v_val_2320_);
lean_dec(v_key_2319_);
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 1, v_x_2300_);
lean_ctor_set(v___x_2322_, 0, v_x_2299_);
v___x_2330_ = v___x_2322_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_x_2299_);
lean_ctor_set(v_reuseFailAlloc_2331_, 1, v_x_2300_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
v___y_2314_ = v___x_2330_;
goto v___jp_2313_;
}
}
}
}
case 1:
{
lean_object* v_node_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2345_; 
v_node_2333_ = lean_ctor_get(v_v_2310_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v_v_2310_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2335_ = v_v_2310_;
v_isShared_2336_ = v_isSharedCheck_2345_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_node_2333_);
lean_dec(v_v_2310_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2345_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
size_t v___x_2337_; size_t v___x_2338_; size_t v___x_2339_; size_t v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2343_; 
v___x_2337_ = ((size_t)5ULL);
v___x_2338_ = lean_usize_shift_right(v_x_2297_, v___x_2337_);
v___x_2339_ = ((size_t)1ULL);
v___x_2340_ = lean_usize_add(v_x_2298_, v___x_2339_);
v___x_2341_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_node_2333_, v___x_2338_, v___x_2340_, v_x_2299_, v_x_2300_);
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 0, v___x_2341_);
v___x_2343_ = v___x_2335_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2341_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
v___y_2314_ = v___x_2343_;
goto v___jp_2313_;
}
}
}
default: 
{
lean_object* v___x_2346_; 
v___x_2346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2346_, 0, v_x_2299_);
lean_ctor_set(v___x_2346_, 1, v_x_2300_);
v___y_2314_ = v___x_2346_;
goto v___jp_2313_;
}
}
v___jp_2313_:
{
lean_object* v___x_2315_; lean_object* v___x_2317_; 
v___x_2315_ = lean_array_fset(v_xs_x27_2312_, v_j_2304_, v___y_2314_);
lean_dec(v_j_2304_);
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 0, v___x_2315_);
v___x_2317_ = v___x_2308_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2315_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
}
else
{
lean_object* v_ks_2349_; lean_object* v_vs_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2368_; 
v_ks_2349_ = lean_ctor_get(v_x_2296_, 0);
v_vs_2350_ = lean_ctor_get(v_x_2296_, 1);
v_isSharedCheck_2368_ = !lean_is_exclusive(v_x_2296_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2352_ = v_x_2296_;
v_isShared_2353_ = v_isSharedCheck_2368_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_vs_2350_);
lean_inc(v_ks_2349_);
lean_dec(v_x_2296_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2368_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_ks_2349_);
lean_ctor_set(v_reuseFailAlloc_2367_, 1, v_vs_2350_);
v___x_2355_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
lean_object* v_newNode_2356_; size_t v___x_2357_; uint8_t v___x_2358_; 
v_newNode_2356_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v___x_2355_, v_x_2299_, v_x_2300_);
v___x_2357_ = ((size_t)7ULL);
v___x_2358_ = lean_usize_dec_le(v___x_2357_, v_x_2298_);
if (v___x_2358_ == 0)
{
lean_object* v___x_2359_; lean_object* v___x_2360_; uint8_t v___x_2361_; 
v___x_2359_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2356_);
v___x_2360_ = lean_unsigned_to_nat(4u);
v___x_2361_ = lean_nat_dec_lt(v___x_2359_, v___x_2360_);
lean_dec(v___x_2359_);
if (v___x_2361_ == 0)
{
lean_object* v_ks_2362_; lean_object* v_vs_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v_ks_2362_ = lean_ctor_get(v_newNode_2356_, 0);
lean_inc_ref(v_ks_2362_);
v_vs_2363_ = lean_ctor_get(v_newNode_2356_, 1);
lean_inc_ref(v_vs_2363_);
lean_dec_ref(v_newNode_2356_);
v___x_2364_ = lean_unsigned_to_nat(0u);
v___x_2365_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0);
v___x_2366_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_x_2298_, v_ks_2362_, v_vs_2363_, v___x_2364_, v___x_2365_);
lean_dec_ref(v_vs_2363_);
lean_dec_ref(v_ks_2362_);
return v___x_2366_;
}
else
{
return v_newNode_2356_;
}
}
else
{
return v_newNode_2356_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(size_t v_depth_2369_, lean_object* v_keys_2370_, lean_object* v_vals_2371_, lean_object* v_i_2372_, lean_object* v_entries_2373_){
_start:
{
lean_object* v___x_2374_; uint8_t v___x_2375_; 
v___x_2374_ = lean_array_get_size(v_keys_2370_);
v___x_2375_ = lean_nat_dec_lt(v_i_2372_, v___x_2374_);
if (v___x_2375_ == 0)
{
lean_dec(v_i_2372_);
return v_entries_2373_;
}
else
{
lean_object* v_k_2376_; lean_object* v_v_2377_; size_t v___x_2378_; size_t v___x_2379_; size_t v___x_2380_; uint64_t v___x_2381_; size_t v_h_2382_; size_t v___x_2383_; lean_object* v___x_2384_; size_t v___x_2385_; size_t v___x_2386_; size_t v___x_2387_; size_t v_h_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v_k_2376_ = lean_array_fget_borrowed(v_keys_2370_, v_i_2372_);
v_v_2377_ = lean_array_fget_borrowed(v_vals_2371_, v_i_2372_);
v___x_2378_ = lean_ptr_addr(v_k_2376_);
v___x_2379_ = ((size_t)3ULL);
v___x_2380_ = lean_usize_shift_right(v___x_2378_, v___x_2379_);
v___x_2381_ = lean_usize_to_uint64(v___x_2380_);
v_h_2382_ = lean_uint64_to_usize(v___x_2381_);
v___x_2383_ = ((size_t)5ULL);
v___x_2384_ = lean_unsigned_to_nat(1u);
v___x_2385_ = ((size_t)1ULL);
v___x_2386_ = lean_usize_sub(v_depth_2369_, v___x_2385_);
v___x_2387_ = lean_usize_mul(v___x_2383_, v___x_2386_);
v_h_2388_ = lean_usize_shift_right(v_h_2382_, v___x_2387_);
v___x_2389_ = lean_nat_add(v_i_2372_, v___x_2384_);
lean_dec(v_i_2372_);
lean_inc(v_v_2377_);
lean_inc(v_k_2376_);
v___x_2390_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_entries_2373_, v_h_2388_, v_depth_2369_, v_k_2376_, v_v_2377_);
v_i_2372_ = v___x_2389_;
v_entries_2373_ = v___x_2390_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2392_, lean_object* v_keys_2393_, lean_object* v_vals_2394_, lean_object* v_i_2395_, lean_object* v_entries_2396_){
_start:
{
size_t v_depth_boxed_2397_; lean_object* v_res_2398_; 
v_depth_boxed_2397_ = lean_unbox_usize(v_depth_2392_);
lean_dec(v_depth_2392_);
v_res_2398_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2397_, v_keys_2393_, v_vals_2394_, v_i_2395_, v_entries_2396_);
lean_dec_ref(v_vals_2394_);
lean_dec_ref(v_keys_2393_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___boxed(lean_object* v_x_2399_, lean_object* v_x_2400_, lean_object* v_x_2401_, lean_object* v_x_2402_, lean_object* v_x_2403_){
_start:
{
size_t v_x_6465__boxed_2404_; size_t v_x_6466__boxed_2405_; lean_object* v_res_2406_; 
v_x_6465__boxed_2404_ = lean_unbox_usize(v_x_2400_);
lean_dec(v_x_2400_);
v_x_6466__boxed_2405_ = lean_unbox_usize(v_x_2401_);
lean_dec(v_x_2401_);
v_res_2406_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2399_, v_x_6465__boxed_2404_, v_x_6466__boxed_2405_, v_x_2402_, v_x_2403_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(lean_object* v_x_2407_, lean_object* v_x_2408_, lean_object* v_x_2409_){
_start:
{
size_t v___x_2410_; size_t v___x_2411_; size_t v___x_2412_; uint64_t v___x_2413_; size_t v___x_2414_; size_t v___x_2415_; lean_object* v___x_2416_; 
v___x_2410_ = lean_ptr_addr(v_x_2408_);
v___x_2411_ = ((size_t)3ULL);
v___x_2412_ = lean_usize_shift_right(v___x_2410_, v___x_2411_);
v___x_2413_ = lean_usize_to_uint64(v___x_2412_);
v___x_2414_ = lean_uint64_to_usize(v___x_2413_);
v___x_2415_ = ((size_t)1ULL);
v___x_2416_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2407_, v___x_2414_, v___x_2415_, v_x_2408_, v_x_2409_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0(lean_object* v_e_2417_, lean_object* v_ringId_2418_, lean_object* v_s_2419_){
_start:
{
lean_object* v_rings_2420_; lean_object* v_exprToRingId_2421_; lean_object* v_semirings_2422_; lean_object* v_exprToSemiringId_2423_; lean_object* v_ncRings_2424_; lean_object* v_exprToNCRingId_2425_; lean_object* v_ncSemirings_2426_; lean_object* v_exprToNCSemiringId_2427_; lean_object* v_steps_2428_; uint8_t v_reportedMaxDegreeIssue_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2437_; 
v_rings_2420_ = lean_ctor_get(v_s_2419_, 0);
v_exprToRingId_2421_ = lean_ctor_get(v_s_2419_, 1);
v_semirings_2422_ = lean_ctor_get(v_s_2419_, 2);
v_exprToSemiringId_2423_ = lean_ctor_get(v_s_2419_, 3);
v_ncRings_2424_ = lean_ctor_get(v_s_2419_, 4);
v_exprToNCRingId_2425_ = lean_ctor_get(v_s_2419_, 5);
v_ncSemirings_2426_ = lean_ctor_get(v_s_2419_, 6);
v_exprToNCSemiringId_2427_ = lean_ctor_get(v_s_2419_, 7);
v_steps_2428_ = lean_ctor_get(v_s_2419_, 8);
v_reportedMaxDegreeIssue_2429_ = lean_ctor_get_uint8(v_s_2419_, sizeof(void*)*9);
v_isSharedCheck_2437_ = !lean_is_exclusive(v_s_2419_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2431_ = v_s_2419_;
v_isShared_2432_ = v_isSharedCheck_2437_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_steps_2428_);
lean_inc(v_exprToNCSemiringId_2427_);
lean_inc(v_ncSemirings_2426_);
lean_inc(v_exprToNCRingId_2425_);
lean_inc(v_ncRings_2424_);
lean_inc(v_exprToSemiringId_2423_);
lean_inc(v_semirings_2422_);
lean_inc(v_exprToRingId_2421_);
lean_inc(v_rings_2420_);
lean_dec(v_s_2419_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2437_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2433_; lean_object* v___x_2435_; 
v___x_2433_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_exprToRingId_2421_, v_e_2417_, v_ringId_2418_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 1, v___x_2433_);
v___x_2435_ = v___x_2431_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_rings_2420_);
lean_ctor_set(v_reuseFailAlloc_2436_, 1, v___x_2433_);
lean_ctor_set(v_reuseFailAlloc_2436_, 2, v_semirings_2422_);
lean_ctor_set(v_reuseFailAlloc_2436_, 3, v_exprToSemiringId_2423_);
lean_ctor_set(v_reuseFailAlloc_2436_, 4, v_ncRings_2424_);
lean_ctor_set(v_reuseFailAlloc_2436_, 5, v_exprToNCRingId_2425_);
lean_ctor_set(v_reuseFailAlloc_2436_, 6, v_ncSemirings_2426_);
lean_ctor_set(v_reuseFailAlloc_2436_, 7, v_exprToNCSemiringId_2427_);
lean_ctor_set(v_reuseFailAlloc_2436_, 8, v_steps_2428_);
lean_ctor_set_uint8(v_reuseFailAlloc_2436_, sizeof(void*)*9, v_reportedMaxDegreeIssue_2429_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1(void){
_start:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2439_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__0));
v___x_2440_ = l_Lean_stringToMessageData(v___x_2439_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(lean_object* v_e_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_){
_start:
{
lean_object* v_ringId_2454_; lean_object* v___f_2455_; lean_object* v___x_2456_; 
v_ringId_2454_ = lean_ctor_get(v_a_2442_, 0);
lean_inc(v_ringId_2454_);
lean_inc_ref(v_e_2441_);
v___f_2455_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2455_, 0, v_e_2441_);
lean_closure_set(v___f_2455_, 1, v_ringId_2454_);
v___x_2456_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_2441_, v_a_2443_, v_a_2448_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_a_2457_);
lean_dec_ref_known(v___x_2456_, 1);
if (lean_obj_tag(v_a_2457_) == 1)
{
lean_object* v_val_2458_; uint8_t v___x_2459_; 
lean_dec_ref(v___f_2455_);
v_val_2458_ = lean_ctor_get(v_a_2457_, 0);
lean_inc(v_val_2458_);
lean_dec_ref_known(v_a_2457_, 1);
v___x_2459_ = lean_nat_dec_eq(v_val_2458_, v_ringId_2454_);
lean_dec(v_val_2458_);
if (v___x_2459_ == 0)
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2460_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1);
v___x_2461_ = l_Lean_indentExpr(v_e_2441_);
v___x_2462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2460_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
v___x_2463_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2444_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; uint8_t v_verbose_2465_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc(v_a_2464_);
lean_dec_ref_known(v___x_2463_, 1);
v_verbose_2465_ = lean_ctor_get_uint8(v_a_2464_, 0);
lean_dec(v_a_2464_);
if (v_verbose_2465_ == 0)
{
lean_dec_ref_known(v___x_2462_, 2);
goto v___jp_2451_;
}
else
{
lean_object* v___x_2466_; 
v___x_2466_ = l_Lean_Meta_Sym_reportIssue(v___x_2462_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_dec_ref_known(v___x_2466_, 1);
goto v___jp_2451_;
}
else
{
return v___x_2466_;
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_dec_ref_known(v___x_2462_, 2);
v_a_2467_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2463_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2463_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
else
{
lean_dec_ref(v_e_2441_);
goto v___jp_2451_;
}
}
else
{
lean_object* v___x_2475_; lean_object* v___x_2476_; 
lean_dec(v_a_2457_);
lean_dec_ref(v_e_2441_);
v___x_2475_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2476_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2475_, v___f_2455_, v_a_2443_);
return v___x_2476_;
}
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_dec_ref(v___f_2455_);
lean_dec_ref(v_e_2441_);
v_a_2477_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2456_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2456_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
v___jp_2451_:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = lean_box(0);
v___x_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2452_);
return v___x_2453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___boxed(lean_object* v_e_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
lean_dec(v_a_2493_);
lean_dec_ref(v_a_2492_);
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
lean_dec(v_a_2487_);
lean_dec_ref(v_a_2486_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(lean_object* v_e_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_){
_start:
{
lean_object* v___x_2509_; 
v___x_2509_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2496_, v_a_2497_, v_a_2498_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___boxed(lean_object* v_e_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(v_e_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_);
lean_dec(v_a_2521_);
lean_dec_ref(v_a_2520_);
lean_dec(v_a_2519_);
lean_dec_ref(v_a_2518_);
lean_dec(v_a_2517_);
lean_dec_ref(v_a_2516_);
lean_dec(v_a_2515_);
lean_dec_ref(v_a_2514_);
lean_dec(v_a_2513_);
lean_dec(v_a_2512_);
lean_dec_ref(v_a_2511_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0(lean_object* v_00_u03b2_2524_, lean_object* v_x_2525_, lean_object* v_x_2526_, lean_object* v_x_2527_){
_start:
{
lean_object* v___x_2528_; 
v___x_2528_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_x_2525_, v_x_2526_, v_x_2527_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(lean_object* v_00_u03b2_2529_, lean_object* v_x_2530_, size_t v_x_2531_, size_t v_x_2532_, lean_object* v_x_2533_, lean_object* v_x_2534_){
_start:
{
lean_object* v___x_2535_; 
v___x_2535_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2530_, v_x_2531_, v_x_2532_, v_x_2533_, v_x_2534_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2536_, lean_object* v_x_2537_, lean_object* v_x_2538_, lean_object* v_x_2539_, lean_object* v_x_2540_, lean_object* v_x_2541_){
_start:
{
size_t v_x_6751__boxed_2542_; size_t v_x_6752__boxed_2543_; lean_object* v_res_2544_; 
v_x_6751__boxed_2542_ = lean_unbox_usize(v_x_2538_);
lean_dec(v_x_2538_);
v_x_6752__boxed_2543_ = lean_unbox_usize(v_x_2539_);
lean_dec(v_x_2539_);
v_res_2544_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(v_00_u03b2_2536_, v_x_2537_, v_x_6751__boxed_2542_, v_x_6752__boxed_2543_, v_x_2540_, v_x_2541_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2545_, lean_object* v_n_2546_, lean_object* v_k_2547_, lean_object* v_v_2548_){
_start:
{
lean_object* v___x_2549_; 
v___x_2549_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v_n_2546_, v_k_2547_, v_v_2548_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2550_, size_t v_depth_2551_, lean_object* v_keys_2552_, lean_object* v_vals_2553_, lean_object* v_heq_2554_, lean_object* v_i_2555_, lean_object* v_entries_2556_){
_start:
{
lean_object* v___x_2557_; 
v___x_2557_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_2551_, v_keys_2552_, v_vals_2553_, v_i_2555_, v_entries_2556_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2558_, lean_object* v_depth_2559_, lean_object* v_keys_2560_, lean_object* v_vals_2561_, lean_object* v_heq_2562_, lean_object* v_i_2563_, lean_object* v_entries_2564_){
_start:
{
size_t v_depth_boxed_2565_; lean_object* v_res_2566_; 
v_depth_boxed_2565_ = lean_unbox_usize(v_depth_2559_);
lean_dec(v_depth_2559_);
v_res_2566_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(v_00_u03b2_2558_, v_depth_boxed_2565_, v_keys_2560_, v_vals_2561_, v_heq_2562_, v_i_2563_, v_entries_2564_);
lean_dec_ref(v_vals_2561_);
lean_dec_ref(v_keys_2560_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2567_, lean_object* v_x_2568_, lean_object* v_x_2569_, lean_object* v_x_2570_, lean_object* v_x_2571_){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2568_, v_x_2569_, v_x_2570_, v_x_2571_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0(lean_object* v_e_2573_, lean_object* v___f_2574_, lean_object* v___f_2575_, lean_object* v_size_2576_, lean_object* v_s_2577_){
_start:
{
lean_object* v_vars_2578_; lean_object* v_varMap_2579_; lean_object* v_denote_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2589_; 
v_vars_2578_ = lean_ctor_get(v_s_2577_, 0);
v_varMap_2579_ = lean_ctor_get(v_s_2577_, 1);
v_denote_2580_ = lean_ctor_get(v_s_2577_, 2);
v_isSharedCheck_2589_ = !lean_is_exclusive(v_s_2577_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2582_ = v_s_2577_;
v_isShared_2583_ = v_isSharedCheck_2589_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_denote_2580_);
lean_inc(v_varMap_2579_);
lean_inc(v_vars_2578_);
lean_dec(v_s_2577_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2589_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2587_; 
lean_inc_ref(v_e_2573_);
v___x_2584_ = l_Lean_PersistentArray_push___redArg(v_vars_2578_, v_e_2573_);
v___x_2585_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2574_, v___f_2575_, v_varMap_2579_, v_e_2573_, v_size_2576_);
if (v_isShared_2583_ == 0)
{
lean_ctor_set(v___x_2582_, 1, v___x_2585_);
lean_ctor_set(v___x_2582_, 0, v___x_2584_);
v___x_2587_ = v___x_2582_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2584_);
lean_ctor_set(v_reuseFailAlloc_2588_, 1, v___x_2585_);
lean_ctor_set(v_reuseFailAlloc_2588_, 2, v_denote_2580_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1(lean_object* v_toPure_2590_, lean_object* v_size_2591_, lean_object* v_____r_2592_){
_start:
{
lean_object* v___x_2593_; 
v___x_2593_ = lean_apply_2(v_toPure_2590_, lean_box(0), v_size_2591_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2(lean_object* v_e_2594_, lean_object* v_inst_2595_, lean_object* v_toBind_2596_, lean_object* v___f_2597_, lean_object* v_____r_2598_){
_start:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2599_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2600_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SolverExtension_markTerm___boxed), 14, 3);
lean_closure_set(v___x_2600_, 0, lean_box(0));
lean_closure_set(v___x_2600_, 1, v___x_2599_);
lean_closure_set(v___x_2600_, 2, v_e_2594_);
v___x_2601_ = lean_apply_2(v_inst_2595_, lean_box(0), v___x_2600_);
v___x_2602_ = lean_apply_4(v_toBind_2596_, lean_box(0), lean_box(0), v___x_2601_, v___f_2597_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3(lean_object* v_inst_2603_, lean_object* v_e_2604_, lean_object* v_toBind_2605_, lean_object* v___f_2606_, lean_object* v_____r_2607_){
_start:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2608_ = lean_apply_1(v_inst_2603_, v_e_2604_);
v___x_2609_ = lean_apply_4(v_toBind_2605_, lean_box(0), lean_box(0), v___x_2608_, v___f_2606_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4(lean_object* v___f_2610_, lean_object* v___f_2611_, lean_object* v_e_2612_, lean_object* v_toPure_2613_, lean_object* v_inst_2614_, lean_object* v_toBind_2615_, lean_object* v_inst_2616_, lean_object* v_modifyRingState_2617_, lean_object* v_s_2618_){
_start:
{
lean_object* v_vars_2619_; lean_object* v_varMap_2620_; lean_object* v___x_2621_; 
v_vars_2619_ = lean_ctor_get(v_s_2618_, 0);
lean_inc_ref(v_vars_2619_);
v_varMap_2620_ = lean_ctor_get(v_s_2618_, 1);
lean_inc_ref(v_varMap_2620_);
lean_dec_ref(v_s_2618_);
lean_inc_ref(v_e_2612_);
lean_inc_ref(v___f_2611_);
lean_inc_ref(v___f_2610_);
v___x_2621_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2610_, v___f_2611_, v_varMap_2620_, v_e_2612_);
lean_dec_ref(v_varMap_2620_);
if (lean_obj_tag(v___x_2621_) == 1)
{
lean_object* v_val_2622_; lean_object* v___x_2623_; 
lean_dec_ref(v_vars_2619_);
lean_dec(v_modifyRingState_2617_);
lean_dec(v_inst_2616_);
lean_dec(v_toBind_2615_);
lean_dec(v_inst_2614_);
lean_dec_ref(v_e_2612_);
lean_dec_ref(v___f_2611_);
lean_dec_ref(v___f_2610_);
v_val_2622_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_val_2622_);
lean_dec_ref_known(v___x_2621_, 1);
v___x_2623_ = lean_apply_2(v_toPure_2613_, lean_box(0), v_val_2622_);
return v___x_2623_;
}
else
{
lean_object* v_size_2624_; lean_object* v___f_2625_; lean_object* v___f_2626_; lean_object* v___f_2627_; lean_object* v___f_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
lean_dec(v___x_2621_);
v_size_2624_ = lean_ctor_get(v_vars_2619_, 2);
lean_inc_n(v_size_2624_, 2);
lean_dec_ref(v_vars_2619_);
lean_inc_ref_n(v_e_2612_, 2);
v___f_2625_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2625_, 0, v_e_2612_);
lean_closure_set(v___f_2625_, 1, v___f_2610_);
lean_closure_set(v___f_2625_, 2, v___f_2611_);
lean_closure_set(v___f_2625_, 3, v_size_2624_);
v___f_2626_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2626_, 0, v_toPure_2613_);
lean_closure_set(v___f_2626_, 1, v_size_2624_);
lean_inc_n(v_toBind_2615_, 2);
v___f_2627_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2627_, 0, v_e_2612_);
lean_closure_set(v___f_2627_, 1, v_inst_2614_);
lean_closure_set(v___f_2627_, 2, v_toBind_2615_);
lean_closure_set(v___f_2627_, 3, v___f_2626_);
v___f_2628_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2628_, 0, v_inst_2616_);
lean_closure_set(v___f_2628_, 1, v_e_2612_);
lean_closure_set(v___f_2628_, 2, v_toBind_2615_);
lean_closure_set(v___f_2628_, 3, v___f_2627_);
v___x_2629_ = lean_apply_1(v_modifyRingState_2617_, v___f_2625_);
v___x_2630_ = lean_apply_4(v_toBind_2615_, lean_box(0), lean_box(0), v___x_2629_, v___f_2628_);
return v___x_2630_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(lean_object* v_inst_2633_, lean_object* v_inst_2634_, lean_object* v_inst_2635_, lean_object* v_inst_2636_, lean_object* v_e_2637_){
_start:
{
lean_object* v_toApplicative_2638_; lean_object* v_toBind_2639_; lean_object* v_getRingState_2640_; lean_object* v_modifyRingState_2641_; lean_object* v_toPure_2642_; lean_object* v___f_2643_; lean_object* v___f_2644_; lean_object* v___f_2645_; lean_object* v___x_2646_; 
v_toApplicative_2638_ = lean_ctor_get(v_inst_2634_, 0);
lean_inc_ref(v_toApplicative_2638_);
v_toBind_2639_ = lean_ctor_get(v_inst_2634_, 1);
lean_inc_n(v_toBind_2639_, 2);
lean_dec_ref(v_inst_2634_);
v_getRingState_2640_ = lean_ctor_get(v_inst_2635_, 0);
lean_inc(v_getRingState_2640_);
v_modifyRingState_2641_ = lean_ctor_get(v_inst_2635_, 1);
lean_inc(v_modifyRingState_2641_);
lean_dec_ref(v_inst_2635_);
v_toPure_2642_ = lean_ctor_get(v_toApplicative_2638_, 1);
lean_inc(v_toPure_2642_);
lean_dec_ref(v_toApplicative_2638_);
v___f_2643_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0));
v___f_2644_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1));
v___f_2645_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2645_, 0, v___f_2643_);
lean_closure_set(v___f_2645_, 1, v___f_2644_);
lean_closure_set(v___f_2645_, 2, v_e_2637_);
lean_closure_set(v___f_2645_, 3, v_toPure_2642_);
lean_closure_set(v___f_2645_, 4, v_inst_2633_);
lean_closure_set(v___f_2645_, 5, v_toBind_2639_);
lean_closure_set(v___f_2645_, 6, v_inst_2636_);
lean_closure_set(v___f_2645_, 7, v_modifyRingState_2641_);
v___x_2646_ = lean_apply_4(v_toBind_2639_, lean_box(0), lean_box(0), v_getRingState_2640_, v___f_2645_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore(lean_object* v_m_2647_, lean_object* v_inst_2648_, lean_object* v_inst_2649_, lean_object* v_inst_2650_, lean_object* v_inst_2651_, lean_object* v_e_2652_){
_start:
{
lean_object* v___x_2653_; 
v___x_2653_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v_inst_2648_, v_inst_2649_, v_inst_2650_, v_inst_2651_, v_e_2652_);
return v___x_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0(lean_object* v_e_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v___x_2667_; 
v___x_2667_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2654_, v___y_2655_, v___y_2656_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0___boxed(lean_object* v_e_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0(v_e_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
return v_res_2681_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2685_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___closed__0));
v___x_2686_ = l_Lean_stringToMessageData(v___x_2685_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0(lean_object* v___x_2687_, lean_object* v___x_2688_, lean_object* v___f_2689_, lean_object* v___x_2690_, lean_object* v___f_2691_, lean_object* v_e_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v___x_2705_; 
v___x_2705_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_2692_, v___y_2694_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_a_2706_; uint8_t v___x_2707_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2705_, 1);
v___x_2707_ = lean_unbox(v_a_2706_);
lean_dec(v_a_2706_);
if (v___x_2707_ == 0)
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_1454__overap_2711_; lean_object* v___x_2712_; 
v___x_2708_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___closed__1);
lean_inc_ref(v_e_2692_);
v___x_2709_ = l_Lean_indentExpr(v_e_2692_);
v___x_2710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2708_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
lean_inc_ref(v___x_2687_);
v___x_1454__overap_2711_ = l_Lean_throwError___redArg(v___x_2687_, v___x_2688_, v___x_2710_);
lean_inc(v___y_2703_);
lean_inc_ref(v___y_2702_);
lean_inc(v___y_2701_);
lean_inc_ref(v___y_2700_);
lean_inc(v___y_2699_);
lean_inc_ref(v___y_2698_);
lean_inc(v___y_2697_);
lean_inc_ref(v___y_2696_);
lean_inc(v___y_2695_);
lean_inc(v___y_2694_);
lean_inc_ref(v___y_2693_);
v___x_2712_ = lean_apply_12(v___x_1454__overap_2711_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, lean_box(0));
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_object* v___x_1457__overap_2713_; lean_object* v___x_2714_; 
lean_dec_ref_known(v___x_2712_, 1);
v___x_1457__overap_2713_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v___f_2689_, v___x_2687_, v___x_2690_, v___f_2691_, v_e_2692_);
lean_inc(v___y_2703_);
lean_inc_ref(v___y_2702_);
lean_inc(v___y_2701_);
lean_inc_ref(v___y_2700_);
lean_inc(v___y_2699_);
lean_inc_ref(v___y_2698_);
lean_inc(v___y_2697_);
lean_inc_ref(v___y_2696_);
lean_inc(v___y_2695_);
lean_inc(v___y_2694_);
lean_inc_ref(v___y_2693_);
v___x_2714_ = lean_apply_12(v___x_1457__overap_2713_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, lean_box(0));
return v___x_2714_;
}
else
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2722_; 
lean_dec_ref(v_e_2692_);
lean_dec_ref(v___f_2691_);
lean_dec_ref(v___x_2690_);
lean_dec(v___f_2689_);
lean_dec_ref(v___x_2687_);
v_a_2715_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2717_ = v___x_2712_;
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2712_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2720_; 
if (v_isShared_2718_ == 0)
{
v___x_2720_ = v___x_2717_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2715_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
}
else
{
lean_object* v___x_1461__overap_2723_; lean_object* v___x_2724_; 
lean_dec_ref(v___x_2688_);
v___x_1461__overap_2723_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v___f_2689_, v___x_2687_, v___x_2690_, v___f_2691_, v_e_2692_);
lean_inc(v___y_2703_);
lean_inc_ref(v___y_2702_);
lean_inc(v___y_2701_);
lean_inc_ref(v___y_2700_);
lean_inc(v___y_2699_);
lean_inc_ref(v___y_2698_);
lean_inc(v___y_2697_);
lean_inc_ref(v___y_2696_);
lean_inc(v___y_2695_);
lean_inc(v___y_2694_);
lean_inc_ref(v___y_2693_);
v___x_2724_ = lean_apply_12(v___x_1461__overap_2723_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, lean_box(0));
return v___x_2724_;
}
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
lean_dec_ref(v_e_2692_);
lean_dec_ref(v___f_2691_);
lean_dec_ref(v___x_2690_);
lean_dec(v___f_2689_);
lean_dec_ref(v___x_2688_);
lean_dec_ref(v___x_2687_);
v_a_2725_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2705_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2705_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___boxed(lean_object** _args){
lean_object* v___x_2733_ = _args[0];
lean_object* v___x_2734_ = _args[1];
lean_object* v___f_2735_ = _args[2];
lean_object* v___x_2736_ = _args[3];
lean_object* v___f_2737_ = _args[4];
lean_object* v_e_2738_ = _args[5];
lean_object* v___y_2739_ = _args[6];
lean_object* v___y_2740_ = _args[7];
lean_object* v___y_2741_ = _args[8];
lean_object* v___y_2742_ = _args[9];
lean_object* v___y_2743_ = _args[10];
lean_object* v___y_2744_ = _args[11];
lean_object* v___y_2745_ = _args[12];
lean_object* v___y_2746_ = _args[13];
lean_object* v___y_2747_ = _args[14];
lean_object* v___y_2748_ = _args[15];
lean_object* v___y_2749_ = _args[16];
lean_object* v___y_2750_ = _args[17];
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0(v___x_2733_, v___x_2734_, v___f_2735_, v___x_2736_, v___f_2737_, v_e_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
return v_res_2751_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__0(void){
_start:
{
lean_object* v___x_2752_; 
v___x_2752_ = l_instMonadEIO___redArg();
return v___x_2752_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__1(void){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2753_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__0);
v___x_2754_ = l_StateRefT_x27_instMonad___redArg(v___x_2753_);
return v___x_2754_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__7(void){
_start:
{
lean_object* v___x_2760_; lean_object* v___f_2761_; 
v___x_2760_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_2761_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2761_, 0, v___x_2760_);
return v___f_2761_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__8(void){
_start:
{
lean_object* v___x_2762_; lean_object* v___f_2763_; 
v___x_2762_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_2763_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2763_, 0, v___x_2762_);
return v___f_2763_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__9(void){
_start:
{
lean_object* v___f_2764_; lean_object* v___f_2765_; lean_object* v___x_2766_; 
v___f_2764_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__8, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__8_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__8);
v___f_2765_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__7, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__7_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__7);
v___x_2766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2766_, 0, v___f_2765_);
lean_ctor_set(v___x_2766_, 1, v___f_2764_);
return v___x_2766_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__10(void){
_start:
{
lean_object* v___x_2767_; lean_object* v___f_2768_; 
v___x_2767_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__9, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__9_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__9);
v___f_2768_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2768_, 0, v___x_2767_);
return v___f_2768_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__11(void){
_start:
{
lean_object* v___x_2769_; lean_object* v___f_2770_; 
v___x_2769_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__9, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__9_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__9);
v___f_2770_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2770_, 0, v___x_2769_);
return v___f_2770_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__12(void){
_start:
{
lean_object* v___f_2771_; lean_object* v___f_2772_; lean_object* v___x_2773_; 
v___f_2771_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__11, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__11_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__11);
v___f_2772_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__10, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__10_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__10);
v___x_2773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___f_2772_);
lean_ctor_set(v___x_2773_, 1, v___f_2771_);
return v___x_2773_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__13(void){
_start:
{
lean_object* v___x_2774_; lean_object* v___f_2775_; 
v___x_2774_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__12);
v___f_2775_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2775_, 0, v___x_2774_);
return v___f_2775_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__14(void){
_start:
{
lean_object* v___x_2776_; lean_object* v___f_2777_; 
v___x_2776_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__12);
v___f_2777_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2777_, 0, v___x_2776_);
return v___f_2777_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__15(void){
_start:
{
lean_object* v___f_2778_; lean_object* v___f_2779_; lean_object* v___x_2780_; 
v___f_2778_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__14, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__14_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__14);
v___f_2779_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__13, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__13_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__13);
v___x_2780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2780_, 0, v___f_2779_);
lean_ctor_set(v___x_2780_, 1, v___f_2778_);
return v___x_2780_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__16(void){
_start:
{
lean_object* v___x_2781_; lean_object* v___f_2782_; 
v___x_2781_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__15, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__15_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__15);
v___f_2782_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2782_, 0, v___x_2781_);
return v___f_2782_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__17(void){
_start:
{
lean_object* v___x_2783_; lean_object* v___f_2784_; 
v___x_2783_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__15, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__15_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__15);
v___f_2784_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2784_, 0, v___x_2783_);
return v___f_2784_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__18(void){
_start:
{
lean_object* v___f_2785_; lean_object* v___f_2786_; lean_object* v___x_2787_; 
v___f_2785_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__17, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__17_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__17);
v___f_2786_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__16, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__16_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__16);
v___x_2787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2787_, 0, v___f_2786_);
lean_ctor_set(v___x_2787_, 1, v___f_2785_);
return v___x_2787_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__19(void){
_start:
{
lean_object* v___x_2788_; lean_object* v___f_2789_; 
v___x_2788_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__18, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__18_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__18);
v___f_2789_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2789_, 0, v___x_2788_);
return v___f_2789_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__20(void){
_start:
{
lean_object* v___x_2790_; lean_object* v___f_2791_; 
v___x_2790_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__18, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__18_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__18);
v___f_2791_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2791_, 0, v___x_2790_);
return v___f_2791_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__21(void){
_start:
{
lean_object* v___f_2792_; lean_object* v___f_2793_; lean_object* v___x_2794_; 
v___f_2792_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__20, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__20_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__20);
v___f_2793_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__19, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__19_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__19);
v___x_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___f_2793_);
lean_ctor_set(v___x_2794_, 1, v___f_2792_);
return v___x_2794_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__22(void){
_start:
{
lean_object* v___x_2795_; lean_object* v___f_2796_; 
v___x_2795_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__21, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__21_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__21);
v___f_2796_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2796_, 0, v___x_2795_);
return v___f_2796_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__23(void){
_start:
{
lean_object* v___x_2797_; lean_object* v___f_2798_; 
v___x_2797_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__21, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__21_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__21);
v___f_2798_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2798_, 0, v___x_2797_);
return v___f_2798_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__24(void){
_start:
{
lean_object* v___f_2799_; lean_object* v___f_2800_; lean_object* v___x_2801_; 
v___f_2799_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__23, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__23_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__23);
v___f_2800_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__22, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__22_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__22);
v___x_2801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___f_2800_);
lean_ctor_set(v___x_2801_, 1, v___f_2799_);
return v___x_2801_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__25(void){
_start:
{
lean_object* v___x_2802_; lean_object* v___f_2803_; 
v___x_2802_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__24, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__24_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__24);
v___f_2803_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2803_, 0, v___x_2802_);
return v___f_2803_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__26(void){
_start:
{
lean_object* v___x_2804_; lean_object* v___f_2805_; 
v___x_2804_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__24, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__24_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__24);
v___f_2805_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2805_, 0, v___x_2804_);
return v___f_2805_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__27(void){
_start:
{
lean_object* v___f_2806_; lean_object* v___f_2807_; lean_object* v___x_2808_; 
v___f_2806_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__26, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__26_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__26);
v___f_2807_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__25, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__25_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__25);
v___x_2808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___f_2807_);
lean_ctor_set(v___x_2808_, 1, v___f_2806_);
return v___x_2808_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__28(void){
_start:
{
lean_object* v___x_2809_; lean_object* v___f_2810_; 
v___x_2809_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__27, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__27_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__27);
v___f_2810_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2810_, 0, v___x_2809_);
return v___f_2810_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__29(void){
_start:
{
lean_object* v___x_2811_; lean_object* v___f_2812_; 
v___x_2811_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__27, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__27_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__27);
v___f_2812_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2812_, 0, v___x_2811_);
return v___f_2812_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__30(void){
_start:
{
lean_object* v___f_2813_; lean_object* v___f_2814_; lean_object* v___x_2815_; 
v___f_2813_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__29, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__29_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__29);
v___f_2814_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__28, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__28_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__28);
v___x_2815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___f_2814_);
lean_ctor_set(v___x_2815_, 1, v___f_2813_);
return v___x_2815_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__31(void){
_start:
{
lean_object* v___x_2816_; lean_object* v___f_2817_; 
v___x_2816_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__30, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__30_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__30);
v___f_2817_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2817_, 0, v___x_2816_);
return v___f_2817_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__32(void){
_start:
{
lean_object* v___x_2818_; lean_object* v___f_2819_; 
v___x_2818_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__30, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__30_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__30);
v___f_2819_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2819_, 0, v___x_2818_);
return v___f_2819_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__33(void){
_start:
{
lean_object* v___f_2820_; lean_object* v___f_2821_; lean_object* v___x_2822_; 
v___f_2820_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__32, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__32_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__32);
v___f_2821_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__31, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__31_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__31);
v___x_2822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2822_, 0, v___f_2821_);
lean_ctor_set(v___x_2822_, 1, v___f_2820_);
return v___x_2822_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__37(void){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2826_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2827_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__36));
v___x_2828_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__35));
v___x_2829_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2828_, v___x_2827_, v___x_2826_);
return v___x_2829_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__38(void){
_start:
{
lean_object* v___x_2830_; lean_object* v___f_2831_; lean_object* v___f_2832_; lean_object* v___x_2833_; 
v___x_2830_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__37, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__37_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__37);
v___f_2831_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6));
v___f_2832_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__34));
v___x_2833_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2832_, v___f_2831_, v___x_2830_);
return v___x_2833_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__39(void){
_start:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2834_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__38, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__38_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__38);
v___x_2835_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__36));
v___x_2836_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__35));
v___x_2837_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2836_, v___x_2835_, v___x_2834_);
return v___x_2837_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__40(void){
_start:
{
lean_object* v___x_2838_; lean_object* v___f_2839_; lean_object* v___f_2840_; lean_object* v___x_2841_; 
v___x_2838_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__39, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__39_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__39);
v___f_2839_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6));
v___f_2840_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__34));
v___x_2841_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2840_, v___f_2839_, v___x_2838_);
return v___x_2841_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__41(void){
_start:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2842_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__40, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__40_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__40);
v___x_2843_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__36));
v___x_2844_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__35));
v___x_2845_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2844_, v___x_2843_, v___x_2842_);
return v___x_2845_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__42(void){
_start:
{
lean_object* v___x_2846_; lean_object* v___f_2847_; lean_object* v___f_2848_; lean_object* v___x_2849_; 
v___x_2846_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__41, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__41_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__41);
v___f_2847_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6));
v___f_2848_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__34));
v___x_2849_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2848_, v___f_2847_, v___x_2846_);
return v___x_2849_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__43(void){
_start:
{
lean_object* v___x_2850_; lean_object* v___f_2851_; lean_object* v___f_2852_; lean_object* v___x_2853_; 
v___x_2850_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__42, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__42_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__42);
v___f_2851_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6));
v___f_2852_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__34));
v___x_2853_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2852_, v___f_2851_, v___x_2850_);
return v___x_2853_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__44(void){
_start:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2854_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__43, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__43_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__43);
v___x_2855_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__36));
v___x_2856_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__35));
v___x_2857_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2856_, v___x_2855_, v___x_2854_);
return v___x_2857_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__45(void){
_start:
{
lean_object* v___x_2858_; lean_object* v___f_2859_; lean_object* v___f_2860_; lean_object* v___x_2861_; 
v___x_2858_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__44, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__44_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__44);
v___f_2859_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6));
v___f_2860_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__34));
v___x_2861_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2860_, v___f_2859_, v___x_2858_);
return v___x_2861_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__48(void){
_start:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___f_2868_; 
v___x_2866_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__36));
v___x_2867_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_2868_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2868_, 0, v___x_2867_);
lean_closure_set(v___f_2868_, 1, v___x_2866_);
return v___f_2868_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__49(void){
_start:
{
lean_object* v___f_2869_; lean_object* v___f_2870_; lean_object* v___f_2871_; 
v___f_2869_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6));
v___f_2870_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__48, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__48_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__48);
v___f_2871_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2871_, 0, v___f_2870_);
lean_closure_set(v___f_2871_, 1, v___f_2869_);
return v___f_2871_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__50(void){
_start:
{
lean_object* v___x_2872_; lean_object* v___f_2873_; lean_object* v___f_2874_; 
v___x_2872_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__36));
v___f_2873_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__49, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__49_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__49);
v___f_2874_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2874_, 0, v___f_2873_);
lean_closure_set(v___f_2874_, 1, v___x_2872_);
return v___f_2874_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__51(void){
_start:
{
lean_object* v___f_2875_; lean_object* v___f_2876_; lean_object* v___f_2877_; 
v___f_2875_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6));
v___f_2876_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__50, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__50_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__50);
v___f_2877_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2877_, 0, v___f_2876_);
lean_closure_set(v___f_2877_, 1, v___f_2875_);
return v___f_2877_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__52(void){
_start:
{
lean_object* v___f_2878_; lean_object* v___f_2879_; lean_object* v___f_2880_; 
v___f_2878_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6));
v___f_2879_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__51, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__51_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__51);
v___f_2880_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2880_, 0, v___f_2879_);
lean_closure_set(v___f_2880_, 1, v___f_2878_);
return v___f_2880_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__53(void){
_start:
{
lean_object* v___x_2881_; lean_object* v___f_2882_; lean_object* v___f_2883_; 
v___x_2881_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__36));
v___f_2882_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__52, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__52_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__52);
v___f_2883_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2883_, 0, v___f_2882_);
lean_closure_set(v___f_2883_, 1, v___x_2881_);
return v___f_2883_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__54(void){
_start:
{
lean_object* v___f_2884_; lean_object* v___f_2885_; lean_object* v___f_2886_; 
v___f_2884_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6));
v___f_2885_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__53, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__53_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__53);
v___f_2886_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2886_, 0, v___f_2885_);
lean_closure_set(v___f_2886_, 1, v___f_2884_);
return v___f_2886_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM(void){
_start:
{
lean_object* v___x_2887_; lean_object* v_toApplicative_2888_; lean_object* v_toFunctor_2889_; lean_object* v_toSeq_2890_; lean_object* v_toSeqLeft_2891_; lean_object* v_toSeqRight_2892_; lean_object* v___f_2893_; lean_object* v___f_2894_; lean_object* v___f_2895_; lean_object* v___f_2896_; lean_object* v___x_2897_; lean_object* v___f_2898_; lean_object* v___f_2899_; lean_object* v___f_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v_toApplicative_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2957_; 
v___x_2887_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__1);
v_toApplicative_2888_ = lean_ctor_get(v___x_2887_, 0);
v_toFunctor_2889_ = lean_ctor_get(v_toApplicative_2888_, 0);
v_toSeq_2890_ = lean_ctor_get(v_toApplicative_2888_, 2);
v_toSeqLeft_2891_ = lean_ctor_get(v_toApplicative_2888_, 3);
v_toSeqRight_2892_ = lean_ctor_get(v_toApplicative_2888_, 4);
v___f_2893_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__2));
v___f_2894_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__3));
lean_inc_ref_n(v_toFunctor_2889_, 2);
v___f_2895_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2895_, 0, v_toFunctor_2889_);
v___f_2896_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2896_, 0, v_toFunctor_2889_);
v___x_2897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2897_, 0, v___f_2895_);
lean_ctor_set(v___x_2897_, 1, v___f_2896_);
lean_inc(v_toSeqRight_2892_);
v___f_2898_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2898_, 0, v_toSeqRight_2892_);
lean_inc(v_toSeqLeft_2891_);
v___f_2899_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2899_, 0, v_toSeqLeft_2891_);
lean_inc(v_toSeq_2890_);
v___f_2900_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2900_, 0, v_toSeq_2890_);
v___x_2901_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2897_);
lean_ctor_set(v___x_2901_, 1, v___f_2893_);
lean_ctor_set(v___x_2901_, 2, v___f_2900_);
lean_ctor_set(v___x_2901_, 3, v___f_2899_);
lean_ctor_set(v___x_2901_, 4, v___f_2898_);
v___x_2902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2901_);
lean_ctor_set(v___x_2902_, 1, v___f_2894_);
v___x_2903_ = l_StateRefT_x27_instMonad___redArg(v___x_2902_);
v_toApplicative_2904_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2957_ == 0)
{
lean_object* v_unused_2958_; 
v_unused_2958_ = lean_ctor_get(v___x_2903_, 1);
lean_dec(v_unused_2958_);
v___x_2906_ = v___x_2903_;
v_isShared_2907_ = v_isSharedCheck_2957_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_toApplicative_2904_);
lean_dec(v___x_2903_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2957_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v_toFunctor_2908_; lean_object* v_toSeq_2909_; lean_object* v_toSeqLeft_2910_; lean_object* v_toSeqRight_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2955_; 
v_toFunctor_2908_ = lean_ctor_get(v_toApplicative_2904_, 0);
v_toSeq_2909_ = lean_ctor_get(v_toApplicative_2904_, 2);
v_toSeqLeft_2910_ = lean_ctor_get(v_toApplicative_2904_, 3);
v_toSeqRight_2911_ = lean_ctor_get(v_toApplicative_2904_, 4);
v_isSharedCheck_2955_ = !lean_is_exclusive(v_toApplicative_2904_);
if (v_isSharedCheck_2955_ == 0)
{
lean_object* v_unused_2956_; 
v_unused_2956_ = lean_ctor_get(v_toApplicative_2904_, 1);
lean_dec(v_unused_2956_);
v___x_2913_ = v_toApplicative_2904_;
v_isShared_2914_ = v_isSharedCheck_2955_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_toSeqRight_2911_);
lean_inc(v_toSeqLeft_2910_);
lean_inc(v_toSeq_2909_);
lean_inc(v_toFunctor_2908_);
lean_dec(v_toApplicative_2904_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2955_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___f_2915_; lean_object* v___f_2916_; lean_object* v___f_2917_; lean_object* v___f_2918_; lean_object* v___x_2919_; lean_object* v___f_2920_; lean_object* v___f_2921_; lean_object* v___f_2922_; lean_object* v___x_2924_; 
v___f_2915_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__4));
v___f_2916_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__5));
lean_inc_ref(v_toFunctor_2908_);
v___f_2917_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2917_, 0, v_toFunctor_2908_);
v___f_2918_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2918_, 0, v_toFunctor_2908_);
v___x_2919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2919_, 0, v___f_2917_);
lean_ctor_set(v___x_2919_, 1, v___f_2918_);
v___f_2920_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2920_, 0, v_toSeqRight_2911_);
v___f_2921_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2921_, 0, v_toSeqLeft_2910_);
v___f_2922_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2922_, 0, v_toSeq_2909_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 4, v___f_2920_);
lean_ctor_set(v___x_2913_, 3, v___f_2921_);
lean_ctor_set(v___x_2913_, 2, v___f_2922_);
lean_ctor_set(v___x_2913_, 1, v___f_2915_);
lean_ctor_set(v___x_2913_, 0, v___x_2919_);
v___x_2924_ = v___x_2913_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2919_);
lean_ctor_set(v_reuseFailAlloc_2954_, 1, v___f_2915_);
lean_ctor_set(v_reuseFailAlloc_2954_, 2, v___f_2922_);
lean_ctor_set(v_reuseFailAlloc_2954_, 3, v___f_2921_);
lean_ctor_set(v_reuseFailAlloc_2954_, 4, v___f_2920_);
v___x_2924_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
lean_object* v___x_2926_; 
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 1, v___f_2916_);
lean_ctor_set(v___x_2906_, 0, v___x_2924_);
v___x_2926_ = v___x_2906_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v___x_2924_);
lean_ctor_set(v_reuseFailAlloc_2953_, 1, v___f_2916_);
v___x_2926_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v_toApplicative_2935_; lean_object* v_toBind_2936_; lean_object* v_getCommRingState_2937_; lean_object* v_modifyCommRingState_2938_; lean_object* v_toPure_2939_; lean_object* v___f_2940_; lean_object* v___f_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v_toMonadRef_2946_; lean_object* v___f_2947_; lean_object* v___f_2948_; lean_object* v___f_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___f_2952_; 
v___x_2927_ = l_StateRefT_x27_instMonad___redArg(v___x_2926_);
v___x_2928_ = l_ReaderT_instMonad___redArg(v___x_2927_);
v___x_2929_ = l_StateRefT_x27_instMonad___redArg(v___x_2928_);
v___x_2930_ = l_ReaderT_instMonad___redArg(v___x_2929_);
v___x_2931_ = l_ReaderT_instMonad___redArg(v___x_2930_);
v___x_2932_ = l_StateRefT_x27_instMonad___redArg(v___x_2931_);
v___x_2933_ = l_ReaderT_instMonad___redArg(v___x_2932_);
v___x_2934_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM;
v_toApplicative_2935_ = lean_ctor_get(v___x_2933_, 0);
v_toBind_2936_ = lean_ctor_get(v___x_2933_, 1);
v_getCommRingState_2937_ = lean_ctor_get(v___x_2934_, 0);
v_modifyCommRingState_2938_ = lean_ctor_get(v___x_2934_, 1);
v_toPure_2939_ = lean_ctor_get(v_toApplicative_2935_, 1);
lean_inc(v_modifyCommRingState_2938_);
v___f_2940_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2940_, 0, v_modifyCommRingState_2938_);
lean_inc(v_toPure_2939_);
v___f_2941_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2941_, 0, v_toPure_2939_);
lean_inc(v_toBind_2936_);
lean_inc(v_getCommRingState_2937_);
v___x_2942_ = lean_apply_4(v_toBind_2936_, lean_box(0), lean_box(0), v_getCommRingState_2937_, v___f_2941_);
v___x_2943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2942_);
lean_ctor_set(v___x_2943_, 1, v___f_2940_);
v___x_2944_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__33, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__33_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__33);
v___x_2945_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__45, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__45_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__45);
v_toMonadRef_2946_ = lean_ctor_get(v___x_2945_, 0);
v___f_2947_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__47));
v___f_2948_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___closed__0));
v___f_2949_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__54, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__54_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__54);
lean_inc_ref(v___x_2933_);
v___x_2950_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_2949_, v___x_2933_);
lean_inc_ref(v_toMonadRef_2946_);
v___x_2951_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2944_);
lean_ctor_set(v___x_2951_, 1, v_toMonadRef_2946_);
lean_ctor_set(v___x_2951_, 2, v___x_2950_);
v___f_2952_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___boxed), 18, 5);
lean_closure_set(v___f_2952_, 0, v___x_2933_);
lean_closure_set(v___f_2952_, 1, v___x_2951_);
lean_closure_set(v___f_2952_, 2, v___f_2947_);
lean_closure_set(v___f_2952_, 3, v___x_2943_);
lean_closure_set(v___f_2952_, 4, v___f_2948_);
return v___f_2952_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0(void){
_start:
{
lean_object* v___x_2959_; lean_object* v_n_2960_; 
v___x_2959_ = lean_unsigned_to_nat(1u);
v_n_2960_ = l_Lean_mkRawNatLit(v___x_2959_);
return v_n_2960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(lean_object* v_u_2974_, lean_object* v_type_2975_, lean_object* v_semiringInst_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_){
_start:
{
lean_object* v_n_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v_ofNatInst_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v_n_2984_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0);
v___x_2985_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__5));
v___x_2986_ = lean_box(0);
v___x_2987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2987_, 0, v_u_2974_);
lean_ctor_set(v___x_2987_, 1, v___x_2986_);
lean_inc_ref(v___x_2987_);
v___x_2988_ = l_Lean_mkConst(v___x_2985_, v___x_2987_);
lean_inc_ref(v_type_2975_);
v_ofNatInst_2989_ = l_Lean_mkApp3(v___x_2988_, v_type_2975_, v_semiringInst_2976_, v_n_2984_);
v___x_2990_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__7));
v___x_2991_ = l_Lean_mkConst(v___x_2990_, v___x_2987_);
v___x_2992_ = l_Lean_mkApp3(v___x_2991_, v_type_2975_, v_n_2984_, v_ofNatInst_2989_);
v___x_2993_ = l_Lean_Meta_Sym_canon(v___x_2992_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v___x_2995_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_a_2994_);
lean_dec_ref_known(v___x_2993_, 1);
v___x_2995_ = l_Lean_Meta_Sym_shareCommon(v_a_2994_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_);
return v___x_2995_;
}
else
{
return v___x_2993_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___boxed(lean_object* v_u_2996_, lean_object* v_type_2997_, lean_object* v_semiringInst_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(v_u_2996_, v_type_2997_, v_semiringInst_2998_, v_a_2999_, v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
lean_dec(v_a_3000_);
lean_dec_ref(v_a_2999_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne(lean_object* v_u_3007_, lean_object* v_type_3008_, lean_object* v_semiringInst_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_){
_start:
{
lean_object* v___x_3022_; 
v___x_3022_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(v_u_3007_, v_type_3008_, v_semiringInst_3009_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___boxed(lean_object* v_u_3023_, lean_object* v_type_3024_, lean_object* v_semiringInst_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne(v_u_3023_, v_type_3024_, v_semiringInst_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_);
lean_dec(v_a_3036_);
lean_dec_ref(v_a_3035_);
lean_dec(v_a_3034_);
lean_dec_ref(v_a_3033_);
lean_dec(v_a_3032_);
lean_dec_ref(v_a_3031_);
lean_dec(v_a_3030_);
lean_dec_ref(v_a_3029_);
lean_dec(v_a_3028_);
lean_dec(v_a_3027_);
lean_dec_ref(v_a_3026_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___lam__0(lean_object* v_a_3039_, lean_object* v_s_3040_){
_start:
{
lean_object* v_toRing_3041_; lean_object* v_invFn_x3f_3042_; lean_object* v_divFn_x3f_3043_; lean_object* v_semiringId_x3f_3044_; lean_object* v_commSemiringInst_3045_; lean_object* v_commRingInst_3046_; lean_object* v_noZeroDivInst_x3f_3047_; lean_object* v_fieldInst_x3f_3048_; lean_object* v_powIdentityInst_x3f_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3080_; 
v_toRing_3041_ = lean_ctor_get(v_s_3040_, 0);
v_invFn_x3f_3042_ = lean_ctor_get(v_s_3040_, 1);
v_divFn_x3f_3043_ = lean_ctor_get(v_s_3040_, 2);
v_semiringId_x3f_3044_ = lean_ctor_get(v_s_3040_, 3);
v_commSemiringInst_3045_ = lean_ctor_get(v_s_3040_, 4);
v_commRingInst_3046_ = lean_ctor_get(v_s_3040_, 5);
v_noZeroDivInst_x3f_3047_ = lean_ctor_get(v_s_3040_, 6);
v_fieldInst_x3f_3048_ = lean_ctor_get(v_s_3040_, 7);
v_powIdentityInst_x3f_3049_ = lean_ctor_get(v_s_3040_, 8);
v_isSharedCheck_3080_ = !lean_is_exclusive(v_s_3040_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3051_ = v_s_3040_;
v_isShared_3052_ = v_isSharedCheck_3080_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_powIdentityInst_x3f_3049_);
lean_inc(v_fieldInst_x3f_3048_);
lean_inc(v_noZeroDivInst_x3f_3047_);
lean_inc(v_commRingInst_3046_);
lean_inc(v_commSemiringInst_3045_);
lean_inc(v_semiringId_x3f_3044_);
lean_inc(v_divFn_x3f_3043_);
lean_inc(v_invFn_x3f_3042_);
lean_inc(v_toRing_3041_);
lean_dec(v_s_3040_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3080_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v_id_3053_; lean_object* v_type_3054_; lean_object* v_u_3055_; lean_object* v_ringInst_3056_; lean_object* v_semiringInst_3057_; lean_object* v_charInst_x3f_3058_; lean_object* v_addFn_x3f_3059_; lean_object* v_mulFn_x3f_3060_; lean_object* v_subFn_x3f_3061_; lean_object* v_negFn_x3f_3062_; lean_object* v_powFn_x3f_3063_; lean_object* v_intCastFn_x3f_3064_; lean_object* v_natCastFn_x3f_3065_; lean_object* v_natSMulFn_x3f_3066_; lean_object* v_intSMulFn_x3f_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3078_; 
v_id_3053_ = lean_ctor_get(v_toRing_3041_, 0);
v_type_3054_ = lean_ctor_get(v_toRing_3041_, 1);
v_u_3055_ = lean_ctor_get(v_toRing_3041_, 2);
v_ringInst_3056_ = lean_ctor_get(v_toRing_3041_, 3);
v_semiringInst_3057_ = lean_ctor_get(v_toRing_3041_, 4);
v_charInst_x3f_3058_ = lean_ctor_get(v_toRing_3041_, 5);
v_addFn_x3f_3059_ = lean_ctor_get(v_toRing_3041_, 6);
v_mulFn_x3f_3060_ = lean_ctor_get(v_toRing_3041_, 7);
v_subFn_x3f_3061_ = lean_ctor_get(v_toRing_3041_, 8);
v_negFn_x3f_3062_ = lean_ctor_get(v_toRing_3041_, 9);
v_powFn_x3f_3063_ = lean_ctor_get(v_toRing_3041_, 10);
v_intCastFn_x3f_3064_ = lean_ctor_get(v_toRing_3041_, 11);
v_natCastFn_x3f_3065_ = lean_ctor_get(v_toRing_3041_, 12);
v_natSMulFn_x3f_3066_ = lean_ctor_get(v_toRing_3041_, 13);
v_intSMulFn_x3f_3067_ = lean_ctor_get(v_toRing_3041_, 14);
v_isSharedCheck_3078_ = !lean_is_exclusive(v_toRing_3041_);
if (v_isSharedCheck_3078_ == 0)
{
lean_object* v_unused_3079_; 
v_unused_3079_ = lean_ctor_get(v_toRing_3041_, 15);
lean_dec(v_unused_3079_);
v___x_3069_ = v_toRing_3041_;
v_isShared_3070_ = v_isSharedCheck_3078_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_intSMulFn_x3f_3067_);
lean_inc(v_natSMulFn_x3f_3066_);
lean_inc(v_natCastFn_x3f_3065_);
lean_inc(v_intCastFn_x3f_3064_);
lean_inc(v_powFn_x3f_3063_);
lean_inc(v_negFn_x3f_3062_);
lean_inc(v_subFn_x3f_3061_);
lean_inc(v_mulFn_x3f_3060_);
lean_inc(v_addFn_x3f_3059_);
lean_inc(v_charInst_x3f_3058_);
lean_inc(v_semiringInst_3057_);
lean_inc(v_ringInst_3056_);
lean_inc(v_u_3055_);
lean_inc(v_type_3054_);
lean_inc(v_id_3053_);
lean_dec(v_toRing_3041_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3078_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3071_; lean_object* v___x_3073_; 
v___x_3071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3071_, 0, v_a_3039_);
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 15, v___x_3071_);
v___x_3073_ = v___x_3069_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_id_3053_);
lean_ctor_set(v_reuseFailAlloc_3077_, 1, v_type_3054_);
lean_ctor_set(v_reuseFailAlloc_3077_, 2, v_u_3055_);
lean_ctor_set(v_reuseFailAlloc_3077_, 3, v_ringInst_3056_);
lean_ctor_set(v_reuseFailAlloc_3077_, 4, v_semiringInst_3057_);
lean_ctor_set(v_reuseFailAlloc_3077_, 5, v_charInst_x3f_3058_);
lean_ctor_set(v_reuseFailAlloc_3077_, 6, v_addFn_x3f_3059_);
lean_ctor_set(v_reuseFailAlloc_3077_, 7, v_mulFn_x3f_3060_);
lean_ctor_set(v_reuseFailAlloc_3077_, 8, v_subFn_x3f_3061_);
lean_ctor_set(v_reuseFailAlloc_3077_, 9, v_negFn_x3f_3062_);
lean_ctor_set(v_reuseFailAlloc_3077_, 10, v_powFn_x3f_3063_);
lean_ctor_set(v_reuseFailAlloc_3077_, 11, v_intCastFn_x3f_3064_);
lean_ctor_set(v_reuseFailAlloc_3077_, 12, v_natCastFn_x3f_3065_);
lean_ctor_set(v_reuseFailAlloc_3077_, 13, v_natSMulFn_x3f_3066_);
lean_ctor_set(v_reuseFailAlloc_3077_, 14, v_intSMulFn_x3f_3067_);
lean_ctor_set(v_reuseFailAlloc_3077_, 15, v___x_3071_);
v___x_3073_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
lean_object* v___x_3075_; 
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 0, v___x_3073_);
v___x_3075_ = v___x_3051_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3073_);
lean_ctor_set(v_reuseFailAlloc_3076_, 1, v_invFn_x3f_3042_);
lean_ctor_set(v_reuseFailAlloc_3076_, 2, v_divFn_x3f_3043_);
lean_ctor_set(v_reuseFailAlloc_3076_, 3, v_semiringId_x3f_3044_);
lean_ctor_set(v_reuseFailAlloc_3076_, 4, v_commSemiringInst_3045_);
lean_ctor_set(v_reuseFailAlloc_3076_, 5, v_commRingInst_3046_);
lean_ctor_set(v_reuseFailAlloc_3076_, 6, v_noZeroDivInst_x3f_3047_);
lean_ctor_set(v_reuseFailAlloc_3076_, 7, v_fieldInst_x3f_3048_);
lean_ctor_set(v_reuseFailAlloc_3076_, 8, v_powIdentityInst_x3f_3049_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3081_, lean_object* v_i_3082_, lean_object* v_k_3083_){
_start:
{
lean_object* v___x_3084_; uint8_t v___x_3085_; 
v___x_3084_ = lean_array_get_size(v_keys_3081_);
v___x_3085_ = lean_nat_dec_lt(v_i_3082_, v___x_3084_);
if (v___x_3085_ == 0)
{
lean_dec(v_i_3082_);
return v___x_3085_;
}
else
{
lean_object* v_k_x27_3086_; size_t v___x_3087_; size_t v___x_3088_; uint8_t v___x_3089_; 
v_k_x27_3086_ = lean_array_fget_borrowed(v_keys_3081_, v_i_3082_);
v___x_3087_ = lean_ptr_addr(v_k_3083_);
v___x_3088_ = lean_ptr_addr(v_k_x27_3086_);
v___x_3089_ = lean_usize_dec_eq(v___x_3087_, v___x_3088_);
if (v___x_3089_ == 0)
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3090_ = lean_unsigned_to_nat(1u);
v___x_3091_ = lean_nat_add(v_i_3082_, v___x_3090_);
lean_dec(v_i_3082_);
v_i_3082_ = v___x_3091_;
goto _start;
}
else
{
lean_dec(v_i_3082_);
return v___x_3085_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3093_, lean_object* v_i_3094_, lean_object* v_k_3095_){
_start:
{
uint8_t v_res_3096_; lean_object* v_r_3097_; 
v_res_3096_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg(v_keys_3093_, v_i_3094_, v_k_3095_);
lean_dec_ref(v_k_3095_);
lean_dec_ref(v_keys_3093_);
v_r_3097_ = lean_box(v_res_3096_);
return v_r_3097_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg(lean_object* v_x_3098_, size_t v_x_3099_, lean_object* v_x_3100_){
_start:
{
if (lean_obj_tag(v_x_3098_) == 0)
{
lean_object* v_es_3101_; lean_object* v___x_3102_; size_t v___x_3103_; size_t v___x_3104_; lean_object* v_j_3105_; lean_object* v___x_3106_; 
v_es_3101_ = lean_ctor_get(v_x_3098_, 0);
v___x_3102_ = lean_box(2);
v___x_3103_ = ((size_t)31ULL);
v___x_3104_ = lean_usize_land(v_x_3099_, v___x_3103_);
v_j_3105_ = lean_usize_to_nat(v___x_3104_);
v___x_3106_ = lean_array_get_borrowed(v___x_3102_, v_es_3101_, v_j_3105_);
lean_dec(v_j_3105_);
switch(lean_obj_tag(v___x_3106_))
{
case 0:
{
lean_object* v_key_3107_; size_t v___x_3108_; size_t v___x_3109_; uint8_t v___x_3110_; 
v_key_3107_ = lean_ctor_get(v___x_3106_, 0);
v___x_3108_ = lean_ptr_addr(v_x_3100_);
v___x_3109_ = lean_ptr_addr(v_key_3107_);
v___x_3110_ = lean_usize_dec_eq(v___x_3108_, v___x_3109_);
return v___x_3110_;
}
case 1:
{
lean_object* v_node_3111_; size_t v___x_3112_; size_t v___x_3113_; 
v_node_3111_ = lean_ctor_get(v___x_3106_, 0);
v___x_3112_ = ((size_t)5ULL);
v___x_3113_ = lean_usize_shift_right(v_x_3099_, v___x_3112_);
v_x_3098_ = v_node_3111_;
v_x_3099_ = v___x_3113_;
goto _start;
}
default: 
{
uint8_t v___x_3115_; 
v___x_3115_ = 0;
return v___x_3115_;
}
}
}
else
{
lean_object* v_ks_3116_; lean_object* v___x_3117_; uint8_t v___x_3118_; 
v_ks_3116_ = lean_ctor_get(v_x_3098_, 0);
v___x_3117_ = lean_unsigned_to_nat(0u);
v___x_3118_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg(v_ks_3116_, v___x_3117_, v_x_3100_);
return v___x_3118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg___boxed(lean_object* v_x_3119_, lean_object* v_x_3120_, lean_object* v_x_3121_){
_start:
{
size_t v_x_9654__boxed_3122_; uint8_t v_res_3123_; lean_object* v_r_3124_; 
v_x_9654__boxed_3122_ = lean_unbox_usize(v_x_3120_);
lean_dec(v_x_3120_);
v_res_3123_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg(v_x_3119_, v_x_9654__boxed_3122_, v_x_3121_);
lean_dec_ref(v_x_3121_);
lean_dec_ref(v_x_3119_);
v_r_3124_ = lean_box(v_res_3123_);
return v_r_3124_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg(lean_object* v_x_3125_, lean_object* v_x_3126_){
_start:
{
size_t v___x_3127_; size_t v___x_3128_; size_t v___x_3129_; uint64_t v___x_3130_; size_t v___x_3131_; uint8_t v___x_3132_; 
v___x_3127_ = lean_ptr_addr(v_x_3126_);
v___x_3128_ = ((size_t)3ULL);
v___x_3129_ = lean_usize_shift_right(v___x_3127_, v___x_3128_);
v___x_3130_ = lean_usize_to_uint64(v___x_3129_);
v___x_3131_ = lean_uint64_to_usize(v___x_3130_);
v___x_3132_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg(v_x_3125_, v___x_3131_, v_x_3126_);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg___boxed(lean_object* v_x_3133_, lean_object* v_x_3134_){
_start:
{
uint8_t v_res_3135_; lean_object* v_r_3136_; 
v_res_3135_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg(v_x_3133_, v_x_3134_);
lean_dec_ref(v_x_3134_);
lean_dec_ref(v_x_3133_);
v_r_3136_ = lean_box(v_res_3135_);
return v_r_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne(lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_){
_start:
{
lean_object* v_one_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___x_3201_; 
v___x_3201_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_3137_, v_a_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_);
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_object* v_a_3202_; lean_object* v_toRing_3203_; lean_object* v_one_x3f_3204_; 
v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
lean_inc(v_a_3202_);
lean_dec_ref_known(v___x_3201_, 1);
v_toRing_3203_ = lean_ctor_get(v_a_3202_, 0);
lean_inc_ref(v_toRing_3203_);
lean_dec(v_a_3202_);
v_one_x3f_3204_ = lean_ctor_get(v_toRing_3203_, 15);
if (lean_obj_tag(v_one_x3f_3204_) == 1)
{
lean_object* v_val_3205_; 
lean_inc_ref(v_one_x3f_3204_);
lean_dec_ref(v_toRing_3203_);
v_val_3205_ = lean_ctor_get(v_one_x3f_3204_, 0);
lean_inc(v_val_3205_);
lean_dec_ref_known(v_one_x3f_3204_, 1);
v_one_3150_ = v_val_3205_;
v___y_3151_ = v_a_3137_;
v___y_3152_ = v_a_3138_;
v___y_3153_ = v_a_3139_;
v___y_3154_ = v_a_3140_;
v___y_3155_ = v_a_3141_;
v___y_3156_ = v_a_3142_;
v___y_3157_ = v_a_3143_;
v___y_3158_ = v_a_3144_;
v___y_3159_ = v_a_3145_;
v___y_3160_ = v_a_3146_;
v___y_3161_ = v_a_3147_;
goto v___jp_3149_;
}
else
{
lean_object* v_type_3206_; lean_object* v_u_3207_; lean_object* v_semiringInst_3208_; lean_object* v___x_3209_; 
v_type_3206_ = lean_ctor_get(v_toRing_3203_, 1);
lean_inc_ref(v_type_3206_);
v_u_3207_ = lean_ctor_get(v_toRing_3203_, 2);
lean_inc(v_u_3207_);
v_semiringInst_3208_ = lean_ctor_get(v_toRing_3203_, 4);
lean_inc_ref(v_semiringInst_3208_);
lean_dec_ref(v_toRing_3203_);
v___x_3209_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(v_u_3207_, v_type_3206_, v_semiringInst_3208_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v_a_3210_; lean_object* v___f_3211_; lean_object* v___x_3212_; 
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
lean_inc_n(v_a_3210_, 2);
lean_dec_ref_known(v___x_3209_, 1);
v___f_3211_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getOne___lam__0), 2, 1);
lean_closure_set(v___f_3211_, 0, v_a_3210_);
v___x_3212_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_3211_, v_a_3137_, v_a_3143_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_dec_ref_known(v___x_3212_, 1);
v_one_3150_ = v_a_3210_;
v___y_3151_ = v_a_3137_;
v___y_3152_ = v_a_3138_;
v___y_3153_ = v_a_3139_;
v___y_3154_ = v_a_3140_;
v___y_3155_ = v_a_3141_;
v___y_3156_ = v_a_3142_;
v___y_3157_ = v_a_3143_;
v___y_3158_ = v_a_3144_;
v___y_3159_ = v_a_3145_;
v___y_3160_ = v_a_3146_;
v___y_3161_ = v_a_3147_;
goto v___jp_3149_;
}
else
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
lean_dec(v_a_3210_);
v_a_3213_ = lean_ctor_get(v___x_3212_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3215_ = v___x_3212_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3212_);
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
return v___x_3209_;
}
}
}
else
{
lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3228_; 
v_a_3221_ = lean_ctor_get(v___x_3201_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3223_ = v___x_3201_;
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v___x_3201_);
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
v___jp_3149_:
{
lean_object* v___x_3162_; 
v___x_3162_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v___y_3151_, v___y_3152_, v___y_3160_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3192_; 
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3165_ = v___x_3162_;
v_isShared_3166_ = v_isSharedCheck_3192_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___x_3162_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3192_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v_toRingState_3167_; lean_object* v_denote_3168_; uint8_t v___x_3169_; 
v_toRingState_3167_ = lean_ctor_get(v_a_3163_, 0);
lean_inc_ref(v_toRingState_3167_);
lean_dec(v_a_3163_);
v_denote_3168_ = lean_ctor_get(v_toRingState_3167_, 2);
lean_inc_ref(v_denote_3168_);
lean_dec_ref(v_toRingState_3167_);
v___x_3169_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg(v_denote_3168_, v_one_3150_);
lean_dec_ref(v_denote_3168_);
if (v___x_3169_ == 0)
{
lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
lean_del_object(v___x_3165_);
v___x_3170_ = lean_unsigned_to_nat(0u);
v___x_3171_ = lean_box(0);
lean_inc(v___y_3161_);
lean_inc_ref(v___y_3160_);
lean_inc(v___y_3159_);
lean_inc_ref(v___y_3158_);
lean_inc(v___y_3157_);
lean_inc_ref(v___y_3156_);
lean_inc(v___y_3155_);
lean_inc_ref(v___y_3154_);
lean_inc(v___y_3153_);
lean_inc(v___y_3152_);
lean_inc_ref(v_one_3150_);
v___x_3172_ = lean_grind_internalize(v_one_3150_, v___x_3170_, v___x_3171_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3179_; 
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3179_ == 0)
{
lean_object* v_unused_3180_; 
v_unused_3180_ = lean_ctor_get(v___x_3172_, 0);
lean_dec(v_unused_3180_);
v___x_3174_ = v___x_3172_;
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
else
{
lean_dec(v___x_3172_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3177_; 
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 0, v_one_3150_);
v___x_3177_ = v___x_3174_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_one_3150_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
else
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
lean_dec_ref(v_one_3150_);
v_a_3181_ = lean_ctor_get(v___x_3172_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___x_3172_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3172_);
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
lean_object* v___x_3190_; 
if (v_isShared_3166_ == 0)
{
lean_ctor_set(v___x_3165_, 0, v_one_3150_);
v___x_3190_ = v___x_3165_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_one_3150_);
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
lean_dec_ref(v_one_3150_);
v_a_3193_ = lean_ctor_get(v___x_3162_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3195_ = v___x_3162_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3162_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___boxed(lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_){
_start:
{
lean_object* v_res_3241_; 
v_res_3241_ = l_Lean_Meta_Grind_Arith_CommRing_getOne(v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_);
lean_dec(v_a_3239_);
lean_dec_ref(v_a_3238_);
lean_dec(v_a_3237_);
lean_dec_ref(v_a_3236_);
lean_dec(v_a_3235_);
lean_dec_ref(v_a_3234_);
lean_dec(v_a_3233_);
lean_dec_ref(v_a_3232_);
lean_dec(v_a_3231_);
lean_dec(v_a_3230_);
lean_dec_ref(v_a_3229_);
return v_res_3241_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0(lean_object* v_00_u03b2_3242_, lean_object* v_x_3243_, lean_object* v_x_3244_){
_start:
{
uint8_t v___x_3245_; 
v___x_3245_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg(v_x_3243_, v_x_3244_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___boxed(lean_object* v_00_u03b2_3246_, lean_object* v_x_3247_, lean_object* v_x_3248_){
_start:
{
uint8_t v_res_3249_; lean_object* v_r_3250_; 
v_res_3249_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0(v_00_u03b2_3246_, v_x_3247_, v_x_3248_);
lean_dec_ref(v_x_3248_);
lean_dec_ref(v_x_3247_);
v_r_3250_ = lean_box(v_res_3249_);
return v_r_3250_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0(lean_object* v_00_u03b2_3251_, lean_object* v_x_3252_, size_t v_x_3253_, lean_object* v_x_3254_){
_start:
{
uint8_t v___x_3255_; 
v___x_3255_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg(v_x_3252_, v_x_3253_, v_x_3254_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3256_, lean_object* v_x_3257_, lean_object* v_x_3258_, lean_object* v_x_3259_){
_start:
{
size_t v_x_9875__boxed_3260_; uint8_t v_res_3261_; lean_object* v_r_3262_; 
v_x_9875__boxed_3260_ = lean_unbox_usize(v_x_3258_);
lean_dec(v_x_3258_);
v_res_3261_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0(v_00_u03b2_3256_, v_x_3257_, v_x_9875__boxed_3260_, v_x_3259_);
lean_dec_ref(v_x_3259_);
lean_dec_ref(v_x_3257_);
v_r_3262_ = lean_box(v_res_3261_);
return v_r_3262_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3263_, lean_object* v_keys_3264_, lean_object* v_vals_3265_, lean_object* v_heq_3266_, lean_object* v_i_3267_, lean_object* v_k_3268_){
_start:
{
uint8_t v___x_3269_; 
v___x_3269_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg(v_keys_3264_, v_i_3267_, v_k_3268_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3270_, lean_object* v_keys_3271_, lean_object* v_vals_3272_, lean_object* v_heq_3273_, lean_object* v_i_3274_, lean_object* v_k_3275_){
_start:
{
uint8_t v_res_3276_; lean_object* v_r_3277_; 
v_res_3276_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1(v_00_u03b2_3270_, v_keys_3271_, v_vals_3272_, v_heq_3273_, v_i_3274_, v_k_3275_);
lean_dec_ref(v_k_3275_);
lean_dec_ref(v_vals_3272_);
lean_dec_ref(v_keys_3271_);
v_r_3277_ = lean_box(v_res_3276_);
return v_r_3277_;
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
