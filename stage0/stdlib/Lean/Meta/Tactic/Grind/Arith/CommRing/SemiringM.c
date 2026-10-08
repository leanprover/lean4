// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.SemiringM
// Imports: public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr
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
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default;
lean_object* l_Array_rightpad___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getArithState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkType;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Sym_Arith_arithExt;
lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getSemiring(lean_object*, lean_object*);
lean_object* l_instMonadLiftT___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiringId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__1_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "`grind` internal error, invalid semiringId"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "`grind` internal error, invalid ringId"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "expression in two different semirings"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "`grind` internal error, semiring term has not been internalized"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0___boxed(lean_object**);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__1;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__3_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__4_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__5_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__7;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__8;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__9;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__10;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__11;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__12;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__13;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__14;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__15;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__16;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__17;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__18;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__19;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__20;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__21;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__22;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__23;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__24;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__25;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__26;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__27;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__28;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__29;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__30;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__31;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__32;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__33;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__34 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__34_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__35 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__35_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__36 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__36_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__37;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__38;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__39;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__40;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__41;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__42;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__43;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__44;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__45;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__46 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__46_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__46_value),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6_value)} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__47 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__47_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__48;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__49;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__50;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__51;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__52;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__53;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__54;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM;
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__2_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "OfSemiring"};
static const lean_object* l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "toQ"};
static const lean_object* l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 53, 64, 113, 205, 30, 141, 114)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(232, 146, 236, 221, 122, 127, 105, 70)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "failed to find instance"};
static const lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNeg"};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(100, 233, 103, 154, 53, 22, 86, 139)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4;
static const lean_string_object l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__6_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 49, 23, 61, 125, 46, 165, 129)}};
static const lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___lam__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__2;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "npow"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__3_value),LEAN_SCALAR_PTR_LITERAL(227, 91, 39, 101, 227, 157, 49, 255)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__5_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHAdd"};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(229, 81, 239, 34, 203, 244, 36, 133)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toAdd"};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 205, 186, 60, 7, 38, 135, 75)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__5_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__6_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMul"};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 107, 107, 59, 202, 230, 169, 251)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toMul"};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(232, 23, 103, 115, 5, 120, 143, 98)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__4_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__5_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__4_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__6_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Lean.Meta.Tactic.Grind.Arith.CommRing.SemiringM"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 104, .m_capacity = 104, .m_length = 103, .m_data = "_private.Lean.Meta.Tactic.Grind.Arith.CommRing.SemiringM.0.Lean.Grind.CommRing.Expr.denoteAsRingExpr.go"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___redArg(lean_object* v_semiringId_1_, lean_object* v_x_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_14_; 
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
lean_inc(v_a_10_);
lean_inc_ref(v_a_9_);
lean_inc(v_a_8_);
lean_inc_ref(v_a_7_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
lean_inc(v_a_3_);
v___x_14_ = lean_apply_12(v_x_2_, v_semiringId_1_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, lean_box(0));
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___redArg___boxed(lean_object* v_semiringId_15_, lean_object* v_x_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___redArg(v_semiringId_15_, v_x_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_);
lean_dec(v_a_26_);
lean_dec_ref(v_a_25_);
lean_dec(v_a_24_);
lean_dec_ref(v_a_23_);
lean_dec(v_a_22_);
lean_dec_ref(v_a_21_);
lean_dec(v_a_20_);
lean_dec_ref(v_a_19_);
lean_dec(v_a_18_);
lean_dec(v_a_17_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run(lean_object* v_00_u03b1_29_, lean_object* v_semiringId_30_, lean_object* v_x_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v___x_43_; 
lean_inc(v_a_41_);
lean_inc_ref(v_a_40_);
lean_inc(v_a_39_);
lean_inc_ref(v_a_38_);
lean_inc(v_a_37_);
lean_inc_ref(v_a_36_);
lean_inc(v_a_35_);
lean_inc_ref(v_a_34_);
lean_inc(v_a_33_);
lean_inc(v_a_32_);
v___x_43_ = lean_apply_12(v_x_31_, v_semiringId_30_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, lean_box(0));
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___boxed(lean_object* v_00_u03b1_44_, lean_object* v_semiringId_45_, lean_object* v_x_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run(v_00_u03b1_44_, v_semiringId_45_, v_x_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
lean_dec(v_a_54_);
lean_dec_ref(v_a_53_);
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
lean_dec(v_a_48_);
lean_dec(v_a_47_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___redArg(lean_object* v_a_59_){
_start:
{
lean_object* v___x_61_; 
lean_inc(v_a_59_);
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v_a_59_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___redArg___boxed(lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___redArg(v_a_62_);
lean_dec(v_a_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiringId(lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_77_; 
lean_inc(v_a_65_);
v___x_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_77_, 0, v_a_65_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___boxed(lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Meta_Grind_Arith_CommRing_getSemiringId(v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
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
lean_dec(v_a_78_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0(lean_object* v_e_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_Meta_Sym_canon(v_e_91_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; lean_object* v___x_106_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_a_105_);
lean_dec_ref_known(v___x_104_, 1);
v___x_106_ = l_Lean_Meta_Sym_shareCommon(v_a_105_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
return v___x_106_;
}
else
{
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0___boxed(lean_object* v_e_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0(v_e_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_110_);
lean_dec(v___y_109_);
lean_dec(v___y_108_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1(lean_object* v_e_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_e_121_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1___boxed(lean_object* v_e_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1(v_e_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec(v___y_137_);
lean_dec(v___y_136_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0(lean_object* v_msgData_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v___x_161_; lean_object* v_env_162_; uint8_t v___x_163_; lean_object* v_env_164_; lean_object* v___x_165_; lean_object* v_toCold_166_; lean_object* v_mctx_167_; lean_object* v_lctx_168_; lean_object* v_options_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_161_ = lean_st_ref_get(v___y_159_);
v_env_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc_ref(v_env_162_);
lean_dec(v___x_161_);
v___x_163_ = 0;
v_env_164_ = l_Lean_Environment_setRecordingDeps(v_env_162_, v___x_163_);
v___x_165_ = lean_st_ref_get(v___y_157_);
v_toCold_166_ = lean_ctor_get(v___y_158_, 0);
v_mctx_167_ = lean_ctor_get(v___x_165_, 0);
lean_inc_ref(v_mctx_167_);
lean_dec(v___x_165_);
v_lctx_168_ = lean_ctor_get(v___y_156_, 2);
v_options_169_ = lean_ctor_get(v_toCold_166_, 2);
lean_inc_ref(v_options_169_);
lean_inc_ref(v_lctx_168_);
v___x_170_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_170_, 0, v_env_164_);
lean_ctor_set(v___x_170_, 1, v_mctx_167_);
lean_ctor_set(v___x_170_, 2, v_lctx_168_);
lean_ctor_set(v___x_170_, 3, v_options_169_);
v___x_171_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v_msgData_155_);
v___x_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0___boxed(lean_object* v_msgData_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0(v_msgData_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(lean_object* v_msg_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v_ref_186_; lean_object* v___x_187_; lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_196_; 
v_ref_186_ = lean_ctor_get(v___y_183_, 2);
v___x_187_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0(v_msg_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
v_a_188_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_196_ == 0)
{
v___x_190_ = v___x_187_;
v_isShared_191_ = v_isSharedCheck_196_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_187_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_196_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_192_; lean_object* v___x_194_; 
lean_inc(v_ref_186_);
v___x_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_192_, 0, v_ref_186_);
lean_ctor_set(v___x_192_, 1, v_a_188_);
if (v_isShared_191_ == 0)
{
lean_ctor_set_tag(v___x_190_, 1);
lean_ctor_set(v___x_190_, 0, v___x_192_);
v___x_194_ = v___x_190_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg___boxed(lean_object* v_msg_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v_msg_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
return v_res_203_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__0));
v___x_206_ = l_Lean_stringToMessageData(v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_213_, v_a_216_);
if (lean_obj_tag(v___x_219_) == 0)
{
lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_233_; 
v_a_220_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_233_ == 0)
{
v___x_222_ = v___x_219_;
v_isShared_223_ = v_isSharedCheck_233_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_219_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_233_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v_semirings_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v_semirings_224_ = lean_ctor_get(v_a_220_, 2);
lean_inc_ref(v_semirings_224_);
lean_dec(v_a_220_);
v___x_225_ = lean_array_get_size(v_semirings_224_);
v___x_226_ = lean_nat_dec_lt(v_a_207_, v___x_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; lean_object* v___x_228_; 
lean_dec_ref(v_semirings_224_);
lean_del_object(v___x_222_);
v___x_227_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1);
v___x_228_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v___x_227_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
return v___x_228_;
}
else
{
lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_229_ = lean_array_fget(v_semirings_224_, v_a_207_);
lean_dec_ref(v_semirings_224_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 0, v___x_229_);
v___x_231_ = v___x_222_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_229_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
v_a_234_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___x_219_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_219_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___boxed(lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
lean_dec(v_a_244_);
lean_dec(v_a_243_);
lean_dec(v_a_242_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0(lean_object* v_00_u03b1_255_, lean_object* v_msg_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v_msg_256_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___boxed(lean_object* v_00_u03b1_270_, lean_object* v_msg_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0(v_00_u03b1_270_, v_msg_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec(v___y_273_);
lean_dec(v___y_272_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0(lean_object* v_a_285_, lean_object* v_f_286_, lean_object* v_s_287_){
_start:
{
lean_object* v_exp_288_; lean_object* v_rings_289_; lean_object* v_semirings_290_; lean_object* v_ncRings_291_; lean_object* v_ncSemirings_292_; lean_object* v_typeClassify_293_; lean_object* v_orders_294_; lean_object* v_typeOrderClassify_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v_exp_288_ = lean_ctor_get(v_s_287_, 0);
v_rings_289_ = lean_ctor_get(v_s_287_, 1);
v_semirings_290_ = lean_ctor_get(v_s_287_, 2);
v_ncRings_291_ = lean_ctor_get(v_s_287_, 3);
v_ncSemirings_292_ = lean_ctor_get(v_s_287_, 4);
v_typeClassify_293_ = lean_ctor_get(v_s_287_, 5);
v_orders_294_ = lean_ctor_get(v_s_287_, 6);
v_typeOrderClassify_295_ = lean_ctor_get(v_s_287_, 7);
v___x_296_ = lean_array_get_size(v_semirings_290_);
v___x_297_ = lean_nat_dec_lt(v_a_285_, v___x_296_);
if (v___x_297_ == 0)
{
lean_dec_ref(v_f_286_);
return v_s_287_;
}
else
{
lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_309_; 
lean_inc_ref(v_typeOrderClassify_295_);
lean_inc_ref(v_orders_294_);
lean_inc_ref(v_typeClassify_293_);
lean_inc_ref(v_ncSemirings_292_);
lean_inc_ref(v_ncRings_291_);
lean_inc_ref(v_semirings_290_);
lean_inc_ref(v_rings_289_);
lean_inc(v_exp_288_);
v_isSharedCheck_309_ = !lean_is_exclusive(v_s_287_);
if (v_isSharedCheck_309_ == 0)
{
lean_object* v_unused_310_; lean_object* v_unused_311_; lean_object* v_unused_312_; lean_object* v_unused_313_; lean_object* v_unused_314_; lean_object* v_unused_315_; lean_object* v_unused_316_; lean_object* v_unused_317_; 
v_unused_310_ = lean_ctor_get(v_s_287_, 7);
lean_dec(v_unused_310_);
v_unused_311_ = lean_ctor_get(v_s_287_, 6);
lean_dec(v_unused_311_);
v_unused_312_ = lean_ctor_get(v_s_287_, 5);
lean_dec(v_unused_312_);
v_unused_313_ = lean_ctor_get(v_s_287_, 4);
lean_dec(v_unused_313_);
v_unused_314_ = lean_ctor_get(v_s_287_, 3);
lean_dec(v_unused_314_);
v_unused_315_ = lean_ctor_get(v_s_287_, 2);
lean_dec(v_unused_315_);
v_unused_316_ = lean_ctor_get(v_s_287_, 1);
lean_dec(v_unused_316_);
v_unused_317_ = lean_ctor_get(v_s_287_, 0);
lean_dec(v_unused_317_);
v___x_299_ = v_s_287_;
v_isShared_300_ = v_isSharedCheck_309_;
goto v_resetjp_298_;
}
else
{
lean_dec(v_s_287_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_309_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v_v_301_; lean_object* v___x_302_; lean_object* v_xs_x27_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_307_; 
v_v_301_ = lean_array_fget(v_semirings_290_, v_a_285_);
v___x_302_ = lean_box(0);
v_xs_x27_303_ = lean_array_fset(v_semirings_290_, v_a_285_, v___x_302_);
v___x_304_ = lean_apply_1(v_f_286_, v_v_301_);
v___x_305_ = lean_array_fset(v_xs_x27_303_, v_a_285_, v___x_304_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 2, v___x_305_);
v___x_307_ = v___x_299_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_exp_288_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_rings_289_);
lean_ctor_set(v_reuseFailAlloc_308_, 2, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_308_, 3, v_ncRings_291_);
lean_ctor_set(v_reuseFailAlloc_308_, 4, v_ncSemirings_292_);
lean_ctor_set(v_reuseFailAlloc_308_, 5, v_typeClassify_293_);
lean_ctor_set(v_reuseFailAlloc_308_, 6, v_orders_294_);
lean_ctor_set(v_reuseFailAlloc_308_, 7, v_typeOrderClassify_295_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed(lean_object* v_a_318_, lean_object* v_f_319_, lean_object* v_s_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0(v_a_318_, v_f_319_, v_s_320_);
lean_dec(v_a_318_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg(lean_object* v_f_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v___f_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
lean_inc(v_a_323_);
v___f_326_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_326_, 0, v_a_323_);
lean_closure_set(v___f_326_, 1, v_f_322_);
v___x_327_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_328_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_327_, v___f_326_, v_a_324_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___boxed(lean_object* v_f_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg(v_f_329_, v_a_330_, v_a_331_);
lean_dec(v_a_331_);
lean_dec(v_a_330_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring(lean_object* v_f_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v___f_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
lean_inc(v_a_335_);
v___f_347_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_347_, 0, v_a_335_);
lean_closure_set(v___f_347_, 1, v_f_334_);
v___x_348_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_349_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_348_, v___f_347_, v_a_341_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___boxed(lean_object* v_f_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring(v_f_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
lean_dec(v_a_353_);
lean_dec(v_a_352_);
lean_dec(v_a_351_);
return v_res_363_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_365_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__0));
v___x_366_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___boxed), 12, 0);
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set(v___x_367_, 1, v___x_365_);
return v___x_367_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM(void){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1);
return v___x_368_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__0));
v___x_371_ = l_Lean_stringToMessageData(v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_378_, v_a_381_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_386_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_385_);
lean_dec_ref_known(v___x_384_, 1);
v___x_386_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_401_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_401_ == 0)
{
v___x_389_ = v___x_386_;
v_isShared_390_ = v_isSharedCheck_401_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_386_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_401_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v_ringId_391_; lean_object* v_rings_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v_ringId_391_ = lean_ctor_get(v_a_387_, 1);
lean_inc(v_ringId_391_);
lean_dec(v_a_387_);
v_rings_392_ = lean_ctor_get(v_a_385_, 1);
lean_inc_ref(v_rings_392_);
lean_dec(v_a_385_);
v___x_393_ = lean_array_get_size(v_rings_392_);
v___x_394_ = lean_nat_dec_lt(v_ringId_391_, v___x_393_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; lean_object* v___x_396_; 
lean_dec_ref(v_rings_392_);
lean_dec(v_ringId_391_);
lean_del_object(v___x_389_);
v___x_395_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1);
v___x_396_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v___x_395_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
return v___x_396_;
}
else
{
lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_397_ = lean_array_fget(v_rings_392_, v_ringId_391_);
lean_dec(v_ringId_391_);
lean_dec_ref(v_rings_392_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_397_);
v___x_399_ = v___x_389_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_397_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
lean_dec(v_a_385_);
v_a_402_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_386_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_386_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
v_a_410_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_384_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_384_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___boxed(lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
lean_dec(v_a_428_);
lean_dec_ref(v_a_427_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
lean_dec(v_a_420_);
lean_dec(v_a_419_);
lean_dec(v_a_418_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0(lean_object* v_ringId_431_, lean_object* v_f_432_, lean_object* v_s_433_){
_start:
{
lean_object* v_exp_434_; lean_object* v_rings_435_; lean_object* v_semirings_436_; lean_object* v_ncRings_437_; lean_object* v_ncSemirings_438_; lean_object* v_typeClassify_439_; lean_object* v_orders_440_; lean_object* v_typeOrderClassify_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v_exp_434_ = lean_ctor_get(v_s_433_, 0);
v_rings_435_ = lean_ctor_get(v_s_433_, 1);
v_semirings_436_ = lean_ctor_get(v_s_433_, 2);
v_ncRings_437_ = lean_ctor_get(v_s_433_, 3);
v_ncSemirings_438_ = lean_ctor_get(v_s_433_, 4);
v_typeClassify_439_ = lean_ctor_get(v_s_433_, 5);
v_orders_440_ = lean_ctor_get(v_s_433_, 6);
v_typeOrderClassify_441_ = lean_ctor_get(v_s_433_, 7);
v___x_442_ = lean_array_get_size(v_rings_435_);
v___x_443_ = lean_nat_dec_lt(v_ringId_431_, v___x_442_);
if (v___x_443_ == 0)
{
lean_dec_ref(v_f_432_);
return v_s_433_;
}
else
{
lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_455_; 
lean_inc_ref(v_typeOrderClassify_441_);
lean_inc_ref(v_orders_440_);
lean_inc_ref(v_typeClassify_439_);
lean_inc_ref(v_ncSemirings_438_);
lean_inc_ref(v_ncRings_437_);
lean_inc_ref(v_semirings_436_);
lean_inc_ref(v_rings_435_);
lean_inc(v_exp_434_);
v_isSharedCheck_455_ = !lean_is_exclusive(v_s_433_);
if (v_isSharedCheck_455_ == 0)
{
lean_object* v_unused_456_; lean_object* v_unused_457_; lean_object* v_unused_458_; lean_object* v_unused_459_; lean_object* v_unused_460_; lean_object* v_unused_461_; lean_object* v_unused_462_; lean_object* v_unused_463_; 
v_unused_456_ = lean_ctor_get(v_s_433_, 7);
lean_dec(v_unused_456_);
v_unused_457_ = lean_ctor_get(v_s_433_, 6);
lean_dec(v_unused_457_);
v_unused_458_ = lean_ctor_get(v_s_433_, 5);
lean_dec(v_unused_458_);
v_unused_459_ = lean_ctor_get(v_s_433_, 4);
lean_dec(v_unused_459_);
v_unused_460_ = lean_ctor_get(v_s_433_, 3);
lean_dec(v_unused_460_);
v_unused_461_ = lean_ctor_get(v_s_433_, 2);
lean_dec(v_unused_461_);
v_unused_462_ = lean_ctor_get(v_s_433_, 1);
lean_dec(v_unused_462_);
v_unused_463_ = lean_ctor_get(v_s_433_, 0);
lean_dec(v_unused_463_);
v___x_445_ = v_s_433_;
v_isShared_446_ = v_isSharedCheck_455_;
goto v_resetjp_444_;
}
else
{
lean_dec(v_s_433_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_455_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v_v_447_; lean_object* v___x_448_; lean_object* v_xs_x27_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_453_; 
v_v_447_ = lean_array_fget(v_rings_435_, v_ringId_431_);
v___x_448_ = lean_box(0);
v_xs_x27_449_ = lean_array_fset(v_rings_435_, v_ringId_431_, v___x_448_);
v___x_450_ = lean_apply_1(v_f_432_, v_v_447_);
v___x_451_ = lean_array_fset(v_xs_x27_449_, v_ringId_431_, v___x_450_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 1, v___x_451_);
v___x_453_ = v___x_445_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_exp_434_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v___x_451_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v_semirings_436_);
lean_ctor_set(v_reuseFailAlloc_454_, 3, v_ncRings_437_);
lean_ctor_set(v_reuseFailAlloc_454_, 4, v_ncSemirings_438_);
lean_ctor_set(v_reuseFailAlloc_454_, 5, v_typeClassify_439_);
lean_ctor_set(v_reuseFailAlloc_454_, 6, v_orders_440_);
lean_ctor_set(v_reuseFailAlloc_454_, 7, v_typeOrderClassify_441_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0___boxed(lean_object* v_ringId_464_, lean_object* v_f_465_, lean_object* v_s_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0(v_ringId_464_, v_f_465_, v_s_466_);
lean_dec(v_ringId_464_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(lean_object* v_f_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v_ringId_483_; lean_object* v___f_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_a_482_);
lean_dec_ref_known(v___x_481_, 1);
v_ringId_483_ = lean_ctor_get(v_a_482_, 1);
lean_inc(v_ringId_483_);
lean_dec(v_a_482_);
v___f_484_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0___boxed), 3, 2);
lean_closure_set(v___f_484_, 0, v_ringId_483_);
lean_closure_set(v___f_484_, 1, v_f_468_);
v___x_485_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_486_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_485_, v___f_484_, v_a_475_);
return v___x_486_;
}
else
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
lean_dec_ref(v_f_468_);
v_a_487_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_494_ == 0)
{
v___x_489_ = v___x_481_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_481_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_487_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___boxed(lean_object* v_f_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v_f_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
lean_dec(v_a_504_);
lean_dec_ref(v_a_503_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
lean_dec(v_a_497_);
lean_dec(v_a_496_);
return v_res_508_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_510_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__0));
v___x_511_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___boxed), 12, 0);
v___x_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
lean_ctor_set(v___x_512_, 1, v___x_510_);
return v___x_512_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM(void){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState___redArg(lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_515_, v_a_516_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_527_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_527_ == 0)
{
v___x_521_ = v___x_518_;
v_isShared_522_ = v_isSharedCheck_527_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_527_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; lean_object* v___x_525_; 
v___x_523_ = l_Lean_Meta_Grind_Arith_CommRing_State_getSemiring(v_a_519_, v_a_514_);
lean_dec(v_a_519_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_523_);
v___x_525_ = v___x_521_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
v_a_528_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_518_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_518_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState___redArg___boxed(lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState___redArg(v_a_536_, v_a_537_, v_a_538_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec(v_a_536_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState(lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState___redArg(v_a_541_, v_a_542_, v_a_550_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState___boxed(lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState(v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
lean_dec(v_a_564_);
lean_dec_ref(v_a_563_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec(v_a_555_);
lean_dec(v_a_554_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg___lam__0(lean_object* v_a_567_, lean_object* v_f_568_, lean_object* v_s_569_){
_start:
{
lean_object* v_rings_570_; lean_object* v_exprToRingId_571_; lean_object* v_semirings_572_; lean_object* v_exprToSemiringId_573_; lean_object* v_ncRings_574_; lean_object* v_exprToNCRingId_575_; lean_object* v_ncSemirings_576_; lean_object* v_exprToNCSemiringId_577_; lean_object* v_steps_578_; uint8_t v_reportedMaxDegreeIssue_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_600_; 
v_rings_570_ = lean_ctor_get(v_s_569_, 0);
v_exprToRingId_571_ = lean_ctor_get(v_s_569_, 1);
v_semirings_572_ = lean_ctor_get(v_s_569_, 2);
v_exprToSemiringId_573_ = lean_ctor_get(v_s_569_, 3);
v_ncRings_574_ = lean_ctor_get(v_s_569_, 4);
v_exprToNCRingId_575_ = lean_ctor_get(v_s_569_, 5);
v_ncSemirings_576_ = lean_ctor_get(v_s_569_, 6);
v_exprToNCSemiringId_577_ = lean_ctor_get(v_s_569_, 7);
v_steps_578_ = lean_ctor_get(v_s_569_, 8);
v_reportedMaxDegreeIssue_579_ = lean_ctor_get_uint8(v_s_569_, sizeof(void*)*9);
v_isSharedCheck_600_ = !lean_is_exclusive(v_s_569_);
if (v_isSharedCheck_600_ == 0)
{
v___x_581_ = v_s_569_;
v_isShared_582_ = v_isSharedCheck_600_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_steps_578_);
lean_inc(v_exprToNCSemiringId_577_);
lean_inc(v_ncSemirings_576_);
lean_inc(v_exprToNCRingId_575_);
lean_inc(v_ncRings_574_);
lean_inc(v_exprToSemiringId_573_);
lean_inc(v_semirings_572_);
lean_inc(v_exprToRingId_571_);
lean_inc(v_rings_570_);
lean_dec(v_s_569_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_600_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_583_ = lean_unsigned_to_nat(1u);
v___x_584_ = lean_nat_add(v_a_567_, v___x_583_);
v___x_585_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default;
v___x_586_ = l_Array_rightpad___redArg(v___x_584_, v___x_585_, v_semirings_572_);
lean_dec(v___x_584_);
v___x_587_ = lean_array_get_size(v___x_586_);
v___x_588_ = lean_nat_dec_lt(v_a_567_, v___x_587_);
if (v___x_588_ == 0)
{
lean_object* v___x_590_; 
lean_dec_ref(v_f_568_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 2, v___x_586_);
v___x_590_ = v___x_581_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_rings_570_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_exprToRingId_571_);
lean_ctor_set(v_reuseFailAlloc_591_, 2, v___x_586_);
lean_ctor_set(v_reuseFailAlloc_591_, 3, v_exprToSemiringId_573_);
lean_ctor_set(v_reuseFailAlloc_591_, 4, v_ncRings_574_);
lean_ctor_set(v_reuseFailAlloc_591_, 5, v_exprToNCRingId_575_);
lean_ctor_set(v_reuseFailAlloc_591_, 6, v_ncSemirings_576_);
lean_ctor_set(v_reuseFailAlloc_591_, 7, v_exprToNCSemiringId_577_);
lean_ctor_set(v_reuseFailAlloc_591_, 8, v_steps_578_);
lean_ctor_set_uint8(v_reuseFailAlloc_591_, sizeof(void*)*9, v_reportedMaxDegreeIssue_579_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
else
{
lean_object* v_v_592_; lean_object* v___x_593_; lean_object* v_xs_x27_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_598_; 
v_v_592_ = lean_array_fget(v___x_586_, v_a_567_);
v___x_593_ = lean_box(0);
v_xs_x27_594_ = lean_array_fset(v___x_586_, v_a_567_, v___x_593_);
v___x_595_ = lean_apply_1(v_f_568_, v_v_592_);
v___x_596_ = lean_array_fset(v_xs_x27_594_, v_a_567_, v___x_595_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 2, v___x_596_);
v___x_598_ = v___x_581_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_rings_570_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_exprToRingId_571_);
lean_ctor_set(v_reuseFailAlloc_599_, 2, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_599_, 3, v_exprToSemiringId_573_);
lean_ctor_set(v_reuseFailAlloc_599_, 4, v_ncRings_574_);
lean_ctor_set(v_reuseFailAlloc_599_, 5, v_exprToNCRingId_575_);
lean_ctor_set(v_reuseFailAlloc_599_, 6, v_ncSemirings_576_);
lean_ctor_set(v_reuseFailAlloc_599_, 7, v_exprToNCSemiringId_577_);
lean_ctor_set(v_reuseFailAlloc_599_, 8, v_steps_578_);
lean_ctor_set_uint8(v_reuseFailAlloc_599_, sizeof(void*)*9, v_reportedMaxDegreeIssue_579_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg___lam__0___boxed(lean_object* v_a_601_, lean_object* v_f_602_, lean_object* v_s_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg___lam__0(v_a_601_, v_f_602_, v_s_603_);
lean_dec(v_a_601_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg(lean_object* v_f_605_, lean_object* v_a_606_, lean_object* v_a_607_){
_start:
{
lean_object* v___f_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
lean_inc(v_a_606_);
v___f_609_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_609_, 0, v_a_606_);
lean_closure_set(v___f_609_, 1, v_f_605_);
v___x_610_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_611_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_610_, v___f_609_, v_a_607_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg___boxed(lean_object* v_f_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg(v_f_612_, v_a_613_, v_a_614_);
lean_dec(v_a_614_);
lean_dec(v_a_613_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState(lean_object* v_f_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg(v_f_617_, v_a_618_, v_a_619_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___boxed(lean_object* v_f_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState(v_f_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
lean_dec(v_a_642_);
lean_dec_ref(v_a_641_);
lean_dec(v_a_640_);
lean_dec_ref(v_a_639_);
lean_dec(v_a_638_);
lean_dec_ref(v_a_637_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_635_);
lean_dec(v_a_634_);
lean_dec(v_a_633_);
lean_dec(v_a_632_);
return v_res_644_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM___closed__1(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_646_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM___closed__0));
v___x_647_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState___boxed), 12, 0);
v___x_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
lean_ctor_set(v___x_648_, 1, v___x_646_);
return v___x_648_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM(void){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM___closed__1);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_650_, lean_object* v_vals_651_, lean_object* v_i_652_, lean_object* v_k_653_){
_start:
{
lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_654_ = lean_array_get_size(v_keys_650_);
v___x_655_ = lean_nat_dec_lt(v_i_652_, v___x_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; 
lean_dec(v_i_652_);
v___x_656_ = lean_box(0);
return v___x_656_;
}
else
{
lean_object* v_k_x27_657_; size_t v___x_658_; size_t v___x_659_; uint8_t v___x_660_; 
v_k_x27_657_ = lean_array_fget_borrowed(v_keys_650_, v_i_652_);
v___x_658_ = lean_ptr_addr(v_k_653_);
v___x_659_ = lean_ptr_addr(v_k_x27_657_);
v___x_660_ = lean_usize_dec_eq(v___x_658_, v___x_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = lean_unsigned_to_nat(1u);
v___x_662_ = lean_nat_add(v_i_652_, v___x_661_);
lean_dec(v_i_652_);
v_i_652_ = v___x_662_;
goto _start;
}
else
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = lean_array_fget_borrowed(v_vals_651_, v_i_652_);
lean_dec(v_i_652_);
lean_inc(v___x_664_);
v___x_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
return v___x_665_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_666_, lean_object* v_vals_667_, lean_object* v_i_668_, lean_object* v_k_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_666_, v_vals_667_, v_i_668_, v_k_669_);
lean_dec_ref(v_k_669_);
lean_dec_ref(v_vals_667_);
lean_dec_ref(v_keys_666_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(lean_object* v_x_671_, size_t v_x_672_, lean_object* v_x_673_){
_start:
{
if (lean_obj_tag(v_x_671_) == 0)
{
lean_object* v_es_674_; lean_object* v___x_675_; size_t v___x_676_; size_t v___x_677_; lean_object* v_j_678_; lean_object* v___x_679_; 
v_es_674_ = lean_ctor_get(v_x_671_, 0);
v___x_675_ = lean_box(2);
v___x_676_ = ((size_t)31ULL);
v___x_677_ = lean_usize_land(v_x_672_, v___x_676_);
v_j_678_ = lean_usize_to_nat(v___x_677_);
v___x_679_ = lean_array_get_borrowed(v___x_675_, v_es_674_, v_j_678_);
lean_dec(v_j_678_);
switch(lean_obj_tag(v___x_679_))
{
case 0:
{
lean_object* v_key_680_; lean_object* v_val_681_; size_t v___x_682_; size_t v___x_683_; uint8_t v___x_684_; 
v_key_680_ = lean_ctor_get(v___x_679_, 0);
v_val_681_ = lean_ctor_get(v___x_679_, 1);
v___x_682_ = lean_ptr_addr(v_x_673_);
v___x_683_ = lean_ptr_addr(v_key_680_);
v___x_684_ = lean_usize_dec_eq(v___x_682_, v___x_683_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; 
v___x_685_ = lean_box(0);
return v___x_685_;
}
else
{
lean_object* v___x_686_; 
lean_inc(v_val_681_);
v___x_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_686_, 0, v_val_681_);
return v___x_686_;
}
}
case 1:
{
lean_object* v_node_687_; size_t v___x_688_; size_t v___x_689_; 
v_node_687_ = lean_ctor_get(v___x_679_, 0);
v___x_688_ = ((size_t)5ULL);
v___x_689_ = lean_usize_shift_right(v_x_672_, v___x_688_);
v_x_671_ = v_node_687_;
v_x_672_ = v___x_689_;
goto _start;
}
default: 
{
lean_object* v___x_691_; 
v___x_691_ = lean_box(0);
return v___x_691_;
}
}
}
else
{
lean_object* v_ks_692_; lean_object* v_vs_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v_ks_692_ = lean_ctor_get(v_x_671_, 0);
v_vs_693_ = lean_ctor_get(v_x_671_, 1);
v___x_694_ = lean_unsigned_to_nat(0u);
v___x_695_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_692_, v_vs_693_, v___x_694_, v_x_673_);
return v___x_695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_696_, lean_object* v_x_697_, lean_object* v_x_698_){
_start:
{
size_t v_x_905__boxed_699_; lean_object* v_res_700_; 
v_x_905__boxed_699_ = lean_unbox_usize(v_x_697_);
lean_dec(v_x_697_);
v_res_700_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_696_, v_x_905__boxed_699_, v_x_698_);
lean_dec_ref(v_x_698_);
lean_dec_ref(v_x_696_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(lean_object* v_x_701_, lean_object* v_x_702_){
_start:
{
size_t v___x_703_; size_t v___x_704_; size_t v___x_705_; uint64_t v___x_706_; size_t v___x_707_; lean_object* v___x_708_; 
v___x_703_ = lean_ptr_addr(v_x_702_);
v___x_704_ = ((size_t)3ULL);
v___x_705_ = lean_usize_shift_right(v___x_703_, v___x_704_);
v___x_706_ = lean_usize_to_uint64(v___x_705_);
v___x_707_ = lean_uint64_to_usize(v___x_706_);
v___x_708_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_701_, v___x_707_, v_x_702_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg___boxed(lean_object* v_x_709_, lean_object* v_x_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_x_709_, v_x_710_);
lean_dec_ref(v_x_710_);
lean_dec_ref(v_x_709_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(lean_object* v_e_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_713_, v_a_714_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_726_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_726_ == 0)
{
v___x_719_ = v___x_716_;
v_isShared_720_ = v_isSharedCheck_726_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_726_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v_exprToSemiringId_721_; lean_object* v___x_722_; lean_object* v___x_724_; 
v_exprToSemiringId_721_ = lean_ctor_get(v_a_717_, 3);
lean_inc_ref(v_exprToSemiringId_721_);
lean_dec(v_a_717_);
v___x_722_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_exprToSemiringId_721_, v_e_712_);
lean_dec_ref(v_exprToSemiringId_721_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v___x_722_);
v___x_724_ = v___x_719_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
v_a_727_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_716_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_716_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg___boxed(lean_object* v_e_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_735_, v_a_736_, v_a_737_);
lean_dec_ref(v_a_737_);
lean_dec(v_a_736_);
lean_dec_ref(v_e_735_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f(lean_object* v_e_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_740_, v_a_741_, v_a_749_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___boxed(lean_object* v_e_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f(v_e_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_);
lean_dec(v_a_763_);
lean_dec_ref(v_a_762_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_a_759_);
lean_dec_ref(v_a_758_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
lean_dec(v_a_755_);
lean_dec(v_a_754_);
lean_dec_ref(v_e_753_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0(lean_object* v_00_u03b2_766_, lean_object* v_x_767_, lean_object* v_x_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_x_767_, v_x_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___boxed(lean_object* v_00_u03b2_770_, lean_object* v_x_771_, lean_object* v_x_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0(v_00_u03b2_770_, v_x_771_, v_x_772_);
lean_dec_ref(v_x_772_);
lean_dec_ref(v_x_771_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_774_, lean_object* v_x_775_, size_t v_x_776_, lean_object* v_x_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_775_, v_x_776_, v_x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_779_, lean_object* v_x_780_, lean_object* v_x_781_, lean_object* v_x_782_){
_start:
{
size_t v_x_1026__boxed_783_; lean_object* v_res_784_; 
v_x_1026__boxed_783_ = lean_unbox_usize(v_x_781_);
lean_dec(v_x_781_);
v_res_784_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0(v_00_u03b2_779_, v_x_780_, v_x_1026__boxed_783_, v_x_782_);
lean_dec_ref(v_x_782_);
lean_dec_ref(v_x_780_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_785_, lean_object* v_keys_786_, lean_object* v_vals_787_, lean_object* v_heq_788_, lean_object* v_i_789_, lean_object* v_k_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_786_, v_vals_787_, v_i_789_, v_k_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_792_, lean_object* v_keys_793_, lean_object* v_vals_794_, lean_object* v_heq_795_, lean_object* v_i_796_, lean_object* v_k_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_792_, v_keys_793_, v_vals_794_, v_heq_795_, v_i_796_, v_k_797_);
lean_dec_ref(v_k_797_);
lean_dec_ref(v_vals_794_);
lean_dec_ref(v_keys_793_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_799_, lean_object* v_x_800_, lean_object* v_x_801_, lean_object* v_x_802_){
_start:
{
lean_object* v_ks_803_; lean_object* v_vs_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_830_; 
v_ks_803_ = lean_ctor_get(v_x_799_, 0);
v_vs_804_ = lean_ctor_get(v_x_799_, 1);
v_isSharedCheck_830_ = !lean_is_exclusive(v_x_799_);
if (v_isSharedCheck_830_ == 0)
{
v___x_806_ = v_x_799_;
v_isShared_807_ = v_isSharedCheck_830_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_vs_804_);
lean_inc(v_ks_803_);
lean_dec(v_x_799_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_830_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_808_ = lean_array_get_size(v_ks_803_);
v___x_809_ = lean_nat_dec_lt(v_x_800_, v___x_808_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_813_; 
lean_dec(v_x_800_);
v___x_810_ = lean_array_push(v_ks_803_, v_x_801_);
v___x_811_ = lean_array_push(v_vs_804_, v_x_802_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 1, v___x_811_);
lean_ctor_set(v___x_806_, 0, v___x_810_);
v___x_813_ = v___x_806_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v___x_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
else
{
lean_object* v_k_x27_815_; size_t v___x_816_; size_t v___x_817_; uint8_t v___x_818_; 
v_k_x27_815_ = lean_array_fget_borrowed(v_ks_803_, v_x_800_);
v___x_816_ = lean_ptr_addr(v_x_801_);
v___x_817_ = lean_ptr_addr(v_k_x27_815_);
v___x_818_ = lean_usize_dec_eq(v___x_816_, v___x_817_);
if (v___x_818_ == 0)
{
lean_object* v___x_820_; 
if (v_isShared_807_ == 0)
{
v___x_820_ = v___x_806_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_ks_803_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v_vs_804_);
v___x_820_ = v_reuseFailAlloc_824_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = lean_unsigned_to_nat(1u);
v___x_822_ = lean_nat_add(v_x_800_, v___x_821_);
lean_dec(v_x_800_);
v_x_799_ = v___x_820_;
v_x_800_ = v___x_822_;
goto _start;
}
}
else
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_825_ = lean_array_fset(v_ks_803_, v_x_800_, v_x_801_);
v___x_826_ = lean_array_fset(v_vs_804_, v_x_800_, v_x_802_);
lean_dec(v_x_800_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 1, v___x_826_);
lean_ctor_set(v___x_806_, 0, v___x_825_);
v___x_828_ = v___x_806_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_825_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v___x_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_831_, lean_object* v_k_832_, lean_object* v_v_833_){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_unsigned_to_nat(0u);
v___x_835_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_831_, v___x_834_, v_k_832_, v_v_833_);
return v___x_835_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(lean_object* v_x_837_, size_t v_x_838_, size_t v_x_839_, lean_object* v_x_840_, lean_object* v_x_841_){
_start:
{
if (lean_obj_tag(v_x_837_) == 0)
{
lean_object* v_es_842_; size_t v___x_843_; size_t v___x_844_; lean_object* v_j_845_; lean_object* v___x_846_; uint8_t v___x_847_; 
v_es_842_ = lean_ctor_get(v_x_837_, 0);
v___x_843_ = ((size_t)31ULL);
v___x_844_ = lean_usize_land(v_x_838_, v___x_843_);
v_j_845_ = lean_usize_to_nat(v___x_844_);
v___x_846_ = lean_array_get_size(v_es_842_);
v___x_847_ = lean_nat_dec_lt(v_j_845_, v___x_846_);
if (v___x_847_ == 0)
{
lean_dec(v_j_845_);
lean_dec(v_x_841_);
lean_dec_ref(v_x_840_);
return v_x_837_;
}
else
{
lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_888_; 
lean_inc_ref(v_es_842_);
v_isSharedCheck_888_ = !lean_is_exclusive(v_x_837_);
if (v_isSharedCheck_888_ == 0)
{
lean_object* v_unused_889_; 
v_unused_889_ = lean_ctor_get(v_x_837_, 0);
lean_dec(v_unused_889_);
v___x_849_ = v_x_837_;
v_isShared_850_ = v_isSharedCheck_888_;
goto v_resetjp_848_;
}
else
{
lean_dec(v_x_837_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_888_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v_v_851_; lean_object* v___x_852_; lean_object* v_xs_x27_853_; lean_object* v___y_855_; 
v_v_851_ = lean_array_fget(v_es_842_, v_j_845_);
v___x_852_ = lean_box(0);
v_xs_x27_853_ = lean_array_fset(v_es_842_, v_j_845_, v___x_852_);
switch(lean_obj_tag(v_v_851_))
{
case 0:
{
lean_object* v_key_860_; lean_object* v_val_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_873_; 
v_key_860_ = lean_ctor_get(v_v_851_, 0);
v_val_861_ = lean_ctor_get(v_v_851_, 1);
v_isSharedCheck_873_ = !lean_is_exclusive(v_v_851_);
if (v_isSharedCheck_873_ == 0)
{
v___x_863_ = v_v_851_;
v_isShared_864_ = v_isSharedCheck_873_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_val_861_);
lean_inc(v_key_860_);
lean_dec(v_v_851_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_873_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
size_t v___x_865_; size_t v___x_866_; uint8_t v___x_867_; 
v___x_865_ = lean_ptr_addr(v_x_840_);
v___x_866_ = lean_ptr_addr(v_key_860_);
v___x_867_ = lean_usize_dec_eq(v___x_865_, v___x_866_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; lean_object* v___x_869_; 
lean_del_object(v___x_863_);
v___x_868_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_860_, v_val_861_, v_x_840_, v_x_841_);
v___x_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
v___y_855_ = v___x_869_;
goto v___jp_854_;
}
else
{
lean_object* v___x_871_; 
lean_dec(v_val_861_);
lean_dec(v_key_860_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 1, v_x_841_);
lean_ctor_set(v___x_863_, 0, v_x_840_);
v___x_871_ = v___x_863_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_x_840_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_x_841_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
v___y_855_ = v___x_871_;
goto v___jp_854_;
}
}
}
}
case 1:
{
lean_object* v_node_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_886_; 
v_node_874_ = lean_ctor_get(v_v_851_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v_v_851_);
if (v_isSharedCheck_886_ == 0)
{
v___x_876_ = v_v_851_;
v_isShared_877_ = v_isSharedCheck_886_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_node_874_);
lean_dec(v_v_851_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_886_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
size_t v___x_878_; size_t v___x_879_; size_t v___x_880_; size_t v___x_881_; lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_878_ = ((size_t)5ULL);
v___x_879_ = lean_usize_shift_right(v_x_838_, v___x_878_);
v___x_880_ = ((size_t)1ULL);
v___x_881_ = lean_usize_add(v_x_839_, v___x_880_);
v___x_882_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_node_874_, v___x_879_, v___x_881_, v_x_840_, v_x_841_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_882_);
v___x_884_ = v___x_876_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
v___y_855_ = v___x_884_;
goto v___jp_854_;
}
}
}
default: 
{
lean_object* v___x_887_; 
v___x_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_887_, 0, v_x_840_);
lean_ctor_set(v___x_887_, 1, v_x_841_);
v___y_855_ = v___x_887_;
goto v___jp_854_;
}
}
v___jp_854_:
{
lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_856_ = lean_array_fset(v_xs_x27_853_, v_j_845_, v___y_855_);
lean_dec(v_j_845_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_856_);
v___x_858_ = v___x_849_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
else
{
lean_object* v_ks_890_; lean_object* v_vs_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_909_; 
v_ks_890_ = lean_ctor_get(v_x_837_, 0);
v_vs_891_ = lean_ctor_get(v_x_837_, 1);
v_isSharedCheck_909_ = !lean_is_exclusive(v_x_837_);
if (v_isSharedCheck_909_ == 0)
{
v___x_893_ = v_x_837_;
v_isShared_894_ = v_isSharedCheck_909_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_vs_891_);
lean_inc(v_ks_890_);
lean_dec(v_x_837_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_909_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_ks_890_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_vs_891_);
v___x_896_ = v_reuseFailAlloc_908_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v_newNode_897_; size_t v___x_898_; uint8_t v___x_899_; 
v_newNode_897_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(v___x_896_, v_x_840_, v_x_841_);
v___x_898_ = ((size_t)7ULL);
v___x_899_ = lean_usize_dec_le(v___x_898_, v_x_839_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_900_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_897_);
v___x_901_ = lean_unsigned_to_nat(4u);
v___x_902_ = lean_nat_dec_lt(v___x_900_, v___x_901_);
lean_dec(v___x_900_);
if (v___x_902_ == 0)
{
lean_object* v_ks_903_; lean_object* v_vs_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v_ks_903_ = lean_ctor_get(v_newNode_897_, 0);
lean_inc_ref(v_ks_903_);
v_vs_904_ = lean_ctor_get(v_newNode_897_, 1);
lean_inc_ref(v_vs_904_);
lean_dec_ref(v_newNode_897_);
v___x_905_ = lean_unsigned_to_nat(0u);
v___x_906_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0);
v___x_907_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_x_839_, v_ks_903_, v_vs_904_, v___x_905_, v___x_906_);
lean_dec_ref(v_vs_904_);
lean_dec_ref(v_ks_903_);
return v___x_907_;
}
else
{
return v_newNode_897_;
}
}
else
{
return v_newNode_897_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(size_t v_depth_910_, lean_object* v_keys_911_, lean_object* v_vals_912_, lean_object* v_i_913_, lean_object* v_entries_914_){
_start:
{
lean_object* v___x_915_; uint8_t v___x_916_; 
v___x_915_ = lean_array_get_size(v_keys_911_);
v___x_916_ = lean_nat_dec_lt(v_i_913_, v___x_915_);
if (v___x_916_ == 0)
{
lean_dec(v_i_913_);
return v_entries_914_;
}
else
{
lean_object* v_k_917_; lean_object* v_v_918_; size_t v___x_919_; size_t v___x_920_; size_t v___x_921_; uint64_t v___x_922_; size_t v_h_923_; size_t v___x_924_; lean_object* v___x_925_; size_t v___x_926_; size_t v___x_927_; size_t v___x_928_; size_t v_h_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v_k_917_ = lean_array_fget_borrowed(v_keys_911_, v_i_913_);
v_v_918_ = lean_array_fget_borrowed(v_vals_912_, v_i_913_);
v___x_919_ = lean_ptr_addr(v_k_917_);
v___x_920_ = ((size_t)3ULL);
v___x_921_ = lean_usize_shift_right(v___x_919_, v___x_920_);
v___x_922_ = lean_usize_to_uint64(v___x_921_);
v_h_923_ = lean_uint64_to_usize(v___x_922_);
v___x_924_ = ((size_t)5ULL);
v___x_925_ = lean_unsigned_to_nat(1u);
v___x_926_ = ((size_t)1ULL);
v___x_927_ = lean_usize_sub(v_depth_910_, v___x_926_);
v___x_928_ = lean_usize_mul(v___x_924_, v___x_927_);
v_h_929_ = lean_usize_shift_right(v_h_923_, v___x_928_);
v___x_930_ = lean_nat_add(v_i_913_, v___x_925_);
lean_dec(v_i_913_);
lean_inc(v_v_918_);
lean_inc(v_k_917_);
v___x_931_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_entries_914_, v_h_929_, v_depth_910_, v_k_917_, v_v_918_);
v_i_913_ = v___x_930_;
v_entries_914_ = v___x_931_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_933_, lean_object* v_keys_934_, lean_object* v_vals_935_, lean_object* v_i_936_, lean_object* v_entries_937_){
_start:
{
size_t v_depth_boxed_938_; lean_object* v_res_939_; 
v_depth_boxed_938_ = lean_unbox_usize(v_depth_933_);
lean_dec(v_depth_933_);
v_res_939_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_938_, v_keys_934_, v_vals_935_, v_i_936_, v_entries_937_);
lean_dec_ref(v_vals_935_);
lean_dec_ref(v_keys_934_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___boxed(lean_object* v_x_940_, lean_object* v_x_941_, lean_object* v_x_942_, lean_object* v_x_943_, lean_object* v_x_944_){
_start:
{
size_t v_x_6465__boxed_945_; size_t v_x_6466__boxed_946_; lean_object* v_res_947_; 
v_x_6465__boxed_945_ = lean_unbox_usize(v_x_941_);
lean_dec(v_x_941_);
v_x_6466__boxed_946_ = lean_unbox_usize(v_x_942_);
lean_dec(v_x_942_);
v_res_947_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_940_, v_x_6465__boxed_945_, v_x_6466__boxed_946_, v_x_943_, v_x_944_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(lean_object* v_x_948_, lean_object* v_x_949_, lean_object* v_x_950_){
_start:
{
size_t v___x_951_; size_t v___x_952_; size_t v___x_953_; uint64_t v___x_954_; size_t v___x_955_; size_t v___x_956_; lean_object* v___x_957_; 
v___x_951_ = lean_ptr_addr(v_x_949_);
v___x_952_ = ((size_t)3ULL);
v___x_953_ = lean_usize_shift_right(v___x_951_, v___x_952_);
v___x_954_ = lean_usize_to_uint64(v___x_953_);
v___x_955_ = lean_uint64_to_usize(v___x_954_);
v___x_956_ = ((size_t)1ULL);
v___x_957_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_948_, v___x_955_, v___x_956_, v_x_949_, v_x_950_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0(lean_object* v_e_958_, lean_object* v_a_959_, lean_object* v_s_960_){
_start:
{
lean_object* v_rings_961_; lean_object* v_exprToRingId_962_; lean_object* v_semirings_963_; lean_object* v_exprToSemiringId_964_; lean_object* v_ncRings_965_; lean_object* v_exprToNCRingId_966_; lean_object* v_ncSemirings_967_; lean_object* v_exprToNCSemiringId_968_; lean_object* v_steps_969_; uint8_t v_reportedMaxDegreeIssue_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_978_; 
v_rings_961_ = lean_ctor_get(v_s_960_, 0);
v_exprToRingId_962_ = lean_ctor_get(v_s_960_, 1);
v_semirings_963_ = lean_ctor_get(v_s_960_, 2);
v_exprToSemiringId_964_ = lean_ctor_get(v_s_960_, 3);
v_ncRings_965_ = lean_ctor_get(v_s_960_, 4);
v_exprToNCRingId_966_ = lean_ctor_get(v_s_960_, 5);
v_ncSemirings_967_ = lean_ctor_get(v_s_960_, 6);
v_exprToNCSemiringId_968_ = lean_ctor_get(v_s_960_, 7);
v_steps_969_ = lean_ctor_get(v_s_960_, 8);
v_reportedMaxDegreeIssue_970_ = lean_ctor_get_uint8(v_s_960_, sizeof(void*)*9);
v_isSharedCheck_978_ = !lean_is_exclusive(v_s_960_);
if (v_isSharedCheck_978_ == 0)
{
v___x_972_ = v_s_960_;
v_isShared_973_ = v_isSharedCheck_978_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_steps_969_);
lean_inc(v_exprToNCSemiringId_968_);
lean_inc(v_ncSemirings_967_);
lean_inc(v_exprToNCRingId_966_);
lean_inc(v_ncRings_965_);
lean_inc(v_exprToSemiringId_964_);
lean_inc(v_semirings_963_);
lean_inc(v_exprToRingId_962_);
lean_inc(v_rings_961_);
lean_dec(v_s_960_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_978_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; lean_object* v___x_976_; 
lean_inc(v_a_959_);
v___x_974_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_exprToSemiringId_964_, v_e_958_, v_a_959_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 3, v___x_974_);
v___x_976_ = v___x_972_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_rings_961_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_exprToRingId_962_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_semirings_963_);
lean_ctor_set(v_reuseFailAlloc_977_, 3, v___x_974_);
lean_ctor_set(v_reuseFailAlloc_977_, 4, v_ncRings_965_);
lean_ctor_set(v_reuseFailAlloc_977_, 5, v_exprToNCRingId_966_);
lean_ctor_set(v_reuseFailAlloc_977_, 6, v_ncSemirings_967_);
lean_ctor_set(v_reuseFailAlloc_977_, 7, v_exprToNCSemiringId_968_);
lean_ctor_set(v_reuseFailAlloc_977_, 8, v_steps_969_);
lean_ctor_set_uint8(v_reuseFailAlloc_977_, sizeof(void*)*9, v_reportedMaxDegreeIssue_970_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0___boxed(lean_object* v_e_979_, lean_object* v_a_980_, lean_object* v_s_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0(v_e_979_, v_a_980_, v_s_981_);
lean_dec(v_a_980_);
return v_res_982_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__0));
v___x_985_ = l_Lean_stringToMessageData(v___x_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(lean_object* v_e_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_){
_start:
{
lean_object* v___f_999_; lean_object* v___x_1000_; 
lean_inc(v_a_987_);
lean_inc_ref(v_e_986_);
v___f_999_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_999_, 0, v_e_986_);
lean_closure_set(v___f_999_, 1, v_a_987_);
v___x_1000_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_986_, v_a_988_, v_a_993_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
if (lean_obj_tag(v_a_1001_) == 1)
{
lean_object* v_val_1002_; uint8_t v___x_1003_; 
lean_dec_ref(v___f_999_);
v_val_1002_ = lean_ctor_get(v_a_1001_, 0);
lean_inc(v_val_1002_);
lean_dec_ref_known(v_a_1001_, 1);
v___x_1003_ = lean_nat_dec_eq(v_val_1002_, v_a_987_);
lean_dec(v_val_1002_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1004_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1);
v___x_1005_ = l_Lean_indentExpr(v_e_986_);
v___x_1006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1004_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_989_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; uint8_t v_verbose_1009_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref_known(v___x_1007_, 1);
v_verbose_1009_ = lean_ctor_get_uint8(v_a_1008_, 0);
lean_dec(v_a_1008_);
if (v_verbose_1009_ == 0)
{
lean_dec_ref_known(v___x_1006_, 2);
goto v___jp_996_;
}
else
{
lean_object* v___x_1010_; 
v___x_1010_ = l_Lean_Meta_Sym_reportIssue(v___x_1006_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_dec_ref_known(v___x_1010_, 1);
goto v___jp_996_;
}
else
{
return v___x_1010_;
}
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_dec_ref_known(v___x_1006_, 2);
v_a_1011_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_1007_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1007_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
else
{
lean_dec_ref(v_e_986_);
goto v___jp_996_;
}
}
else
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
lean_dec(v_a_1001_);
lean_dec_ref(v_e_986_);
v___x_1019_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1020_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1019_, v___f_999_, v_a_988_);
return v___x_1020_;
}
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
lean_dec_ref(v___f_999_);
lean_dec_ref(v_e_986_);
v_a_1021_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_1000_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1000_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
v___jp_996_:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = lean_box(0);
v___x_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
return v___x_998_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___boxed(lean_object* v_e_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
lean_dec(v_a_1033_);
lean_dec_ref(v_a_1032_);
lean_dec(v_a_1031_);
lean_dec(v_a_1030_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(lean_object* v_e_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1040_, v_a_1041_, v_a_1042_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___boxed(lean_object* v_e_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(v_e_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
lean_dec(v_a_1057_);
lean_dec(v_a_1056_);
lean_dec(v_a_1055_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0(lean_object* v_00_u03b2_1068_, lean_object* v_x_1069_, lean_object* v_x_1070_, lean_object* v_x_1071_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_x_1069_, v_x_1070_, v_x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(lean_object* v_00_u03b2_1073_, lean_object* v_x_1074_, size_t v_x_1075_, size_t v_x_1076_, lean_object* v_x_1077_, lean_object* v_x_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_1074_, v_x_1075_, v_x_1076_, v_x_1077_, v_x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_, lean_object* v_x_1085_){
_start:
{
size_t v_x_6751__boxed_1086_; size_t v_x_6752__boxed_1087_; lean_object* v_res_1088_; 
v_x_6751__boxed_1086_ = lean_unbox_usize(v_x_1082_);
lean_dec(v_x_1082_);
v_x_6752__boxed_1087_ = lean_unbox_usize(v_x_1083_);
lean_dec(v_x_1083_);
v_res_1088_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(v_00_u03b2_1080_, v_x_1081_, v_x_6751__boxed_1086_, v_x_6752__boxed_1087_, v_x_1084_, v_x_1085_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1089_, lean_object* v_n_1090_, lean_object* v_k_1091_, lean_object* v_v_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(v_n_1090_, v_k_1091_, v_v_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1094_, size_t v_depth_1095_, lean_object* v_keys_1096_, lean_object* v_vals_1097_, lean_object* v_heq_1098_, lean_object* v_i_1099_, lean_object* v_entries_1100_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_1095_, v_keys_1096_, v_vals_1097_, v_i_1099_, v_entries_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1102_, lean_object* v_depth_1103_, lean_object* v_keys_1104_, lean_object* v_vals_1105_, lean_object* v_heq_1106_, lean_object* v_i_1107_, lean_object* v_entries_1108_){
_start:
{
size_t v_depth_boxed_1109_; lean_object* v_res_1110_; 
v_depth_boxed_1109_ = lean_unbox_usize(v_depth_1103_);
lean_dec(v_depth_1103_);
v_res_1110_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(v_00_u03b2_1102_, v_depth_boxed_1109_, v_keys_1104_, v_vals_1105_, v_heq_1106_, v_i_1107_, v_entries_1108_);
lean_dec_ref(v_vals_1105_);
lean_dec_ref(v_keys_1104_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1111_, lean_object* v_x_1112_, lean_object* v_x_1113_, lean_object* v_x_1114_, lean_object* v_x_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1112_, v_x_1113_, v_x_1114_, v_x_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0(lean_object* v_e_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1117_, v___y_1118_, v___y_1119_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0___boxed(lean_object* v_e_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0(v_e_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec(v___y_1132_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0(lean_object* v_e_1147_, lean_object* v___f_1148_, lean_object* v___f_1149_, lean_object* v_size_1150_, lean_object* v_s_1151_){
_start:
{
lean_object* v_denote_1152_; lean_object* v_vars_1153_; lean_object* v_varMap_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1163_; 
v_denote_1152_ = lean_ctor_get(v_s_1151_, 0);
v_vars_1153_ = lean_ctor_get(v_s_1151_, 1);
v_varMap_1154_ = lean_ctor_get(v_s_1151_, 2);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_s_1151_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1156_ = v_s_1151_;
v_isShared_1157_ = v_isSharedCheck_1163_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_varMap_1154_);
lean_inc(v_vars_1153_);
lean_inc(v_denote_1152_);
lean_dec(v_s_1151_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1163_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1161_; 
lean_inc_ref(v_e_1147_);
v___x_1158_ = l_Lean_PersistentArray_push___redArg(v_vars_1153_, v_e_1147_);
v___x_1159_ = l_Lean_PersistentHashMap_insert___redArg(v___f_1148_, v___f_1149_, v_varMap_1154_, v_e_1147_, v_size_1150_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 2, v___x_1159_);
lean_ctor_set(v___x_1156_, 1, v___x_1158_);
v___x_1161_ = v___x_1156_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_denote_1152_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v___x_1158_);
lean_ctor_set(v_reuseFailAlloc_1162_, 2, v___x_1159_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__1(lean_object* v_toPure_1164_, lean_object* v_size_1165_, lean_object* v_____r_1166_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_apply_2(v_toPure_1164_, lean_box(0), v_size_1165_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2(lean_object* v_e_1168_, lean_object* v_inst_1169_, lean_object* v_toBind_1170_, lean_object* v___f_1171_, lean_object* v_____r_1172_){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1173_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1174_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SolverExtension_markTerm___boxed), 14, 3);
lean_closure_set(v___x_1174_, 0, lean_box(0));
lean_closure_set(v___x_1174_, 1, v___x_1173_);
lean_closure_set(v___x_1174_, 2, v_e_1168_);
v___x_1175_ = lean_apply_2(v_inst_1169_, lean_box(0), v___x_1174_);
v___x_1176_ = lean_apply_4(v_toBind_1170_, lean_box(0), lean_box(0), v___x_1175_, v___f_1171_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3(lean_object* v_inst_1177_, lean_object* v_e_1178_, lean_object* v_toBind_1179_, lean_object* v___f_1180_, lean_object* v_____r_1181_){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = lean_apply_1(v_inst_1177_, v_e_1178_);
v___x_1183_ = lean_apply_4(v_toBind_1179_, lean_box(0), lean_box(0), v___x_1182_, v___f_1180_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4(lean_object* v___f_1184_, lean_object* v___f_1185_, lean_object* v_e_1186_, lean_object* v_toPure_1187_, lean_object* v_inst_1188_, lean_object* v_toBind_1189_, lean_object* v_inst_1190_, lean_object* v_modifySemiringState_1191_, lean_object* v_s_1192_){
_start:
{
lean_object* v_vars_1193_; lean_object* v_varMap_1194_; lean_object* v___x_1195_; 
v_vars_1193_ = lean_ctor_get(v_s_1192_, 1);
lean_inc_ref(v_vars_1193_);
v_varMap_1194_ = lean_ctor_get(v_s_1192_, 2);
lean_inc_ref(v_varMap_1194_);
lean_dec_ref(v_s_1192_);
lean_inc_ref(v_e_1186_);
lean_inc_ref(v___f_1185_);
lean_inc_ref(v___f_1184_);
v___x_1195_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_1184_, v___f_1185_, v_varMap_1194_, v_e_1186_);
lean_dec_ref(v_varMap_1194_);
if (lean_obj_tag(v___x_1195_) == 1)
{
lean_object* v_val_1196_; lean_object* v___x_1197_; 
lean_dec_ref(v_vars_1193_);
lean_dec(v_modifySemiringState_1191_);
lean_dec(v_inst_1190_);
lean_dec(v_toBind_1189_);
lean_dec(v_inst_1188_);
lean_dec_ref(v_e_1186_);
lean_dec_ref(v___f_1185_);
lean_dec_ref(v___f_1184_);
v_val_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc(v_val_1196_);
lean_dec_ref_known(v___x_1195_, 1);
v___x_1197_ = lean_apply_2(v_toPure_1187_, lean_box(0), v_val_1196_);
return v___x_1197_;
}
else
{
lean_object* v_size_1198_; lean_object* v___f_1199_; lean_object* v___f_1200_; lean_object* v___f_1201_; lean_object* v___f_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
lean_dec(v___x_1195_);
v_size_1198_ = lean_ctor_get(v_vars_1193_, 2);
lean_inc_n(v_size_1198_, 2);
lean_dec_ref(v_vars_1193_);
lean_inc_ref_n(v_e_1186_, 2);
v___f_1199_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1199_, 0, v_e_1186_);
lean_closure_set(v___f_1199_, 1, v___f_1184_);
lean_closure_set(v___f_1199_, 2, v___f_1185_);
lean_closure_set(v___f_1199_, 3, v_size_1198_);
v___f_1200_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1200_, 0, v_toPure_1187_);
lean_closure_set(v___f_1200_, 1, v_size_1198_);
lean_inc_n(v_toBind_1189_, 2);
v___f_1201_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1201_, 0, v_e_1186_);
lean_closure_set(v___f_1201_, 1, v_inst_1188_);
lean_closure_set(v___f_1201_, 2, v_toBind_1189_);
lean_closure_set(v___f_1201_, 3, v___f_1200_);
v___f_1202_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1202_, 0, v_inst_1190_);
lean_closure_set(v___f_1202_, 1, v_e_1186_);
lean_closure_set(v___f_1202_, 2, v_toBind_1189_);
lean_closure_set(v___f_1202_, 3, v___f_1201_);
v___x_1203_ = lean_apply_1(v_modifySemiringState_1191_, v___f_1199_);
v___x_1204_ = lean_apply_4(v_toBind_1189_, lean_box(0), lean_box(0), v___x_1203_, v___f_1202_);
return v___x_1204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(lean_object* v_inst_1207_, lean_object* v_inst_1208_, lean_object* v_inst_1209_, lean_object* v_inst_1210_, lean_object* v_e_1211_){
_start:
{
lean_object* v_toApplicative_1212_; lean_object* v_toBind_1213_; lean_object* v_getSemiringState_1214_; lean_object* v_modifySemiringState_1215_; lean_object* v_toPure_1216_; lean_object* v___f_1217_; lean_object* v___f_1218_; lean_object* v___f_1219_; lean_object* v___x_1220_; 
v_toApplicative_1212_ = lean_ctor_get(v_inst_1208_, 0);
lean_inc_ref(v_toApplicative_1212_);
v_toBind_1213_ = lean_ctor_get(v_inst_1208_, 1);
lean_inc_n(v_toBind_1213_, 2);
lean_dec_ref(v_inst_1208_);
v_getSemiringState_1214_ = lean_ctor_get(v_inst_1209_, 0);
lean_inc(v_getSemiringState_1214_);
v_modifySemiringState_1215_ = lean_ctor_get(v_inst_1209_, 1);
lean_inc(v_modifySemiringState_1215_);
lean_dec_ref(v_inst_1209_);
v_toPure_1216_ = lean_ctor_get(v_toApplicative_1212_, 1);
lean_inc(v_toPure_1216_);
lean_dec_ref(v_toApplicative_1212_);
v___f_1217_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0));
v___f_1218_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1));
v___f_1219_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4), 9, 8);
lean_closure_set(v___f_1219_, 0, v___f_1217_);
lean_closure_set(v___f_1219_, 1, v___f_1218_);
lean_closure_set(v___f_1219_, 2, v_e_1211_);
lean_closure_set(v___f_1219_, 3, v_toPure_1216_);
lean_closure_set(v___f_1219_, 4, v_inst_1207_);
lean_closure_set(v___f_1219_, 5, v_toBind_1213_);
lean_closure_set(v___f_1219_, 6, v_inst_1210_);
lean_closure_set(v___f_1219_, 7, v_modifySemiringState_1215_);
v___x_1220_ = lean_apply_4(v_toBind_1213_, lean_box(0), lean_box(0), v_getSemiringState_1214_, v___f_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore(lean_object* v_m_1221_, lean_object* v_inst_1222_, lean_object* v_inst_1223_, lean_object* v_inst_1224_, lean_object* v_inst_1225_, lean_object* v_e_1226_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(v_inst_1222_, v_inst_1223_, v_inst_1224_, v_inst_1225_, v_e_1226_);
return v___x_1227_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0___closed__0));
v___x_1230_ = l_Lean_stringToMessageData(v___x_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0(lean_object* v___x_1231_, lean_object* v___x_1232_, lean_object* v___f_1233_, lean_object* v___x_1234_, lean_object* v___f_1235_, lean_object* v_e_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_1236_, v___y_1238_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; uint8_t v___x_1251_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1250_);
lean_dec_ref_known(v___x_1249_, 1);
v___x_1251_ = lean_unbox(v_a_1250_);
lean_dec(v_a_1250_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1449__overap_1255_; lean_object* v___x_1256_; 
v___x_1252_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0___closed__1);
lean_inc_ref(v_e_1236_);
v___x_1253_ = l_Lean_indentExpr(v_e_1236_);
v___x_1254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1252_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
lean_inc_ref(v___x_1231_);
v___x_1449__overap_1255_ = l_Lean_throwError___redArg(v___x_1231_, v___x_1232_, v___x_1254_);
lean_inc(v___y_1247_);
lean_inc_ref(v___y_1246_);
lean_inc(v___y_1245_);
lean_inc_ref(v___y_1244_);
lean_inc(v___y_1243_);
lean_inc_ref(v___y_1242_);
lean_inc(v___y_1241_);
lean_inc_ref(v___y_1240_);
lean_inc(v___y_1239_);
lean_inc(v___y_1238_);
lean_inc(v___y_1237_);
v___x_1256_ = lean_apply_12(v___x_1449__overap_1255_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, lean_box(0));
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v___x_1452__overap_1257_; lean_object* v___x_1258_; 
lean_dec_ref_known(v___x_1256_, 1);
v___x_1452__overap_1257_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(v___f_1233_, v___x_1231_, v___x_1234_, v___f_1235_, v_e_1236_);
lean_inc(v___y_1247_);
lean_inc_ref(v___y_1246_);
lean_inc(v___y_1245_);
lean_inc_ref(v___y_1244_);
lean_inc(v___y_1243_);
lean_inc_ref(v___y_1242_);
lean_inc(v___y_1241_);
lean_inc_ref(v___y_1240_);
lean_inc(v___y_1239_);
lean_inc(v___y_1238_);
lean_inc(v___y_1237_);
v___x_1258_ = lean_apply_12(v___x_1452__overap_1257_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, lean_box(0));
return v___x_1258_;
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_dec_ref(v_e_1236_);
lean_dec_ref(v___f_1235_);
lean_dec_ref(v___x_1234_);
lean_dec(v___f_1233_);
lean_dec_ref(v___x_1231_);
v_a_1259_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1256_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1256_);
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
else
{
lean_object* v___x_1456__overap_1267_; lean_object* v___x_1268_; 
lean_dec_ref(v___x_1232_);
v___x_1456__overap_1267_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(v___f_1233_, v___x_1231_, v___x_1234_, v___f_1235_, v_e_1236_);
lean_inc(v___y_1247_);
lean_inc_ref(v___y_1246_);
lean_inc(v___y_1245_);
lean_inc_ref(v___y_1244_);
lean_inc(v___y_1243_);
lean_inc_ref(v___y_1242_);
lean_inc(v___y_1241_);
lean_inc_ref(v___y_1240_);
lean_inc(v___y_1239_);
lean_inc(v___y_1238_);
lean_inc(v___y_1237_);
v___x_1268_ = lean_apply_12(v___x_1456__overap_1267_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, lean_box(0));
return v___x_1268_;
}
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_dec_ref(v_e_1236_);
lean_dec_ref(v___f_1235_);
lean_dec_ref(v___x_1234_);
lean_dec(v___f_1233_);
lean_dec_ref(v___x_1232_);
lean_dec_ref(v___x_1231_);
v_a_1269_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1249_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1249_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0___boxed(lean_object** _args){
lean_object* v___x_1277_ = _args[0];
lean_object* v___x_1278_ = _args[1];
lean_object* v___f_1279_ = _args[2];
lean_object* v___x_1280_ = _args[3];
lean_object* v___f_1281_ = _args[4];
lean_object* v_e_1282_ = _args[5];
lean_object* v___y_1283_ = _args[6];
lean_object* v___y_1284_ = _args[7];
lean_object* v___y_1285_ = _args[8];
lean_object* v___y_1286_ = _args[9];
lean_object* v___y_1287_ = _args[10];
lean_object* v___y_1288_ = _args[11];
lean_object* v___y_1289_ = _args[12];
lean_object* v___y_1290_ = _args[13];
lean_object* v___y_1291_ = _args[14];
lean_object* v___y_1292_ = _args[15];
lean_object* v___y_1293_ = _args[16];
lean_object* v___y_1294_ = _args[17];
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0(v___x_1277_, v___x_1278_, v___f_1279_, v___x_1280_, v___f_1281_, v_e_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec(v___y_1283_);
return v_res_1295_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__0(void){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = l_instMonadEIO___redArg();
return v___x_1296_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__1(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__0);
v___x_1298_ = l_StateRefT_x27_instMonad___redArg(v___x_1297_);
return v___x_1298_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__7(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___f_1305_; 
v___x_1304_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_1305_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1305_, 0, v___x_1304_);
return v___f_1305_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__8(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___f_1307_; 
v___x_1306_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_1307_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1307_, 0, v___x_1306_);
return v___f_1307_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__9(void){
_start:
{
lean_object* v___f_1308_; lean_object* v___f_1309_; lean_object* v___x_1310_; 
v___f_1308_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__8, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__8_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__8);
v___f_1309_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__7, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__7_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__7);
v___x_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___f_1309_);
lean_ctor_set(v___x_1310_, 1, v___f_1308_);
return v___x_1310_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__10(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___f_1312_; 
v___x_1311_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__9, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__9_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__9);
v___f_1312_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1312_, 0, v___x_1311_);
return v___f_1312_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__11(void){
_start:
{
lean_object* v___x_1313_; lean_object* v___f_1314_; 
v___x_1313_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__9, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__9_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__9);
v___f_1314_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1314_, 0, v___x_1313_);
return v___f_1314_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__12(void){
_start:
{
lean_object* v___f_1315_; lean_object* v___f_1316_; lean_object* v___x_1317_; 
v___f_1315_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__11, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__11_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__11);
v___f_1316_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__10, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__10_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__10);
v___x_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___f_1316_);
lean_ctor_set(v___x_1317_, 1, v___f_1315_);
return v___x_1317_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__13(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___f_1319_; 
v___x_1318_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__12);
v___f_1319_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1319_, 0, v___x_1318_);
return v___f_1319_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__14(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___f_1321_; 
v___x_1320_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__12);
v___f_1321_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1321_, 0, v___x_1320_);
return v___f_1321_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__15(void){
_start:
{
lean_object* v___f_1322_; lean_object* v___f_1323_; lean_object* v___x_1324_; 
v___f_1322_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__14, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__14_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__14);
v___f_1323_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__13, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__13_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__13);
v___x_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___f_1323_);
lean_ctor_set(v___x_1324_, 1, v___f_1322_);
return v___x_1324_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__16(void){
_start:
{
lean_object* v___x_1325_; lean_object* v___f_1326_; 
v___x_1325_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__15, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__15_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__15);
v___f_1326_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1326_, 0, v___x_1325_);
return v___f_1326_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__17(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___f_1328_; 
v___x_1327_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__15, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__15_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__15);
v___f_1328_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1328_, 0, v___x_1327_);
return v___f_1328_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__18(void){
_start:
{
lean_object* v___f_1329_; lean_object* v___f_1330_; lean_object* v___x_1331_; 
v___f_1329_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__17, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__17_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__17);
v___f_1330_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__16, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__16_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__16);
v___x_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___f_1330_);
lean_ctor_set(v___x_1331_, 1, v___f_1329_);
return v___x_1331_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__19(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___f_1333_; 
v___x_1332_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__18, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__18_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__18);
v___f_1333_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1333_, 0, v___x_1332_);
return v___f_1333_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__20(void){
_start:
{
lean_object* v___x_1334_; lean_object* v___f_1335_; 
v___x_1334_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__18, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__18_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__18);
v___f_1335_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1335_, 0, v___x_1334_);
return v___f_1335_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__21(void){
_start:
{
lean_object* v___f_1336_; lean_object* v___f_1337_; lean_object* v___x_1338_; 
v___f_1336_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__20, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__20_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__20);
v___f_1337_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__19, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__19_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__19);
v___x_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1338_, 0, v___f_1337_);
lean_ctor_set(v___x_1338_, 1, v___f_1336_);
return v___x_1338_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__22(void){
_start:
{
lean_object* v___x_1339_; lean_object* v___f_1340_; 
v___x_1339_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__21, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__21_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__21);
v___f_1340_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1340_, 0, v___x_1339_);
return v___f_1340_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__23(void){
_start:
{
lean_object* v___x_1341_; lean_object* v___f_1342_; 
v___x_1341_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__21, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__21_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__21);
v___f_1342_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1342_, 0, v___x_1341_);
return v___f_1342_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__24(void){
_start:
{
lean_object* v___f_1343_; lean_object* v___f_1344_; lean_object* v___x_1345_; 
v___f_1343_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__23, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__23_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__23);
v___f_1344_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__22, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__22_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__22);
v___x_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___f_1344_);
lean_ctor_set(v___x_1345_, 1, v___f_1343_);
return v___x_1345_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__25(void){
_start:
{
lean_object* v___x_1346_; lean_object* v___f_1347_; 
v___x_1346_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__24, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__24_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__24);
v___f_1347_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1347_, 0, v___x_1346_);
return v___f_1347_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__26(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___f_1349_; 
v___x_1348_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__24, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__24_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__24);
v___f_1349_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1349_, 0, v___x_1348_);
return v___f_1349_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__27(void){
_start:
{
lean_object* v___f_1350_; lean_object* v___f_1351_; lean_object* v___x_1352_; 
v___f_1350_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__26, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__26_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__26);
v___f_1351_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__25, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__25_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__25);
v___x_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___f_1351_);
lean_ctor_set(v___x_1352_, 1, v___f_1350_);
return v___x_1352_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__28(void){
_start:
{
lean_object* v___x_1353_; lean_object* v___f_1354_; 
v___x_1353_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__27, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__27_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__27);
v___f_1354_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1354_, 0, v___x_1353_);
return v___f_1354_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__29(void){
_start:
{
lean_object* v___x_1355_; lean_object* v___f_1356_; 
v___x_1355_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__27, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__27_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__27);
v___f_1356_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1356_, 0, v___x_1355_);
return v___f_1356_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__30(void){
_start:
{
lean_object* v___f_1357_; lean_object* v___f_1358_; lean_object* v___x_1359_; 
v___f_1357_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__29, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__29_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__29);
v___f_1358_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__28, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__28_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__28);
v___x_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___f_1358_);
lean_ctor_set(v___x_1359_, 1, v___f_1357_);
return v___x_1359_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__31(void){
_start:
{
lean_object* v___x_1360_; lean_object* v___f_1361_; 
v___x_1360_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__30, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__30_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__30);
v___f_1361_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1361_, 0, v___x_1360_);
return v___f_1361_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__32(void){
_start:
{
lean_object* v___x_1362_; lean_object* v___f_1363_; 
v___x_1362_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__30, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__30_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__30);
v___f_1363_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1363_, 0, v___x_1362_);
return v___f_1363_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__33(void){
_start:
{
lean_object* v___f_1364_; lean_object* v___f_1365_; lean_object* v___x_1366_; 
v___f_1364_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__32, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__32_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__32);
v___f_1365_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__31, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__31_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__31);
v___x_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___f_1365_);
lean_ctor_set(v___x_1366_, 1, v___f_1364_);
return v___x_1366_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__37(void){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1370_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1371_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__36));
v___x_1372_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__35));
v___x_1373_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1372_, v___x_1371_, v___x_1370_);
return v___x_1373_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__38(void){
_start:
{
lean_object* v___x_1374_; lean_object* v___f_1375_; lean_object* v___f_1376_; lean_object* v___x_1377_; 
v___x_1374_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__37, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__37_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__37);
v___f_1375_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6));
v___f_1376_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__34));
v___x_1377_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1376_, v___f_1375_, v___x_1374_);
return v___x_1377_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__39(void){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1378_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__38, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__38_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__38);
v___x_1379_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__36));
v___x_1380_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__35));
v___x_1381_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1380_, v___x_1379_, v___x_1378_);
return v___x_1381_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__40(void){
_start:
{
lean_object* v___x_1382_; lean_object* v___f_1383_; lean_object* v___f_1384_; lean_object* v___x_1385_; 
v___x_1382_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__39, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__39_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__39);
v___f_1383_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6));
v___f_1384_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__34));
v___x_1385_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1384_, v___f_1383_, v___x_1382_);
return v___x_1385_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__41(void){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1386_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__40, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__40_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__40);
v___x_1387_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__36));
v___x_1388_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__35));
v___x_1389_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1388_, v___x_1387_, v___x_1386_);
return v___x_1389_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__42(void){
_start:
{
lean_object* v___x_1390_; lean_object* v___f_1391_; lean_object* v___f_1392_; lean_object* v___x_1393_; 
v___x_1390_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__41, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__41_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__41);
v___f_1391_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6));
v___f_1392_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__34));
v___x_1393_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1392_, v___f_1391_, v___x_1390_);
return v___x_1393_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__43(void){
_start:
{
lean_object* v___x_1394_; lean_object* v___f_1395_; lean_object* v___f_1396_; lean_object* v___x_1397_; 
v___x_1394_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__42, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__42_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__42);
v___f_1395_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6));
v___f_1396_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__34));
v___x_1397_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1396_, v___f_1395_, v___x_1394_);
return v___x_1397_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__44(void){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1398_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__43, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__43_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__43);
v___x_1399_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__36));
v___x_1400_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__35));
v___x_1401_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1400_, v___x_1399_, v___x_1398_);
return v___x_1401_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__45(void){
_start:
{
lean_object* v___x_1402_; lean_object* v___f_1403_; lean_object* v___f_1404_; lean_object* v___x_1405_; 
v___x_1402_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__44, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__44_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__44);
v___f_1403_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6));
v___f_1404_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__34));
v___x_1405_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1404_, v___f_1403_, v___x_1402_);
return v___x_1405_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__48(void){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___f_1412_; 
v___x_1410_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__36));
v___x_1411_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_1412_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1412_, 0, v___x_1411_);
lean_closure_set(v___f_1412_, 1, v___x_1410_);
return v___f_1412_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__49(void){
_start:
{
lean_object* v___f_1413_; lean_object* v___f_1414_; lean_object* v___f_1415_; 
v___f_1413_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6));
v___f_1414_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__48, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__48_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__48);
v___f_1415_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1415_, 0, v___f_1414_);
lean_closure_set(v___f_1415_, 1, v___f_1413_);
return v___f_1415_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__50(void){
_start:
{
lean_object* v___x_1416_; lean_object* v___f_1417_; lean_object* v___f_1418_; 
v___x_1416_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__36));
v___f_1417_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__49, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__49_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__49);
v___f_1418_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1418_, 0, v___f_1417_);
lean_closure_set(v___f_1418_, 1, v___x_1416_);
return v___f_1418_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__51(void){
_start:
{
lean_object* v___f_1419_; lean_object* v___f_1420_; lean_object* v___f_1421_; 
v___f_1419_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6));
v___f_1420_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__50, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__50_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__50);
v___f_1421_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1421_, 0, v___f_1420_);
lean_closure_set(v___f_1421_, 1, v___f_1419_);
return v___f_1421_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__52(void){
_start:
{
lean_object* v___f_1422_; lean_object* v___f_1423_; lean_object* v___f_1424_; 
v___f_1422_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6));
v___f_1423_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__51, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__51_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__51);
v___f_1424_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1424_, 0, v___f_1423_);
lean_closure_set(v___f_1424_, 1, v___f_1422_);
return v___f_1424_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__53(void){
_start:
{
lean_object* v___x_1425_; lean_object* v___f_1426_; lean_object* v___f_1427_; 
v___x_1425_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__36));
v___f_1426_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__52, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__52_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__52);
v___f_1427_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1427_, 0, v___f_1426_);
lean_closure_set(v___f_1427_, 1, v___x_1425_);
return v___f_1427_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__54(void){
_start:
{
lean_object* v___f_1428_; lean_object* v___f_1429_; lean_object* v___f_1430_; 
v___f_1428_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6));
v___f_1429_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__53, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__53_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__53);
v___f_1430_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1430_, 0, v___f_1429_);
lean_closure_set(v___f_1430_, 1, v___f_1428_);
return v___f_1430_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM(void){
_start:
{
lean_object* v___x_1431_; lean_object* v_toApplicative_1432_; lean_object* v_toFunctor_1433_; lean_object* v_toSeq_1434_; lean_object* v_toSeqLeft_1435_; lean_object* v_toSeqRight_1436_; lean_object* v___f_1437_; lean_object* v___f_1438_; lean_object* v___f_1439_; lean_object* v___f_1440_; lean_object* v___x_1441_; lean_object* v___f_1442_; lean_object* v___f_1443_; lean_object* v___f_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v_toApplicative_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1492_; 
v___x_1431_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__1);
v_toApplicative_1432_ = lean_ctor_get(v___x_1431_, 0);
v_toFunctor_1433_ = lean_ctor_get(v_toApplicative_1432_, 0);
v_toSeq_1434_ = lean_ctor_get(v_toApplicative_1432_, 2);
v_toSeqLeft_1435_ = lean_ctor_get(v_toApplicative_1432_, 3);
v_toSeqRight_1436_ = lean_ctor_get(v_toApplicative_1432_, 4);
v___f_1437_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__2));
v___f_1438_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__3));
lean_inc_ref_n(v_toFunctor_1433_, 2);
v___f_1439_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1439_, 0, v_toFunctor_1433_);
v___f_1440_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1440_, 0, v_toFunctor_1433_);
v___x_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___f_1439_);
lean_ctor_set(v___x_1441_, 1, v___f_1440_);
lean_inc(v_toSeqRight_1436_);
v___f_1442_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1442_, 0, v_toSeqRight_1436_);
lean_inc(v_toSeqLeft_1435_);
v___f_1443_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1443_, 0, v_toSeqLeft_1435_);
lean_inc(v_toSeq_1434_);
v___f_1444_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1444_, 0, v_toSeq_1434_);
v___x_1445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1441_);
lean_ctor_set(v___x_1445_, 1, v___f_1437_);
lean_ctor_set(v___x_1445_, 2, v___f_1444_);
lean_ctor_set(v___x_1445_, 3, v___f_1443_);
lean_ctor_set(v___x_1445_, 4, v___f_1442_);
v___x_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
lean_ctor_set(v___x_1446_, 1, v___f_1438_);
v___x_1447_ = l_StateRefT_x27_instMonad___redArg(v___x_1446_);
v_toApplicative_1448_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1492_ == 0)
{
lean_object* v_unused_1493_; 
v_unused_1493_ = lean_ctor_get(v___x_1447_, 1);
lean_dec(v_unused_1493_);
v___x_1450_ = v___x_1447_;
v_isShared_1451_ = v_isSharedCheck_1492_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_toApplicative_1448_);
lean_dec(v___x_1447_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1492_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v_toFunctor_1452_; lean_object* v_toSeq_1453_; lean_object* v_toSeqLeft_1454_; lean_object* v_toSeqRight_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1490_; 
v_toFunctor_1452_ = lean_ctor_get(v_toApplicative_1448_, 0);
v_toSeq_1453_ = lean_ctor_get(v_toApplicative_1448_, 2);
v_toSeqLeft_1454_ = lean_ctor_get(v_toApplicative_1448_, 3);
v_toSeqRight_1455_ = lean_ctor_get(v_toApplicative_1448_, 4);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_toApplicative_1448_);
if (v_isSharedCheck_1490_ == 0)
{
lean_object* v_unused_1491_; 
v_unused_1491_ = lean_ctor_get(v_toApplicative_1448_, 1);
lean_dec(v_unused_1491_);
v___x_1457_ = v_toApplicative_1448_;
v_isShared_1458_ = v_isSharedCheck_1490_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_toSeqRight_1455_);
lean_inc(v_toSeqLeft_1454_);
lean_inc(v_toSeq_1453_);
lean_inc(v_toFunctor_1452_);
lean_dec(v_toApplicative_1448_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1490_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___f_1459_; lean_object* v___f_1460_; lean_object* v___f_1461_; lean_object* v___f_1462_; lean_object* v___x_1463_; lean_object* v___f_1464_; lean_object* v___f_1465_; lean_object* v___f_1466_; lean_object* v___x_1468_; 
v___f_1459_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__4));
v___f_1460_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__5));
lean_inc_ref(v_toFunctor_1452_);
v___f_1461_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1461_, 0, v_toFunctor_1452_);
v___f_1462_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1462_, 0, v_toFunctor_1452_);
v___x_1463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___f_1461_);
lean_ctor_set(v___x_1463_, 1, v___f_1462_);
v___f_1464_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1464_, 0, v_toSeqRight_1455_);
v___f_1465_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1465_, 0, v_toSeqLeft_1454_);
v___f_1466_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1466_, 0, v_toSeq_1453_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 4, v___f_1464_);
lean_ctor_set(v___x_1457_, 3, v___f_1465_);
lean_ctor_set(v___x_1457_, 2, v___f_1466_);
lean_ctor_set(v___x_1457_, 1, v___f_1459_);
lean_ctor_set(v___x_1457_, 0, v___x_1463_);
v___x_1468_ = v___x_1457_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1463_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v___f_1459_);
lean_ctor_set(v_reuseFailAlloc_1489_, 2, v___f_1466_);
lean_ctor_set(v_reuseFailAlloc_1489_, 3, v___f_1465_);
lean_ctor_set(v_reuseFailAlloc_1489_, 4, v___f_1464_);
v___x_1468_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
lean_object* v___x_1470_; 
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 1, v___f_1460_);
lean_ctor_set(v___x_1450_, 0, v___x_1468_);
v___x_1470_ = v___x_1450_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1468_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v___f_1460_);
v___x_1470_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v_toMonadRef_1481_; lean_object* v___f_1482_; lean_object* v___f_1483_; lean_object* v___f_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___f_1487_; 
v___x_1471_ = l_StateRefT_x27_instMonad___redArg(v___x_1470_);
v___x_1472_ = l_ReaderT_instMonad___redArg(v___x_1471_);
v___x_1473_ = l_StateRefT_x27_instMonad___redArg(v___x_1472_);
v___x_1474_ = l_ReaderT_instMonad___redArg(v___x_1473_);
v___x_1475_ = l_ReaderT_instMonad___redArg(v___x_1474_);
v___x_1476_ = l_StateRefT_x27_instMonad___redArg(v___x_1475_);
v___x_1477_ = l_ReaderT_instMonad___redArg(v___x_1476_);
v___x_1478_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM;
v___x_1479_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__33, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__33_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__33);
v___x_1480_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__45, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__45_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__45);
v_toMonadRef_1481_ = lean_ctor_get(v___x_1480_, 0);
v___f_1482_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__47));
v___f_1483_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___closed__0));
v___f_1484_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__54, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__54_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__54);
lean_inc_ref(v___x_1477_);
v___x_1485_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1484_, v___x_1477_);
lean_inc_ref(v_toMonadRef_1481_);
v___x_1486_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1479_);
lean_ctor_set(v___x_1486_, 1, v_toMonadRef_1481_);
lean_ctor_set(v___x_1486_, 2, v___x_1485_);
v___f_1487_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0___boxed), 18, 5);
lean_closure_set(v___f_1487_, 0, v___x_1477_);
lean_closure_set(v___f_1487_, 1, v___x_1486_);
lean_closure_set(v___f_1487_, 2, v___f_1482_);
lean_closure_set(v___f_1487_, 3, v___x_1478_);
lean_closure_set(v___f_1487_, 4, v___f_1483_);
return v___f_1487_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__1(lean_object* v_a_1494_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = lean_nat_to_int(v_a_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0(lean_object* v___y_1496_, lean_object* v_a_1497_, lean_object* v_s_1498_){
_start:
{
lean_object* v_exp_1499_; lean_object* v_rings_1500_; lean_object* v_semirings_1501_; lean_object* v_ncRings_1502_; lean_object* v_ncSemirings_1503_; lean_object* v_typeClassify_1504_; lean_object* v_orders_1505_; lean_object* v_typeOrderClassify_1506_; lean_object* v___x_1507_; uint8_t v___x_1508_; 
v_exp_1499_ = lean_ctor_get(v_s_1498_, 0);
v_rings_1500_ = lean_ctor_get(v_s_1498_, 1);
v_semirings_1501_ = lean_ctor_get(v_s_1498_, 2);
v_ncRings_1502_ = lean_ctor_get(v_s_1498_, 3);
v_ncSemirings_1503_ = lean_ctor_get(v_s_1498_, 4);
v_typeClassify_1504_ = lean_ctor_get(v_s_1498_, 5);
v_orders_1505_ = lean_ctor_get(v_s_1498_, 6);
v_typeOrderClassify_1506_ = lean_ctor_get(v_s_1498_, 7);
v___x_1507_ = lean_array_get_size(v_semirings_1501_);
v___x_1508_ = lean_nat_dec_lt(v___y_1496_, v___x_1507_);
if (v___x_1508_ == 0)
{
lean_dec_ref(v_a_1497_);
return v_s_1498_;
}
else
{
lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1532_; 
lean_inc_ref(v_typeOrderClassify_1506_);
lean_inc_ref(v_orders_1505_);
lean_inc_ref(v_typeClassify_1504_);
lean_inc_ref(v_ncSemirings_1503_);
lean_inc_ref(v_ncRings_1502_);
lean_inc_ref(v_semirings_1501_);
lean_inc_ref(v_rings_1500_);
lean_inc(v_exp_1499_);
v_isSharedCheck_1532_ = !lean_is_exclusive(v_s_1498_);
if (v_isSharedCheck_1532_ == 0)
{
lean_object* v_unused_1533_; lean_object* v_unused_1534_; lean_object* v_unused_1535_; lean_object* v_unused_1536_; lean_object* v_unused_1537_; lean_object* v_unused_1538_; lean_object* v_unused_1539_; lean_object* v_unused_1540_; 
v_unused_1533_ = lean_ctor_get(v_s_1498_, 7);
lean_dec(v_unused_1533_);
v_unused_1534_ = lean_ctor_get(v_s_1498_, 6);
lean_dec(v_unused_1534_);
v_unused_1535_ = lean_ctor_get(v_s_1498_, 5);
lean_dec(v_unused_1535_);
v_unused_1536_ = lean_ctor_get(v_s_1498_, 4);
lean_dec(v_unused_1536_);
v_unused_1537_ = lean_ctor_get(v_s_1498_, 3);
lean_dec(v_unused_1537_);
v_unused_1538_ = lean_ctor_get(v_s_1498_, 2);
lean_dec(v_unused_1538_);
v_unused_1539_ = lean_ctor_get(v_s_1498_, 1);
lean_dec(v_unused_1539_);
v_unused_1540_ = lean_ctor_get(v_s_1498_, 0);
lean_dec(v_unused_1540_);
v___x_1510_ = v_s_1498_;
v_isShared_1511_ = v_isSharedCheck_1532_;
goto v_resetjp_1509_;
}
else
{
lean_dec(v_s_1498_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1532_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v_v_1512_; lean_object* v_toSemiring_1513_; lean_object* v_ringId_1514_; lean_object* v_commSemiringInst_1515_; lean_object* v_addRightCancelInst_x3f_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1530_; 
v_v_1512_ = lean_array_fget(v_semirings_1501_, v___y_1496_);
v_toSemiring_1513_ = lean_ctor_get(v_v_1512_, 0);
v_ringId_1514_ = lean_ctor_get(v_v_1512_, 1);
v_commSemiringInst_1515_ = lean_ctor_get(v_v_1512_, 2);
v_addRightCancelInst_x3f_1516_ = lean_ctor_get(v_v_1512_, 3);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_v_1512_);
if (v_isSharedCheck_1530_ == 0)
{
lean_object* v_unused_1531_; 
v_unused_1531_ = lean_ctor_get(v_v_1512_, 4);
lean_dec(v_unused_1531_);
v___x_1518_ = v_v_1512_;
v_isShared_1519_ = v_isSharedCheck_1530_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_addRightCancelInst_x3f_1516_);
lean_inc(v_commSemiringInst_1515_);
lean_inc(v_ringId_1514_);
lean_inc(v_toSemiring_1513_);
lean_dec(v_v_1512_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1530_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1520_; lean_object* v_xs_x27_1521_; lean_object* v___x_1522_; lean_object* v___x_1524_; 
v___x_1520_ = lean_box(0);
v_xs_x27_1521_ = lean_array_fset(v_semirings_1501_, v___y_1496_, v___x_1520_);
v___x_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1522_, 0, v_a_1497_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 4, v___x_1522_);
v___x_1524_ = v___x_1518_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_toSemiring_1513_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_ringId_1514_);
lean_ctor_set(v_reuseFailAlloc_1529_, 2, v_commSemiringInst_1515_);
lean_ctor_set(v_reuseFailAlloc_1529_, 3, v_addRightCancelInst_x3f_1516_);
lean_ctor_set(v_reuseFailAlloc_1529_, 4, v___x_1522_);
v___x_1524_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
lean_object* v___x_1525_; lean_object* v___x_1527_; 
v___x_1525_ = lean_array_fset(v_xs_x27_1521_, v___y_1496_, v___x_1524_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 2, v___x_1525_);
v___x_1527_ = v___x_1510_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_exp_1499_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_rings_1500_);
lean_ctor_set(v_reuseFailAlloc_1528_, 2, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1528_, 3, v_ncRings_1502_);
lean_ctor_set(v_reuseFailAlloc_1528_, 4, v_ncSemirings_1503_);
lean_ctor_set(v_reuseFailAlloc_1528_, 5, v_typeClassify_1504_);
lean_ctor_set(v_reuseFailAlloc_1528_, 6, v_orders_1505_);
lean_ctor_set(v_reuseFailAlloc_1528_, 7, v_typeOrderClassify_1506_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0___boxed(lean_object* v___y_1541_, lean_object* v_a_1542_, lean_object* v_s_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0(v___y_1541_, v_a_1542_, v_s_1543_);
lean_dec(v___y_1541_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v___y_1569_; lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1612_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1593_ = v___x_1590_;
v_isShared_1594_ = v_isSharedCheck_1612_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1590_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1612_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v_toQFn_x3f_1595_; 
v_toQFn_x3f_1595_ = lean_ctor_get(v_a_1591_, 4);
if (lean_obj_tag(v_toQFn_x3f_1595_) == 1)
{
lean_object* v_val_1596_; lean_object* v___x_1598_; 
lean_inc_ref(v_toQFn_x3f_1595_);
lean_dec(v_a_1591_);
v_val_1596_ = lean_ctor_get(v_toQFn_x3f_1595_, 0);
lean_inc(v_val_1596_);
lean_dec_ref_known(v_toQFn_x3f_1595_, 1);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 0, v_val_1596_);
v___x_1598_ = v___x_1593_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_val_1596_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
else
{
lean_object* v_toSemiring_1600_; lean_object* v_type_1601_; lean_object* v_u_1602_; lean_object* v_semiringInst_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
lean_del_object(v___x_1593_);
v_toSemiring_1600_ = lean_ctor_get(v_a_1591_, 0);
lean_inc_ref(v_toSemiring_1600_);
lean_dec(v_a_1591_);
v_type_1601_ = lean_ctor_get(v_toSemiring_1600_, 1);
lean_inc_ref(v_type_1601_);
v_u_1602_ = lean_ctor_get(v_toSemiring_1600_, 2);
lean_inc(v_u_1602_);
v_semiringInst_1603_ = lean_ctor_get(v_toSemiring_1600_, 3);
lean_inc_ref(v_semiringInst_1603_);
lean_dec_ref(v_toSemiring_1600_);
v___x_1604_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__5));
v___x_1605_ = lean_box(0);
v___x_1606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1606_, 0, v_u_1602_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
v___x_1607_ = l_Lean_mkConst(v___x_1604_, v___x_1606_);
v___x_1608_ = l_Lean_mkAppB(v___x_1607_, v_type_1601_, v_semiringInst_1603_);
v___x_1609_ = l_Lean_Meta_Sym_canon(v___x_1608_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1611_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref_known(v___x_1609_, 1);
v___x_1611_ = l_Lean_Meta_Sym_shareCommon(v_a_1610_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
v___y_1569_ = v___x_1611_;
goto v___jp_1568_;
}
else
{
v___y_1569_ = v___x_1609_;
goto v___jp_1568_;
}
}
}
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
v_a_1613_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1590_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1590_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
v___jp_1568_:
{
if (lean_obj_tag(v___y_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___f_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v_a_1570_ = lean_ctor_get(v___y_1569_, 0);
lean_inc_n(v_a_1570_, 2);
lean_dec_ref_known(v___y_1569_, 1);
lean_inc(v___y_1556_);
v___f_1571_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1571_, 0, v___y_1556_);
lean_closure_set(v___f_1571_, 1, v_a_1570_);
v___x_1572_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_1573_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_1572_, v___f_1571_, v___y_1562_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1580_ == 0)
{
lean_object* v_unused_1581_; 
v_unused_1581_ = lean_ctor_get(v___x_1573_, 0);
lean_dec(v_unused_1581_);
v___x_1575_ = v___x_1573_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_dec(v___x_1573_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v_a_1570_);
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1570_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec(v_a_1570_);
v_a_1582_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1573_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1573_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
else
{
return v___y_1569_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___boxed(lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec(v___y_1621_);
return v_res_1633_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6___closed__0(void){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6(lean_object* v_msg_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v___x_1648_; lean_object* v___f_1649_; lean_object* v___x_41156__overap_1650_; lean_object* v___x_1651_; 
v___x_1648_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6___closed__0);
v___f_1649_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1649_, 0, v___x_1648_);
v___x_41156__overap_1650_ = lean_panic_fn_borrowed(v___f_1649_, v_msg_1635_);
lean_dec_ref(v___f_1649_);
lean_inc(v___y_1646_);
lean_inc_ref(v___y_1645_);
lean_inc(v___y_1644_);
lean_inc_ref(v___y_1643_);
lean_inc(v___y_1642_);
lean_inc_ref(v___y_1641_);
lean_inc(v___y_1640_);
lean_inc_ref(v___y_1639_);
lean_inc(v___y_1638_);
lean_inc(v___y_1637_);
lean_inc(v___y_1636_);
v___x_1651_ = lean_apply_12(v___x_41156__overap_1650_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, lean_box(0));
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6___boxed(lean_object* v_msg_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6(v_msg_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec(v___y_1653_);
return v_res_1665_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg___closed__0));
v___x_1668_ = l_Lean_stringToMessageData(v___x_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg(lean_object* v_type_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v___x_1676_; 
lean_inc_ref(v_type_1669_);
v___x_1676_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1689_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1679_ = v___x_1676_;
v_isShared_1680_ = v_isSharedCheck_1689_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1676_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1689_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
if (lean_obj_tag(v_a_1677_) == 1)
{
lean_object* v_val_1681_; lean_object* v___x_1683_; 
lean_dec_ref(v_type_1669_);
v_val_1681_ = lean_ctor_get(v_a_1677_, 0);
lean_inc(v_val_1681_);
lean_dec_ref_known(v_a_1677_, 1);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 0, v_val_1681_);
v___x_1683_ = v___x_1679_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_val_1681_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
else
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
lean_del_object(v___x_1679_);
lean_dec(v_a_1677_);
v___x_1685_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg___closed__1, &l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg___closed__1_once, _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg___closed__1);
v___x_1686_ = l_Lean_indentExpr(v_type_1669_);
v___x_1687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1685_);
lean_ctor_set(v___x_1687_, 1, v___x_1686_);
v___x_1688_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v___x_1687_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
return v___x_1688_;
}
}
}
else
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
lean_dec_ref(v_type_1669_);
v_a_1690_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1676_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1676_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_type_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg(v_type_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__4(lean_object* v_type_1706_, lean_object* v_u_1707_, lean_object* v_instDeclName_1708_, lean_object* v_declName_1709_, lean_object* v_expectedInst_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1723_ = lean_box(0);
v___x_1724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1724_, 0, v_u_1707_);
lean_ctor_set(v___x_1724_, 1, v___x_1723_);
lean_inc_ref(v___x_1724_);
v___x_1725_ = l_Lean_mkConst(v_instDeclName_1708_, v___x_1724_);
lean_inc_ref(v_type_1706_);
v___x_1726_ = l_Lean_Expr_app___override(v___x_1725_, v_type_1706_);
v___x_1727_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg(v___x_1726_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___x_1729_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc_n(v_a_1728_, 2);
lean_dec_ref_known(v___x_1727_, 1);
lean_inc(v_declName_1709_);
v___x_1729_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v_declName_1709_, v_a_1728_, v_expectedInst_1710_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
lean_dec_ref_known(v___x_1729_, 1);
v___x_1730_ = l_Lean_mkConst(v_declName_1709_, v___x_1724_);
v___x_1731_ = l_Lean_mkAppB(v___x_1730_, v_type_1706_, v_a_1728_);
v___x_1732_ = l_Lean_Meta_Sym_canon(v___x_1731_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_a_1733_; lean_object* v___x_1734_; 
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_a_1733_);
lean_dec_ref_known(v___x_1732_, 1);
v___x_1734_ = l_Lean_Meta_Sym_shareCommon(v_a_1733_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
return v___x_1734_;
}
else
{
return v___x_1732_;
}
}
else
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
lean_dec(v_a_1728_);
lean_dec_ref_known(v___x_1724_, 2);
lean_dec(v_declName_1709_);
lean_dec_ref(v_type_1706_);
v_a_1735_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1729_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1729_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1735_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1724_, 2);
lean_dec_ref(v_expectedInst_1710_);
lean_dec(v_declName_1709_);
lean_dec_ref(v_type_1706_);
return v___x_1727_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__4___boxed(lean_object** _args){
lean_object* v_type_1743_ = _args[0];
lean_object* v_u_1744_ = _args[1];
lean_object* v_instDeclName_1745_ = _args[2];
lean_object* v_declName_1746_ = _args[3];
lean_object* v_expectedInst_1747_ = _args[4];
lean_object* v___y_1748_ = _args[5];
lean_object* v___y_1749_ = _args[6];
lean_object* v___y_1750_ = _args[7];
lean_object* v___y_1751_ = _args[8];
lean_object* v___y_1752_ = _args[9];
lean_object* v___y_1753_ = _args[10];
lean_object* v___y_1754_ = _args[11];
lean_object* v___y_1755_ = _args[12];
lean_object* v___y_1756_ = _args[13];
lean_object* v___y_1757_ = _args[14];
lean_object* v___y_1758_ = _args[15];
lean_object* v___y_1759_ = _args[16];
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__4(v_type_1743_, v_u_1744_, v_instDeclName_1745_, v_declName_1746_, v_expectedInst_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec(v___y_1748_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___lam__0(lean_object* v_a_1761_, lean_object* v_s_1762_){
_start:
{
lean_object* v_toRing_1763_; lean_object* v_invFn_x3f_1764_; lean_object* v_divFn_x3f_1765_; lean_object* v_semiringId_x3f_1766_; lean_object* v_commSemiringInst_1767_; lean_object* v_commRingInst_1768_; lean_object* v_noZeroDivInst_x3f_1769_; lean_object* v_fieldInst_x3f_1770_; lean_object* v_powIdentityInst_x3f_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1802_; 
v_toRing_1763_ = lean_ctor_get(v_s_1762_, 0);
v_invFn_x3f_1764_ = lean_ctor_get(v_s_1762_, 1);
v_divFn_x3f_1765_ = lean_ctor_get(v_s_1762_, 2);
v_semiringId_x3f_1766_ = lean_ctor_get(v_s_1762_, 3);
v_commSemiringInst_1767_ = lean_ctor_get(v_s_1762_, 4);
v_commRingInst_1768_ = lean_ctor_get(v_s_1762_, 5);
v_noZeroDivInst_x3f_1769_ = lean_ctor_get(v_s_1762_, 6);
v_fieldInst_x3f_1770_ = lean_ctor_get(v_s_1762_, 7);
v_powIdentityInst_x3f_1771_ = lean_ctor_get(v_s_1762_, 8);
v_isSharedCheck_1802_ = !lean_is_exclusive(v_s_1762_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1773_ = v_s_1762_;
v_isShared_1774_ = v_isSharedCheck_1802_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_powIdentityInst_x3f_1771_);
lean_inc(v_fieldInst_x3f_1770_);
lean_inc(v_noZeroDivInst_x3f_1769_);
lean_inc(v_commRingInst_1768_);
lean_inc(v_commSemiringInst_1767_);
lean_inc(v_semiringId_x3f_1766_);
lean_inc(v_divFn_x3f_1765_);
lean_inc(v_invFn_x3f_1764_);
lean_inc(v_toRing_1763_);
lean_dec(v_s_1762_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1802_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v_id_1775_; lean_object* v_type_1776_; lean_object* v_u_1777_; lean_object* v_ringInst_1778_; lean_object* v_semiringInst_1779_; lean_object* v_charInst_x3f_1780_; lean_object* v_addFn_x3f_1781_; lean_object* v_mulFn_x3f_1782_; lean_object* v_subFn_x3f_1783_; lean_object* v_powFn_x3f_1784_; lean_object* v_intCastFn_x3f_1785_; lean_object* v_natCastFn_x3f_1786_; lean_object* v_natSMulFn_x3f_1787_; lean_object* v_intSMulFn_x3f_1788_; lean_object* v_one_x3f_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1800_; 
v_id_1775_ = lean_ctor_get(v_toRing_1763_, 0);
v_type_1776_ = lean_ctor_get(v_toRing_1763_, 1);
v_u_1777_ = lean_ctor_get(v_toRing_1763_, 2);
v_ringInst_1778_ = lean_ctor_get(v_toRing_1763_, 3);
v_semiringInst_1779_ = lean_ctor_get(v_toRing_1763_, 4);
v_charInst_x3f_1780_ = lean_ctor_get(v_toRing_1763_, 5);
v_addFn_x3f_1781_ = lean_ctor_get(v_toRing_1763_, 6);
v_mulFn_x3f_1782_ = lean_ctor_get(v_toRing_1763_, 7);
v_subFn_x3f_1783_ = lean_ctor_get(v_toRing_1763_, 8);
v_powFn_x3f_1784_ = lean_ctor_get(v_toRing_1763_, 10);
v_intCastFn_x3f_1785_ = lean_ctor_get(v_toRing_1763_, 11);
v_natCastFn_x3f_1786_ = lean_ctor_get(v_toRing_1763_, 12);
v_natSMulFn_x3f_1787_ = lean_ctor_get(v_toRing_1763_, 13);
v_intSMulFn_x3f_1788_ = lean_ctor_get(v_toRing_1763_, 14);
v_one_x3f_1789_ = lean_ctor_get(v_toRing_1763_, 15);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_toRing_1763_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; 
v_unused_1801_ = lean_ctor_get(v_toRing_1763_, 9);
lean_dec(v_unused_1801_);
v___x_1791_ = v_toRing_1763_;
v_isShared_1792_ = v_isSharedCheck_1800_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_one_x3f_1789_);
lean_inc(v_intSMulFn_x3f_1788_);
lean_inc(v_natSMulFn_x3f_1787_);
lean_inc(v_natCastFn_x3f_1786_);
lean_inc(v_intCastFn_x3f_1785_);
lean_inc(v_powFn_x3f_1784_);
lean_inc(v_subFn_x3f_1783_);
lean_inc(v_mulFn_x3f_1782_);
lean_inc(v_addFn_x3f_1781_);
lean_inc(v_charInst_x3f_1780_);
lean_inc(v_semiringInst_1779_);
lean_inc(v_ringInst_1778_);
lean_inc(v_u_1777_);
lean_inc(v_type_1776_);
lean_inc(v_id_1775_);
lean_dec(v_toRing_1763_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1800_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1793_; lean_object* v___x_1795_; 
v___x_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1793_, 0, v_a_1761_);
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 9, v___x_1793_);
v___x_1795_ = v___x_1791_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_id_1775_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v_type_1776_);
lean_ctor_set(v_reuseFailAlloc_1799_, 2, v_u_1777_);
lean_ctor_set(v_reuseFailAlloc_1799_, 3, v_ringInst_1778_);
lean_ctor_set(v_reuseFailAlloc_1799_, 4, v_semiringInst_1779_);
lean_ctor_set(v_reuseFailAlloc_1799_, 5, v_charInst_x3f_1780_);
lean_ctor_set(v_reuseFailAlloc_1799_, 6, v_addFn_x3f_1781_);
lean_ctor_set(v_reuseFailAlloc_1799_, 7, v_mulFn_x3f_1782_);
lean_ctor_set(v_reuseFailAlloc_1799_, 8, v_subFn_x3f_1783_);
lean_ctor_set(v_reuseFailAlloc_1799_, 9, v___x_1793_);
lean_ctor_set(v_reuseFailAlloc_1799_, 10, v_powFn_x3f_1784_);
lean_ctor_set(v_reuseFailAlloc_1799_, 11, v_intCastFn_x3f_1785_);
lean_ctor_set(v_reuseFailAlloc_1799_, 12, v_natCastFn_x3f_1786_);
lean_ctor_set(v_reuseFailAlloc_1799_, 13, v_natSMulFn_x3f_1787_);
lean_ctor_set(v_reuseFailAlloc_1799_, 14, v_intSMulFn_x3f_1788_);
lean_ctor_set(v_reuseFailAlloc_1799_, 15, v_one_x3f_1789_);
v___x_1795_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
lean_object* v___x_1797_; 
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v___x_1795_);
v___x_1797_ = v___x_1773_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1795_);
lean_ctor_set(v_reuseFailAlloc_1798_, 1, v_invFn_x3f_1764_);
lean_ctor_set(v_reuseFailAlloc_1798_, 2, v_divFn_x3f_1765_);
lean_ctor_set(v_reuseFailAlloc_1798_, 3, v_semiringId_x3f_1766_);
lean_ctor_set(v_reuseFailAlloc_1798_, 4, v_commSemiringInst_1767_);
lean_ctor_set(v_reuseFailAlloc_1798_, 5, v_commRingInst_1768_);
lean_ctor_set(v_reuseFailAlloc_1798_, 6, v_noZeroDivInst_x3f_1769_);
lean_ctor_set(v_reuseFailAlloc_1798_, 7, v_fieldInst_x3f_1770_);
lean_ctor_set(v_reuseFailAlloc_1798_, 8, v_powIdentityInst_x3f_1771_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1869_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1831_ = v___x_1828_;
v_isShared_1832_ = v_isSharedCheck_1869_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1828_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1869_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v_toRing_1833_; lean_object* v_negFn_x3f_1834_; 
v_toRing_1833_ = lean_ctor_get(v_a_1829_, 0);
lean_inc_ref(v_toRing_1833_);
lean_dec(v_a_1829_);
v_negFn_x3f_1834_ = lean_ctor_get(v_toRing_1833_, 9);
if (lean_obj_tag(v_negFn_x3f_1834_) == 1)
{
lean_object* v_val_1835_; lean_object* v___x_1837_; 
lean_inc_ref(v_negFn_x3f_1834_);
lean_dec_ref(v_toRing_1833_);
v_val_1835_ = lean_ctor_get(v_negFn_x3f_1834_, 0);
lean_inc(v_val_1835_);
lean_dec_ref_known(v_negFn_x3f_1834_, 1);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v_val_1835_);
v___x_1837_ = v___x_1831_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_val_1835_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
else
{
lean_object* v_type_1839_; lean_object* v_u_1840_; lean_object* v_ringInst_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v_expectedInst_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
lean_del_object(v___x_1831_);
v_type_1839_ = lean_ctor_get(v_toRing_1833_, 1);
lean_inc_ref_n(v_type_1839_, 2);
v_u_1840_ = lean_ctor_get(v_toRing_1833_, 2);
lean_inc_n(v_u_1840_, 2);
v_ringInst_1841_ = lean_ctor_get(v_toRing_1833_, 3);
lean_inc_ref(v_ringInst_1841_);
lean_dec_ref(v_toRing_1833_);
v___x_1842_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1));
v___x_1843_ = lean_box(0);
v___x_1844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1844_, 0, v_u_1840_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = l_Lean_mkConst(v___x_1842_, v___x_1844_);
v_expectedInst_1846_ = l_Lean_mkAppB(v___x_1845_, v_type_1839_, v_ringInst_1841_);
v___x_1847_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__3));
v___x_1848_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5));
v___x_1849_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__4(v_type_1839_, v_u_1840_, v___x_1847_, v___x_1848_, v_expectedInst_1846_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; lean_object* v___f_1851_; lean_object* v___x_1852_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc_n(v_a_1850_, 2);
lean_dec_ref_known(v___x_1849_, 1);
v___f_1851_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_1851_, 0, v_a_1850_);
v___x_1852_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_1851_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1859_ == 0)
{
lean_object* v_unused_1860_; 
v_unused_1860_ = lean_ctor_get(v___x_1852_, 0);
lean_dec(v_unused_1860_);
v___x_1854_ = v___x_1852_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_dec(v___x_1852_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v_a_1850_);
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1850_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec(v_a_1850_);
v_a_1861_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1852_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1852_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
else
{
return v___x_1849_;
}
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
v_a_1870_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1828_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1828_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___boxed(lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec(v___y_1878_);
return v_res_1890_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = lean_unsigned_to_nat(0u);
v___x_1899_ = lean_nat_to_int(v___x_1898_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(lean_object* v_k_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v___x_1919_; 
v___x_1919_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1980_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1922_ = v___x_1919_;
v_isShared_1923_ = v_isSharedCheck_1980_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1919_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1980_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v_toRing_1924_; lean_object* v_type_1925_; lean_object* v_u_1926_; lean_object* v_semiringInst_1927_; lean_object* v___x_1928_; lean_object* v_n_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v_ofNatInst_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v_toRing_1924_ = lean_ctor_get(v_a_1920_, 0);
lean_inc_ref(v_toRing_1924_);
lean_dec(v_a_1920_);
v_type_1925_ = lean_ctor_get(v_toRing_1924_, 1);
lean_inc_ref_n(v_type_1925_, 2);
v_u_1926_ = lean_ctor_get(v_toRing_1924_, 2);
lean_inc(v_u_1926_);
v_semiringInst_1927_ = lean_ctor_get(v_toRing_1924_, 4);
lean_inc_ref(v_semiringInst_1927_);
lean_dec_ref(v_toRing_1924_);
v___x_1928_ = lean_nat_abs(v_k_1906_);
v_n_1929_ = l_Lean_mkRawNatLit(v___x_1928_);
v___x_1930_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__1));
v___x_1931_ = lean_box(0);
v___x_1932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1932_, 0, v_u_1926_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
lean_inc_ref(v___x_1932_);
v___x_1964_ = l_Lean_mkConst(v___x_1930_, v___x_1932_);
lean_inc_ref(v_n_1929_);
v___x_1965_ = l_Lean_mkAppB(v___x_1964_, v_type_1925_, v_n_1929_);
v___x_1966_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1965_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
lean_dec_ref_known(v___x_1966_, 1);
if (lean_obj_tag(v_a_1967_) == 1)
{
lean_object* v_val_1968_; 
lean_dec_ref(v_semiringInst_1927_);
v_val_1968_ = lean_ctor_get(v_a_1967_, 0);
lean_inc(v_val_1968_);
lean_dec_ref_known(v_a_1967_, 1);
v_ofNatInst_1934_ = v_val_1968_;
v___y_1935_ = v___y_1907_;
v___y_1936_ = v___y_1908_;
v___y_1937_ = v___y_1909_;
v___y_1938_ = v___y_1910_;
v___y_1939_ = v___y_1911_;
v___y_1940_ = v___y_1912_;
v___y_1941_ = v___y_1913_;
v___y_1942_ = v___y_1914_;
v___y_1943_ = v___y_1915_;
v___y_1944_ = v___y_1916_;
v___y_1945_ = v___y_1917_;
goto v___jp_1933_;
}
else
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
lean_dec(v_a_1967_);
v___x_1969_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__6));
lean_inc_ref(v___x_1932_);
v___x_1970_ = l_Lean_mkConst(v___x_1969_, v___x_1932_);
lean_inc_ref(v_n_1929_);
lean_inc_ref(v_type_1925_);
v___x_1971_ = l_Lean_mkApp3(v___x_1970_, v_type_1925_, v_semiringInst_1927_, v_n_1929_);
v_ofNatInst_1934_ = v___x_1971_;
v___y_1935_ = v___y_1907_;
v___y_1936_ = v___y_1908_;
v___y_1937_ = v___y_1909_;
v___y_1938_ = v___y_1910_;
v___y_1939_ = v___y_1911_;
v___y_1940_ = v___y_1912_;
v___y_1941_ = v___y_1913_;
v___y_1942_ = v___y_1914_;
v___y_1943_ = v___y_1915_;
v___y_1944_ = v___y_1916_;
v___y_1945_ = v___y_1917_;
goto v___jp_1933_;
}
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
lean_dec_ref_known(v___x_1932_, 2);
lean_dec_ref(v_n_1929_);
lean_dec_ref(v_semiringInst_1927_);
lean_dec_ref(v_type_1925_);
lean_del_object(v___x_1922_);
v_a_1972_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1966_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1966_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
v___jp_1933_:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v_e_1948_; lean_object* v___x_1949_; uint8_t v___x_1950_; 
v___x_1946_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3));
v___x_1947_ = l_Lean_mkConst(v___x_1946_, v___x_1932_);
v_e_1948_ = l_Lean_mkApp3(v___x_1947_, v_type_1925_, v_n_1929_, v_ofNatInst_1934_);
v___x_1949_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4, &l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4_once, _init_l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4);
v___x_1950_ = lean_int_dec_lt(v_k_1906_, v___x_1949_);
if (v___x_1950_ == 0)
{
lean_object* v___x_1952_; 
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v_e_1948_);
v___x_1952_ = v___x_1922_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_e_1948_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
else
{
lean_object* v___x_1954_; 
lean_del_object(v___x_1922_);
v___x_1954_ = l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1963_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1957_ = v___x_1954_;
v_isShared_1958_ = v_isSharedCheck_1963_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1963_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1959_; lean_object* v___x_1961_; 
v___x_1959_ = l_Lean_Expr_app___override(v_a_1955_, v_e_1948_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v___x_1959_);
v___x_1961_ = v___x_1957_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___x_1959_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
else
{
lean_dec_ref(v_e_1948_);
return v___x_1954_;
}
}
}
}
}
else
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
v_a_1981_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1919_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1919_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___boxed(lean_object* v_k_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v_k_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec(v_k_1989_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___lam__0(lean_object* v_a_2003_, lean_object* v_s_2004_){
_start:
{
lean_object* v_toRing_2005_; lean_object* v_invFn_x3f_2006_; lean_object* v_divFn_x3f_2007_; lean_object* v_semiringId_x3f_2008_; lean_object* v_commSemiringInst_2009_; lean_object* v_commRingInst_2010_; lean_object* v_noZeroDivInst_x3f_2011_; lean_object* v_fieldInst_x3f_2012_; lean_object* v_powIdentityInst_x3f_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2044_; 
v_toRing_2005_ = lean_ctor_get(v_s_2004_, 0);
v_invFn_x3f_2006_ = lean_ctor_get(v_s_2004_, 1);
v_divFn_x3f_2007_ = lean_ctor_get(v_s_2004_, 2);
v_semiringId_x3f_2008_ = lean_ctor_get(v_s_2004_, 3);
v_commSemiringInst_2009_ = lean_ctor_get(v_s_2004_, 4);
v_commRingInst_2010_ = lean_ctor_get(v_s_2004_, 5);
v_noZeroDivInst_x3f_2011_ = lean_ctor_get(v_s_2004_, 6);
v_fieldInst_x3f_2012_ = lean_ctor_get(v_s_2004_, 7);
v_powIdentityInst_x3f_2013_ = lean_ctor_get(v_s_2004_, 8);
v_isSharedCheck_2044_ = !lean_is_exclusive(v_s_2004_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2015_ = v_s_2004_;
v_isShared_2016_ = v_isSharedCheck_2044_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_powIdentityInst_x3f_2013_);
lean_inc(v_fieldInst_x3f_2012_);
lean_inc(v_noZeroDivInst_x3f_2011_);
lean_inc(v_commRingInst_2010_);
lean_inc(v_commSemiringInst_2009_);
lean_inc(v_semiringId_x3f_2008_);
lean_inc(v_divFn_x3f_2007_);
lean_inc(v_invFn_x3f_2006_);
lean_inc(v_toRing_2005_);
lean_dec(v_s_2004_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2044_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v_id_2017_; lean_object* v_type_2018_; lean_object* v_u_2019_; lean_object* v_ringInst_2020_; lean_object* v_semiringInst_2021_; lean_object* v_charInst_x3f_2022_; lean_object* v_addFn_x3f_2023_; lean_object* v_mulFn_x3f_2024_; lean_object* v_subFn_x3f_2025_; lean_object* v_negFn_x3f_2026_; lean_object* v_intCastFn_x3f_2027_; lean_object* v_natCastFn_x3f_2028_; lean_object* v_natSMulFn_x3f_2029_; lean_object* v_intSMulFn_x3f_2030_; lean_object* v_one_x3f_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2042_; 
v_id_2017_ = lean_ctor_get(v_toRing_2005_, 0);
v_type_2018_ = lean_ctor_get(v_toRing_2005_, 1);
v_u_2019_ = lean_ctor_get(v_toRing_2005_, 2);
v_ringInst_2020_ = lean_ctor_get(v_toRing_2005_, 3);
v_semiringInst_2021_ = lean_ctor_get(v_toRing_2005_, 4);
v_charInst_x3f_2022_ = lean_ctor_get(v_toRing_2005_, 5);
v_addFn_x3f_2023_ = lean_ctor_get(v_toRing_2005_, 6);
v_mulFn_x3f_2024_ = lean_ctor_get(v_toRing_2005_, 7);
v_subFn_x3f_2025_ = lean_ctor_get(v_toRing_2005_, 8);
v_negFn_x3f_2026_ = lean_ctor_get(v_toRing_2005_, 9);
v_intCastFn_x3f_2027_ = lean_ctor_get(v_toRing_2005_, 11);
v_natCastFn_x3f_2028_ = lean_ctor_get(v_toRing_2005_, 12);
v_natSMulFn_x3f_2029_ = lean_ctor_get(v_toRing_2005_, 13);
v_intSMulFn_x3f_2030_ = lean_ctor_get(v_toRing_2005_, 14);
v_one_x3f_2031_ = lean_ctor_get(v_toRing_2005_, 15);
v_isSharedCheck_2042_ = !lean_is_exclusive(v_toRing_2005_);
if (v_isSharedCheck_2042_ == 0)
{
lean_object* v_unused_2043_; 
v_unused_2043_ = lean_ctor_get(v_toRing_2005_, 10);
lean_dec(v_unused_2043_);
v___x_2033_ = v_toRing_2005_;
v_isShared_2034_ = v_isSharedCheck_2042_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_one_x3f_2031_);
lean_inc(v_intSMulFn_x3f_2030_);
lean_inc(v_natSMulFn_x3f_2029_);
lean_inc(v_natCastFn_x3f_2028_);
lean_inc(v_intCastFn_x3f_2027_);
lean_inc(v_negFn_x3f_2026_);
lean_inc(v_subFn_x3f_2025_);
lean_inc(v_mulFn_x3f_2024_);
lean_inc(v_addFn_x3f_2023_);
lean_inc(v_charInst_x3f_2022_);
lean_inc(v_semiringInst_2021_);
lean_inc(v_ringInst_2020_);
lean_inc(v_u_2019_);
lean_inc(v_type_2018_);
lean_inc(v_id_2017_);
lean_dec(v_toRing_2005_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2042_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2035_; lean_object* v___x_2037_; 
v___x_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2035_, 0, v_a_2003_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 10, v___x_2035_);
v___x_2037_ = v___x_2033_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_id_2017_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_type_2018_);
lean_ctor_set(v_reuseFailAlloc_2041_, 2, v_u_2019_);
lean_ctor_set(v_reuseFailAlloc_2041_, 3, v_ringInst_2020_);
lean_ctor_set(v_reuseFailAlloc_2041_, 4, v_semiringInst_2021_);
lean_ctor_set(v_reuseFailAlloc_2041_, 5, v_charInst_x3f_2022_);
lean_ctor_set(v_reuseFailAlloc_2041_, 6, v_addFn_x3f_2023_);
lean_ctor_set(v_reuseFailAlloc_2041_, 7, v_mulFn_x3f_2024_);
lean_ctor_set(v_reuseFailAlloc_2041_, 8, v_subFn_x3f_2025_);
lean_ctor_set(v_reuseFailAlloc_2041_, 9, v_negFn_x3f_2026_);
lean_ctor_set(v_reuseFailAlloc_2041_, 10, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2041_, 11, v_intCastFn_x3f_2027_);
lean_ctor_set(v_reuseFailAlloc_2041_, 12, v_natCastFn_x3f_2028_);
lean_ctor_set(v_reuseFailAlloc_2041_, 13, v_natSMulFn_x3f_2029_);
lean_ctor_set(v_reuseFailAlloc_2041_, 14, v_intSMulFn_x3f_2030_);
lean_ctor_set(v_reuseFailAlloc_2041_, 15, v_one_x3f_2031_);
v___x_2037_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
lean_object* v___x_2039_; 
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 0, v___x_2037_);
v___x_2039_ = v___x_2015_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2037_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v_invFn_x3f_2006_);
lean_ctor_set(v_reuseFailAlloc_2040_, 2, v_divFn_x3f_2007_);
lean_ctor_set(v_reuseFailAlloc_2040_, 3, v_semiringId_x3f_2008_);
lean_ctor_set(v_reuseFailAlloc_2040_, 4, v_commSemiringInst_2009_);
lean_ctor_set(v_reuseFailAlloc_2040_, 5, v_commRingInst_2010_);
lean_ctor_set(v_reuseFailAlloc_2040_, 6, v_noZeroDivInst_x3f_2011_);
lean_ctor_set(v_reuseFailAlloc_2040_, 7, v_fieldInst_x3f_2012_);
lean_ctor_set(v_reuseFailAlloc_2040_, 8, v_powIdentityInst_x3f_2013_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__2(void){
_start:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = lean_unsigned_to_nat(0u);
v___x_2049_ = l_Lean_Level_ofNat(v___x_2048_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7(lean_object* v_u_2060_, lean_object* v_type_2061_, lean_object* v_semiringInst_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2075_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__1));
v___x_2076_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__2, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__2);
v___x_2077_ = lean_box(0);
lean_inc(v_u_2060_);
v___x_2078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2078_, 0, v_u_2060_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
lean_inc_ref(v___x_2078_);
v___x_2079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2076_);
lean_ctor_set(v___x_2079_, 1, v___x_2078_);
v___x_2080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2080_, 0, v_u_2060_);
lean_ctor_set(v___x_2080_, 1, v___x_2079_);
lean_inc_ref(v___x_2080_);
v___x_2081_ = l_Lean_mkConst(v___x_2075_, v___x_2080_);
v___x_2082_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2061_, 2);
v___x_2083_ = l_Lean_mkApp3(v___x_2081_, v_type_2061_, v___x_2082_, v_type_2061_);
v___x_2084_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg(v___x_2083_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v_inst_x27_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc_n(v_a_2085_, 2);
lean_dec_ref_known(v___x_2084_, 1);
v___x_2086_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__4));
v___x_2087_ = l_Lean_mkConst(v___x_2086_, v___x_2078_);
lean_inc_ref(v_type_2061_);
v_inst_x27_2088_ = l_Lean_mkAppB(v___x_2087_, v_type_2061_, v_semiringInst_2062_);
v___x_2089_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__6));
v___x_2090_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v___x_2089_, v_a_2085_, v_inst_x27_2088_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
lean_dec_ref_known(v___x_2090_, 1);
v___x_2091_ = l_Lean_mkConst(v___x_2089_, v___x_2080_);
lean_inc_ref(v_type_2061_);
v___x_2092_ = l_Lean_mkApp4(v___x_2091_, v_type_2061_, v___x_2082_, v_type_2061_, v_a_2085_);
v___x_2093_ = l_Lean_Meta_Sym_canon(v___x_2092_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v___x_2095_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_a_2094_);
lean_dec_ref_known(v___x_2093_, 1);
v___x_2095_ = l_Lean_Meta_Sym_shareCommon(v_a_2094_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
return v___x_2095_;
}
else
{
return v___x_2093_;
}
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec(v_a_2085_);
lean_dec_ref_known(v___x_2080_, 2);
lean_dec_ref(v_type_2061_);
v_a_2096_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2090_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2090_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2080_, 2);
lean_dec_ref_known(v___x_2078_, 2);
lean_dec_ref(v_semiringInst_2062_);
lean_dec_ref(v_type_2061_);
return v___x_2084_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___boxed(lean_object* v_u_2104_, lean_object* v_type_2105_, lean_object* v_semiringInst_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7(v_u_2104_, v_type_2105_, v_semiringInst_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec(v___y_2107_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2166_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2135_ = v___x_2132_;
v_isShared_2136_ = v_isSharedCheck_2166_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2132_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2166_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v_toRing_2137_; lean_object* v_powFn_x3f_2138_; 
v_toRing_2137_ = lean_ctor_get(v_a_2133_, 0);
lean_inc_ref(v_toRing_2137_);
lean_dec(v_a_2133_);
v_powFn_x3f_2138_ = lean_ctor_get(v_toRing_2137_, 10);
if (lean_obj_tag(v_powFn_x3f_2138_) == 1)
{
lean_object* v_val_2139_; lean_object* v___x_2141_; 
lean_inc_ref(v_powFn_x3f_2138_);
lean_dec_ref(v_toRing_2137_);
v_val_2139_ = lean_ctor_get(v_powFn_x3f_2138_, 0);
lean_inc(v_val_2139_);
lean_dec_ref_known(v_powFn_x3f_2138_, 1);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v_val_2139_);
v___x_2141_ = v___x_2135_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_val_2139_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
else
{
lean_object* v_type_2143_; lean_object* v_u_2144_; lean_object* v_semiringInst_2145_; lean_object* v___x_2146_; 
lean_del_object(v___x_2135_);
v_type_2143_ = lean_ctor_get(v_toRing_2137_, 1);
lean_inc_ref(v_type_2143_);
v_u_2144_ = lean_ctor_get(v_toRing_2137_, 2);
lean_inc(v_u_2144_);
v_semiringInst_2145_ = lean_ctor_get(v_toRing_2137_, 4);
lean_inc_ref(v_semiringInst_2145_);
lean_dec_ref(v_toRing_2137_);
v___x_2146_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7(v_u_2144_, v_type_2143_, v_semiringInst_2145_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; lean_object* v___f_2148_; lean_object* v___x_2149_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc_n(v_a_2147_, 2);
lean_dec_ref_known(v___x_2146_, 1);
v___f_2148_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___lam__0), 2, 1);
lean_closure_set(v___f_2148_, 0, v_a_2147_);
v___x_2149_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2148_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2156_ == 0)
{
lean_object* v_unused_2157_; 
v_unused_2157_ = lean_ctor_get(v___x_2149_, 0);
lean_dec(v_unused_2157_);
v___x_2151_ = v___x_2149_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_dec(v___x_2149_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 0, v_a_2147_);
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2147_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
else
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
lean_dec(v_a_2147_);
v_a_2158_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2160_ = v___x_2149_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2149_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2158_);
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
else
{
return v___x_2146_;
}
}
}
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
v_a_2167_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2132_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2132_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___boxed(lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec(v___y_2175_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4(lean_object* v_type_2188_, lean_object* v_u_2189_, lean_object* v_instDeclName_2190_, lean_object* v_declName_2191_, lean_object* v_expectedInst_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2205_ = lean_box(0);
lean_inc_n(v_u_2189_, 2);
v___x_2206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2206_, 0, v_u_2189_);
lean_ctor_set(v___x_2206_, 1, v___x_2205_);
v___x_2207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2207_, 0, v_u_2189_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
v___x_2208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2208_, 0, v_u_2189_);
lean_ctor_set(v___x_2208_, 1, v___x_2207_);
lean_inc_ref(v___x_2208_);
v___x_2209_ = l_Lean_mkConst(v_instDeclName_2190_, v___x_2208_);
lean_inc_ref_n(v_type_2188_, 3);
v___x_2210_ = l_Lean_mkApp3(v___x_2209_, v_type_2188_, v_type_2188_, v_type_2188_);
v___x_2211_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg(v___x_2210_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v_a_2212_; lean_object* v___x_2213_; 
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
lean_inc_n(v_a_2212_, 2);
lean_dec_ref_known(v___x_2211_, 1);
lean_inc(v_declName_2191_);
v___x_2213_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v_declName_2191_, v_a_2212_, v_expectedInst_2192_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
lean_dec_ref_known(v___x_2213_, 1);
v___x_2214_ = l_Lean_mkConst(v_declName_2191_, v___x_2208_);
lean_inc_ref_n(v_type_2188_, 2);
v___x_2215_ = l_Lean_mkApp4(v___x_2214_, v_type_2188_, v_type_2188_, v_type_2188_, v_a_2212_);
v___x_2216_ = l_Lean_Meta_Sym_canon(v___x_2215_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v_a_2217_; lean_object* v___x_2218_; 
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_a_2217_);
lean_dec_ref_known(v___x_2216_, 1);
v___x_2218_ = l_Lean_Meta_Sym_shareCommon(v_a_2217_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
return v___x_2218_;
}
else
{
return v___x_2216_;
}
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2226_; 
lean_dec(v_a_2212_);
lean_dec_ref_known(v___x_2208_, 2);
lean_dec(v_declName_2191_);
lean_dec_ref(v_type_2188_);
v_a_2219_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2221_ = v___x_2213_;
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2213_);
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
lean_dec_ref_known(v___x_2208_, 2);
lean_dec_ref(v_expectedInst_2192_);
lean_dec(v_declName_2191_);
lean_dec_ref(v_type_2188_);
return v___x_2211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4___boxed(lean_object** _args){
lean_object* v_type_2227_ = _args[0];
lean_object* v_u_2228_ = _args[1];
lean_object* v_instDeclName_2229_ = _args[2];
lean_object* v_declName_2230_ = _args[3];
lean_object* v_expectedInst_2231_ = _args[4];
lean_object* v___y_2232_ = _args[5];
lean_object* v___y_2233_ = _args[6];
lean_object* v___y_2234_ = _args[7];
lean_object* v___y_2235_ = _args[8];
lean_object* v___y_2236_ = _args[9];
lean_object* v___y_2237_ = _args[10];
lean_object* v___y_2238_ = _args[11];
lean_object* v___y_2239_ = _args[12];
lean_object* v___y_2240_ = _args[13];
lean_object* v___y_2241_ = _args[14];
lean_object* v___y_2242_ = _args[15];
lean_object* v___y_2243_ = _args[16];
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4(v_type_2227_, v_u_2228_, v_instDeclName_2229_, v_declName_2230_, v_expectedInst_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec(v___y_2232_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0(lean_object* v_a_2245_, lean_object* v_s_2246_){
_start:
{
lean_object* v_toRing_2247_; lean_object* v_invFn_x3f_2248_; lean_object* v_divFn_x3f_2249_; lean_object* v_semiringId_x3f_2250_; lean_object* v_commSemiringInst_2251_; lean_object* v_commRingInst_2252_; lean_object* v_noZeroDivInst_x3f_2253_; lean_object* v_fieldInst_x3f_2254_; lean_object* v_powIdentityInst_x3f_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2286_; 
v_toRing_2247_ = lean_ctor_get(v_s_2246_, 0);
v_invFn_x3f_2248_ = lean_ctor_get(v_s_2246_, 1);
v_divFn_x3f_2249_ = lean_ctor_get(v_s_2246_, 2);
v_semiringId_x3f_2250_ = lean_ctor_get(v_s_2246_, 3);
v_commSemiringInst_2251_ = lean_ctor_get(v_s_2246_, 4);
v_commRingInst_2252_ = lean_ctor_get(v_s_2246_, 5);
v_noZeroDivInst_x3f_2253_ = lean_ctor_get(v_s_2246_, 6);
v_fieldInst_x3f_2254_ = lean_ctor_get(v_s_2246_, 7);
v_powIdentityInst_x3f_2255_ = lean_ctor_get(v_s_2246_, 8);
v_isSharedCheck_2286_ = !lean_is_exclusive(v_s_2246_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2257_ = v_s_2246_;
v_isShared_2258_ = v_isSharedCheck_2286_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_powIdentityInst_x3f_2255_);
lean_inc(v_fieldInst_x3f_2254_);
lean_inc(v_noZeroDivInst_x3f_2253_);
lean_inc(v_commRingInst_2252_);
lean_inc(v_commSemiringInst_2251_);
lean_inc(v_semiringId_x3f_2250_);
lean_inc(v_divFn_x3f_2249_);
lean_inc(v_invFn_x3f_2248_);
lean_inc(v_toRing_2247_);
lean_dec(v_s_2246_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2286_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v_id_2259_; lean_object* v_type_2260_; lean_object* v_u_2261_; lean_object* v_ringInst_2262_; lean_object* v_semiringInst_2263_; lean_object* v_charInst_x3f_2264_; lean_object* v_mulFn_x3f_2265_; lean_object* v_subFn_x3f_2266_; lean_object* v_negFn_x3f_2267_; lean_object* v_powFn_x3f_2268_; lean_object* v_intCastFn_x3f_2269_; lean_object* v_natCastFn_x3f_2270_; lean_object* v_natSMulFn_x3f_2271_; lean_object* v_intSMulFn_x3f_2272_; lean_object* v_one_x3f_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2284_; 
v_id_2259_ = lean_ctor_get(v_toRing_2247_, 0);
v_type_2260_ = lean_ctor_get(v_toRing_2247_, 1);
v_u_2261_ = lean_ctor_get(v_toRing_2247_, 2);
v_ringInst_2262_ = lean_ctor_get(v_toRing_2247_, 3);
v_semiringInst_2263_ = lean_ctor_get(v_toRing_2247_, 4);
v_charInst_x3f_2264_ = lean_ctor_get(v_toRing_2247_, 5);
v_mulFn_x3f_2265_ = lean_ctor_get(v_toRing_2247_, 7);
v_subFn_x3f_2266_ = lean_ctor_get(v_toRing_2247_, 8);
v_negFn_x3f_2267_ = lean_ctor_get(v_toRing_2247_, 9);
v_powFn_x3f_2268_ = lean_ctor_get(v_toRing_2247_, 10);
v_intCastFn_x3f_2269_ = lean_ctor_get(v_toRing_2247_, 11);
v_natCastFn_x3f_2270_ = lean_ctor_get(v_toRing_2247_, 12);
v_natSMulFn_x3f_2271_ = lean_ctor_get(v_toRing_2247_, 13);
v_intSMulFn_x3f_2272_ = lean_ctor_get(v_toRing_2247_, 14);
v_one_x3f_2273_ = lean_ctor_get(v_toRing_2247_, 15);
v_isSharedCheck_2284_ = !lean_is_exclusive(v_toRing_2247_);
if (v_isSharedCheck_2284_ == 0)
{
lean_object* v_unused_2285_; 
v_unused_2285_ = lean_ctor_get(v_toRing_2247_, 6);
lean_dec(v_unused_2285_);
v___x_2275_ = v_toRing_2247_;
v_isShared_2276_ = v_isSharedCheck_2284_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_one_x3f_2273_);
lean_inc(v_intSMulFn_x3f_2272_);
lean_inc(v_natSMulFn_x3f_2271_);
lean_inc(v_natCastFn_x3f_2270_);
lean_inc(v_intCastFn_x3f_2269_);
lean_inc(v_powFn_x3f_2268_);
lean_inc(v_negFn_x3f_2267_);
lean_inc(v_subFn_x3f_2266_);
lean_inc(v_mulFn_x3f_2265_);
lean_inc(v_charInst_x3f_2264_);
lean_inc(v_semiringInst_2263_);
lean_inc(v_ringInst_2262_);
lean_inc(v_u_2261_);
lean_inc(v_type_2260_);
lean_inc(v_id_2259_);
lean_dec(v_toRing_2247_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2284_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2277_; lean_object* v___x_2279_; 
v___x_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2277_, 0, v_a_2245_);
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 6, v___x_2277_);
v___x_2279_ = v___x_2275_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_id_2259_);
lean_ctor_set(v_reuseFailAlloc_2283_, 1, v_type_2260_);
lean_ctor_set(v_reuseFailAlloc_2283_, 2, v_u_2261_);
lean_ctor_set(v_reuseFailAlloc_2283_, 3, v_ringInst_2262_);
lean_ctor_set(v_reuseFailAlloc_2283_, 4, v_semiringInst_2263_);
lean_ctor_set(v_reuseFailAlloc_2283_, 5, v_charInst_x3f_2264_);
lean_ctor_set(v_reuseFailAlloc_2283_, 6, v___x_2277_);
lean_ctor_set(v_reuseFailAlloc_2283_, 7, v_mulFn_x3f_2265_);
lean_ctor_set(v_reuseFailAlloc_2283_, 8, v_subFn_x3f_2266_);
lean_ctor_set(v_reuseFailAlloc_2283_, 9, v_negFn_x3f_2267_);
lean_ctor_set(v_reuseFailAlloc_2283_, 10, v_powFn_x3f_2268_);
lean_ctor_set(v_reuseFailAlloc_2283_, 11, v_intCastFn_x3f_2269_);
lean_ctor_set(v_reuseFailAlloc_2283_, 12, v_natCastFn_x3f_2270_);
lean_ctor_set(v_reuseFailAlloc_2283_, 13, v_natSMulFn_x3f_2271_);
lean_ctor_set(v_reuseFailAlloc_2283_, 14, v_intSMulFn_x3f_2272_);
lean_ctor_set(v_reuseFailAlloc_2283_, 15, v_one_x3f_2273_);
v___x_2279_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
lean_object* v___x_2281_; 
if (v_isShared_2258_ == 0)
{
lean_ctor_set(v___x_2257_, 0, v___x_2279_);
v___x_2281_ = v___x_2257_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2279_);
lean_ctor_set(v_reuseFailAlloc_2282_, 1, v_invFn_x3f_2248_);
lean_ctor_set(v_reuseFailAlloc_2282_, 2, v_divFn_x3f_2249_);
lean_ctor_set(v_reuseFailAlloc_2282_, 3, v_semiringId_x3f_2250_);
lean_ctor_set(v_reuseFailAlloc_2282_, 4, v_commSemiringInst_2251_);
lean_ctor_set(v_reuseFailAlloc_2282_, 5, v_commRingInst_2252_);
lean_ctor_set(v_reuseFailAlloc_2282_, 6, v_noZeroDivInst_x3f_2253_);
lean_ctor_set(v_reuseFailAlloc_2282_, 7, v_fieldInst_x3f_2254_);
lean_ctor_set(v_reuseFailAlloc_2282_, 8, v_powIdentityInst_x3f_2255_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2359_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2318_ = v___x_2315_;
v_isShared_2319_ = v_isSharedCheck_2359_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2315_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2359_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v_toRing_2320_; lean_object* v_addFn_x3f_2321_; 
v_toRing_2320_ = lean_ctor_get(v_a_2316_, 0);
lean_inc_ref(v_toRing_2320_);
lean_dec(v_a_2316_);
v_addFn_x3f_2321_ = lean_ctor_get(v_toRing_2320_, 6);
if (lean_obj_tag(v_addFn_x3f_2321_) == 1)
{
lean_object* v_val_2322_; lean_object* v___x_2324_; 
lean_inc_ref(v_addFn_x3f_2321_);
lean_dec_ref(v_toRing_2320_);
v_val_2322_ = lean_ctor_get(v_addFn_x3f_2321_, 0);
lean_inc(v_val_2322_);
lean_dec_ref_known(v_addFn_x3f_2321_, 1);
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 0, v_val_2322_);
v___x_2324_ = v___x_2318_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_val_2322_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
else
{
lean_object* v_type_2326_; lean_object* v_u_2327_; lean_object* v_semiringInst_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v_expectedInst_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
lean_del_object(v___x_2318_);
v_type_2326_ = lean_ctor_get(v_toRing_2320_, 1);
lean_inc_ref_n(v_type_2326_, 3);
v_u_2327_ = lean_ctor_get(v_toRing_2320_, 2);
lean_inc_n(v_u_2327_, 2);
v_semiringInst_2328_ = lean_ctor_get(v_toRing_2320_, 4);
lean_inc_ref(v_semiringInst_2328_);
lean_dec_ref(v_toRing_2320_);
v___x_2329_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__1));
v___x_2330_ = lean_box(0);
v___x_2331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2331_, 0, v_u_2327_);
lean_ctor_set(v___x_2331_, 1, v___x_2330_);
lean_inc_ref(v___x_2331_);
v___x_2332_ = l_Lean_mkConst(v___x_2329_, v___x_2331_);
v___x_2333_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__3));
v___x_2334_ = l_Lean_mkConst(v___x_2333_, v___x_2331_);
v___x_2335_ = l_Lean_mkAppB(v___x_2334_, v_type_2326_, v_semiringInst_2328_);
v_expectedInst_2336_ = l_Lean_mkAppB(v___x_2332_, v_type_2326_, v___x_2335_);
v___x_2337_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__5));
v___x_2338_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__7));
v___x_2339_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4(v_type_2326_, v_u_2327_, v___x_2337_, v___x_2338_, v_expectedInst_2336_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___f_2341_; lean_object* v___x_2342_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc_n(v_a_2340_, 2);
lean_dec_ref_known(v___x_2339_, 1);
v___f_2341_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_2341_, 0, v_a_2340_);
v___x_2342_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2341_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2349_ == 0)
{
lean_object* v_unused_2350_; 
v_unused_2350_ = lean_ctor_get(v___x_2342_, 0);
lean_dec(v_unused_2350_);
v___x_2344_ = v___x_2342_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_dec(v___x_2342_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 0, v_a_2340_);
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2340_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
lean_dec(v_a_2340_);
v_a_2351_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2342_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2342_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
else
{
return v___x_2339_;
}
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
v_a_2360_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2315_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2315_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___boxed(lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec(v___y_2368_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___lam__0(lean_object* v_a_2381_, lean_object* v_s_2382_){
_start:
{
lean_object* v_toRing_2383_; lean_object* v_invFn_x3f_2384_; lean_object* v_divFn_x3f_2385_; lean_object* v_semiringId_x3f_2386_; lean_object* v_commSemiringInst_2387_; lean_object* v_commRingInst_2388_; lean_object* v_noZeroDivInst_x3f_2389_; lean_object* v_fieldInst_x3f_2390_; lean_object* v_powIdentityInst_x3f_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2422_; 
v_toRing_2383_ = lean_ctor_get(v_s_2382_, 0);
v_invFn_x3f_2384_ = lean_ctor_get(v_s_2382_, 1);
v_divFn_x3f_2385_ = lean_ctor_get(v_s_2382_, 2);
v_semiringId_x3f_2386_ = lean_ctor_get(v_s_2382_, 3);
v_commSemiringInst_2387_ = lean_ctor_get(v_s_2382_, 4);
v_commRingInst_2388_ = lean_ctor_get(v_s_2382_, 5);
v_noZeroDivInst_x3f_2389_ = lean_ctor_get(v_s_2382_, 6);
v_fieldInst_x3f_2390_ = lean_ctor_get(v_s_2382_, 7);
v_powIdentityInst_x3f_2391_ = lean_ctor_get(v_s_2382_, 8);
v_isSharedCheck_2422_ = !lean_is_exclusive(v_s_2382_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2393_ = v_s_2382_;
v_isShared_2394_ = v_isSharedCheck_2422_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_powIdentityInst_x3f_2391_);
lean_inc(v_fieldInst_x3f_2390_);
lean_inc(v_noZeroDivInst_x3f_2389_);
lean_inc(v_commRingInst_2388_);
lean_inc(v_commSemiringInst_2387_);
lean_inc(v_semiringId_x3f_2386_);
lean_inc(v_divFn_x3f_2385_);
lean_inc(v_invFn_x3f_2384_);
lean_inc(v_toRing_2383_);
lean_dec(v_s_2382_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2422_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v_id_2395_; lean_object* v_type_2396_; lean_object* v_u_2397_; lean_object* v_ringInst_2398_; lean_object* v_semiringInst_2399_; lean_object* v_charInst_x3f_2400_; lean_object* v_addFn_x3f_2401_; lean_object* v_subFn_x3f_2402_; lean_object* v_negFn_x3f_2403_; lean_object* v_powFn_x3f_2404_; lean_object* v_intCastFn_x3f_2405_; lean_object* v_natCastFn_x3f_2406_; lean_object* v_natSMulFn_x3f_2407_; lean_object* v_intSMulFn_x3f_2408_; lean_object* v_one_x3f_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2420_; 
v_id_2395_ = lean_ctor_get(v_toRing_2383_, 0);
v_type_2396_ = lean_ctor_get(v_toRing_2383_, 1);
v_u_2397_ = lean_ctor_get(v_toRing_2383_, 2);
v_ringInst_2398_ = lean_ctor_get(v_toRing_2383_, 3);
v_semiringInst_2399_ = lean_ctor_get(v_toRing_2383_, 4);
v_charInst_x3f_2400_ = lean_ctor_get(v_toRing_2383_, 5);
v_addFn_x3f_2401_ = lean_ctor_get(v_toRing_2383_, 6);
v_subFn_x3f_2402_ = lean_ctor_get(v_toRing_2383_, 8);
v_negFn_x3f_2403_ = lean_ctor_get(v_toRing_2383_, 9);
v_powFn_x3f_2404_ = lean_ctor_get(v_toRing_2383_, 10);
v_intCastFn_x3f_2405_ = lean_ctor_get(v_toRing_2383_, 11);
v_natCastFn_x3f_2406_ = lean_ctor_get(v_toRing_2383_, 12);
v_natSMulFn_x3f_2407_ = lean_ctor_get(v_toRing_2383_, 13);
v_intSMulFn_x3f_2408_ = lean_ctor_get(v_toRing_2383_, 14);
v_one_x3f_2409_ = lean_ctor_get(v_toRing_2383_, 15);
v_isSharedCheck_2420_ = !lean_is_exclusive(v_toRing_2383_);
if (v_isSharedCheck_2420_ == 0)
{
lean_object* v_unused_2421_; 
v_unused_2421_ = lean_ctor_get(v_toRing_2383_, 7);
lean_dec(v_unused_2421_);
v___x_2411_ = v_toRing_2383_;
v_isShared_2412_ = v_isSharedCheck_2420_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_one_x3f_2409_);
lean_inc(v_intSMulFn_x3f_2408_);
lean_inc(v_natSMulFn_x3f_2407_);
lean_inc(v_natCastFn_x3f_2406_);
lean_inc(v_intCastFn_x3f_2405_);
lean_inc(v_powFn_x3f_2404_);
lean_inc(v_negFn_x3f_2403_);
lean_inc(v_subFn_x3f_2402_);
lean_inc(v_addFn_x3f_2401_);
lean_inc(v_charInst_x3f_2400_);
lean_inc(v_semiringInst_2399_);
lean_inc(v_ringInst_2398_);
lean_inc(v_u_2397_);
lean_inc(v_type_2396_);
lean_inc(v_id_2395_);
lean_dec(v_toRing_2383_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2420_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2413_; lean_object* v___x_2415_; 
v___x_2413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2413_, 0, v_a_2381_);
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 7, v___x_2413_);
v___x_2415_ = v___x_2411_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_id_2395_);
lean_ctor_set(v_reuseFailAlloc_2419_, 1, v_type_2396_);
lean_ctor_set(v_reuseFailAlloc_2419_, 2, v_u_2397_);
lean_ctor_set(v_reuseFailAlloc_2419_, 3, v_ringInst_2398_);
lean_ctor_set(v_reuseFailAlloc_2419_, 4, v_semiringInst_2399_);
lean_ctor_set(v_reuseFailAlloc_2419_, 5, v_charInst_x3f_2400_);
lean_ctor_set(v_reuseFailAlloc_2419_, 6, v_addFn_x3f_2401_);
lean_ctor_set(v_reuseFailAlloc_2419_, 7, v___x_2413_);
lean_ctor_set(v_reuseFailAlloc_2419_, 8, v_subFn_x3f_2402_);
lean_ctor_set(v_reuseFailAlloc_2419_, 9, v_negFn_x3f_2403_);
lean_ctor_set(v_reuseFailAlloc_2419_, 10, v_powFn_x3f_2404_);
lean_ctor_set(v_reuseFailAlloc_2419_, 11, v_intCastFn_x3f_2405_);
lean_ctor_set(v_reuseFailAlloc_2419_, 12, v_natCastFn_x3f_2406_);
lean_ctor_set(v_reuseFailAlloc_2419_, 13, v_natSMulFn_x3f_2407_);
lean_ctor_set(v_reuseFailAlloc_2419_, 14, v_intSMulFn_x3f_2408_);
lean_ctor_set(v_reuseFailAlloc_2419_, 15, v_one_x3f_2409_);
v___x_2415_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
lean_object* v___x_2417_; 
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 0, v___x_2415_);
v___x_2417_ = v___x_2393_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2415_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v_invFn_x3f_2384_);
lean_ctor_set(v_reuseFailAlloc_2418_, 2, v_divFn_x3f_2385_);
lean_ctor_set(v_reuseFailAlloc_2418_, 3, v_semiringId_x3f_2386_);
lean_ctor_set(v_reuseFailAlloc_2418_, 4, v_commSemiringInst_2387_);
lean_ctor_set(v_reuseFailAlloc_2418_, 5, v_commRingInst_2388_);
lean_ctor_set(v_reuseFailAlloc_2418_, 6, v_noZeroDivInst_x3f_2389_);
lean_ctor_set(v_reuseFailAlloc_2418_, 7, v_fieldInst_x3f_2390_);
lean_ctor_set(v_reuseFailAlloc_2418_, 8, v_powIdentityInst_x3f_2391_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v___x_2451_; 
v___x_2451_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2495_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2454_ = v___x_2451_;
v_isShared_2455_ = v_isSharedCheck_2495_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2451_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2495_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v_toRing_2456_; lean_object* v_mulFn_x3f_2457_; 
v_toRing_2456_ = lean_ctor_get(v_a_2452_, 0);
lean_inc_ref(v_toRing_2456_);
lean_dec(v_a_2452_);
v_mulFn_x3f_2457_ = lean_ctor_get(v_toRing_2456_, 7);
if (lean_obj_tag(v_mulFn_x3f_2457_) == 1)
{
lean_object* v_val_2458_; lean_object* v___x_2460_; 
lean_inc_ref(v_mulFn_x3f_2457_);
lean_dec_ref(v_toRing_2456_);
v_val_2458_ = lean_ctor_get(v_mulFn_x3f_2457_, 0);
lean_inc(v_val_2458_);
lean_dec_ref_known(v_mulFn_x3f_2457_, 1);
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 0, v_val_2458_);
v___x_2460_ = v___x_2454_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_val_2458_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
else
{
lean_object* v_type_2462_; lean_object* v_u_2463_; lean_object* v_semiringInst_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v_expectedInst_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
lean_del_object(v___x_2454_);
v_type_2462_ = lean_ctor_get(v_toRing_2456_, 1);
lean_inc_ref_n(v_type_2462_, 3);
v_u_2463_ = lean_ctor_get(v_toRing_2456_, 2);
lean_inc_n(v_u_2463_, 2);
v_semiringInst_2464_ = lean_ctor_get(v_toRing_2456_, 4);
lean_inc_ref(v_semiringInst_2464_);
lean_dec_ref(v_toRing_2456_);
v___x_2465_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__1));
v___x_2466_ = lean_box(0);
v___x_2467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2467_, 0, v_u_2463_);
lean_ctor_set(v___x_2467_, 1, v___x_2466_);
lean_inc_ref(v___x_2467_);
v___x_2468_ = l_Lean_mkConst(v___x_2465_, v___x_2467_);
v___x_2469_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__3));
v___x_2470_ = l_Lean_mkConst(v___x_2469_, v___x_2467_);
v___x_2471_ = l_Lean_mkAppB(v___x_2470_, v_type_2462_, v_semiringInst_2464_);
v_expectedInst_2472_ = l_Lean_mkAppB(v___x_2468_, v_type_2462_, v___x_2471_);
v___x_2473_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__5));
v___x_2474_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__7));
v___x_2475_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4(v_type_2462_, v_u_2463_, v___x_2473_, v___x_2474_, v_expectedInst_2472_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v_a_2476_; lean_object* v___f_2477_; lean_object* v___x_2478_; 
v_a_2476_ = lean_ctor_get(v___x_2475_, 0);
lean_inc_n(v_a_2476_, 2);
lean_dec_ref_known(v___x_2475_, 1);
v___f_2477_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___lam__0), 2, 1);
lean_closure_set(v___f_2477_, 0, v_a_2476_);
v___x_2478_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2477_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2485_ == 0)
{
lean_object* v_unused_2486_; 
v_unused_2486_ = lean_ctor_get(v___x_2478_, 0);
lean_dec(v_unused_2486_);
v___x_2480_ = v___x_2478_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_dec(v___x_2478_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v_a_2476_);
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2476_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
else
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
lean_dec(v_a_2476_);
v_a_2487_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___x_2478_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2478_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2487_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
else
{
return v___x_2475_;
}
}
}
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
v_a_2496_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2451_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2451_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
if (v_isShared_2499_ == 0)
{
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___boxed(lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec(v___y_2504_);
return v_res_2516_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3(void){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2520_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__2));
v___x_2521_ = lean_unsigned_to_nat(39u);
v___x_2522_ = lean_unsigned_to_nat(131u);
v___x_2523_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__1));
v___x_2524_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__0));
v___x_2525_ = l_mkPanicMessageWithDecl(v___x_2524_, v___x_2523_, v___x_2522_, v___x_2521_, v___x_2520_);
return v___x_2525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(lean_object* v_gen_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_){
_start:
{
switch(lean_obj_tag(v_a_2527_))
{
case 0:
{
lean_object* v_k_2540_; lean_object* v___x_2541_; 
lean_dec(v_gen_2526_);
v_k_2540_ = lean_ctor_get(v_a_2527_, 0);
lean_inc(v_k_2540_);
lean_dec_ref_known(v_a_2527_, 1);
v___x_2541_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v_k_2540_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_);
lean_dec(v_k_2540_);
return v___x_2541_;
}
case 1:
{
lean_object* v_k_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
lean_dec(v_gen_2526_);
v_k_2542_ = lean_ctor_get(v_a_2527_, 0);
lean_inc(v_k_2542_);
lean_dec_ref_known(v_a_2527_, 1);
v___x_2543_ = lean_nat_to_int(v_k_2542_);
v___x_2544_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v___x_2543_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_);
lean_dec(v___x_2543_);
return v___x_2544_;
}
case 3:
{
lean_object* v_i_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v_i_2545_ = lean_ctor_get(v_a_2527_, 0);
lean_inc(v_i_2545_);
lean_dec_ref_known(v_a_2527_, 1);
v___x_2546_ = l_Lean_instInhabitedExpr;
v___x_2547_ = l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_a_2548_; lean_object* v___x_2549_; 
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_a_2548_);
lean_dec_ref_known(v___x_2547_, 1);
v___x_2549_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState___redArg(v_a_2528_, v_a_2529_, v_a_2537_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; lean_object* v___y_2552_; lean_object* v_vars_2574_; lean_object* v_size_2575_; uint8_t v___x_2576_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_a_2550_);
lean_dec_ref_known(v___x_2549_, 1);
v_vars_2574_ = lean_ctor_get(v_a_2550_, 1);
lean_inc_ref(v_vars_2574_);
lean_dec(v_a_2550_);
v_size_2575_ = lean_ctor_get(v_vars_2574_, 2);
v___x_2576_ = lean_nat_dec_lt(v_i_2545_, v_size_2575_);
if (v___x_2576_ == 0)
{
lean_object* v___x_2577_; 
lean_dec_ref(v_vars_2574_);
lean_dec(v_i_2545_);
v___x_2577_ = l_outOfBounds___redArg(v___x_2546_);
v___y_2552_ = v___x_2577_;
goto v___jp_2551_;
}
else
{
lean_object* v___x_2578_; 
v___x_2578_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2546_, v_vars_2574_, v_i_2545_);
lean_dec(v_i_2545_);
lean_dec_ref(v_vars_2574_);
v___y_2552_ = v___x_2578_;
goto v___jp_2551_;
}
v___jp_2551_:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2553_ = l_Lean_Expr_app___override(v_a_2548_, v___y_2552_);
v___x_2554_ = l_Lean_Meta_Sym_shareCommon(v___x_2553_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc_n(v_a_2555_, 2);
lean_dec_ref_known(v___x_2554_, 1);
v___x_2556_ = lean_box(0);
lean_inc(v_a_2538_);
lean_inc_ref(v_a_2537_);
lean_inc(v_a_2536_);
lean_inc_ref(v_a_2535_);
lean_inc(v_a_2534_);
lean_inc_ref(v_a_2533_);
lean_inc(v_a_2532_);
lean_inc_ref(v_a_2531_);
lean_inc(v_a_2530_);
lean_inc(v_a_2529_);
v___x_2557_ = lean_grind_internalize(v_a_2555_, v_gen_2526_, v___x_2556_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2564_ == 0)
{
lean_object* v_unused_2565_; 
v_unused_2565_ = lean_ctor_get(v___x_2557_, 0);
lean_dec(v_unused_2565_);
v___x_2559_ = v___x_2557_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_dec(v___x_2557_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v_a_2555_);
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_a_2555_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
lean_dec(v_a_2555_);
v_a_2566_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2557_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2557_);
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
else
{
lean_dec(v_gen_2526_);
return v___x_2554_;
}
}
}
else
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2586_; 
lean_dec(v_a_2548_);
lean_dec(v_i_2545_);
lean_dec(v_gen_2526_);
v_a_2579_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2581_ = v___x_2549_;
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2549_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2584_; 
if (v_isShared_2582_ == 0)
{
v___x_2584_ = v___x_2581_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_a_2579_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
else
{
lean_dec(v_i_2545_);
lean_dec(v_gen_2526_);
return v___x_2547_;
}
}
case 5:
{
lean_object* v_a_2587_; lean_object* v_b_2588_; lean_object* v___x_2589_; 
v_a_2587_ = lean_ctor_get(v_a_2527_, 0);
lean_inc_ref(v_a_2587_);
v_b_2588_ = lean_ctor_get(v_a_2527_, 1);
lean_inc_ref(v_b_2588_);
lean_dec_ref_known(v_a_2527_, 2);
v___x_2589_ = l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; lean_object* v___x_2591_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_a_2590_);
lean_dec_ref_known(v___x_2589_, 1);
lean_inc(v_gen_2526_);
v___x_2591_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_gen_2526_, v_a_2587_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v___x_2593_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref_known(v___x_2591_, 1);
v___x_2593_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_gen_2526_, v_b_2588_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2602_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2596_ = v___x_2593_;
v_isShared_2597_ = v_isSharedCheck_2602_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2593_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2602_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2598_; lean_object* v___x_2600_; 
v___x_2598_ = l_Lean_mkAppB(v_a_2590_, v_a_2592_, v_a_2594_);
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 0, v___x_2598_);
v___x_2600_ = v___x_2596_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2598_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
else
{
lean_dec(v_a_2592_);
lean_dec(v_a_2590_);
return v___x_2593_;
}
}
else
{
lean_dec(v_a_2590_);
lean_dec_ref(v_b_2588_);
lean_dec(v_gen_2526_);
return v___x_2591_;
}
}
else
{
lean_dec_ref(v_b_2588_);
lean_dec_ref(v_a_2587_);
lean_dec(v_gen_2526_);
return v___x_2589_;
}
}
case 7:
{
lean_object* v_a_2603_; lean_object* v_b_2604_; lean_object* v___x_2605_; 
v_a_2603_ = lean_ctor_get(v_a_2527_, 0);
lean_inc_ref(v_a_2603_);
v_b_2604_ = lean_ctor_get(v_a_2527_, 1);
lean_inc_ref(v_b_2604_);
lean_dec_ref_known(v_a_2527_, 2);
v___x_2605_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; lean_object* v___x_2607_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
lean_inc(v_a_2606_);
lean_dec_ref_known(v___x_2605_, 1);
lean_inc(v_gen_2526_);
v___x_2607_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_gen_2526_, v_a_2603_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2608_; lean_object* v___x_2609_; 
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
lean_inc(v_a_2608_);
lean_dec_ref_known(v___x_2607_, 1);
v___x_2609_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_gen_2526_, v_b_2604_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2618_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2612_ = v___x_2609_;
v_isShared_2613_ = v_isSharedCheck_2618_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2609_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2618_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2614_; lean_object* v___x_2616_; 
v___x_2614_ = l_Lean_mkAppB(v_a_2606_, v_a_2608_, v_a_2610_);
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 0, v___x_2614_);
v___x_2616_ = v___x_2612_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2614_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
else
{
lean_dec(v_a_2608_);
lean_dec(v_a_2606_);
return v___x_2609_;
}
}
else
{
lean_dec(v_a_2606_);
lean_dec_ref(v_b_2604_);
lean_dec(v_gen_2526_);
return v___x_2607_;
}
}
else
{
lean_dec_ref(v_b_2604_);
lean_dec_ref(v_a_2603_);
lean_dec(v_gen_2526_);
return v___x_2605_;
}
}
case 8:
{
lean_object* v_a_2619_; lean_object* v_k_2620_; lean_object* v___x_2621_; 
v_a_2619_ = lean_ctor_get(v_a_2527_, 0);
lean_inc_ref(v_a_2619_);
v_k_2620_ = lean_ctor_get(v_a_2527_, 1);
lean_inc(v_k_2620_);
lean_dec_ref_known(v_a_2527_, 2);
v___x_2621_ = l_Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_a_2622_; lean_object* v___x_2623_; 
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_a_2622_);
lean_dec_ref_known(v___x_2621_, 1);
v___x_2623_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_gen_2526_, v_a_2619_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2633_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2626_ = v___x_2623_;
v_isShared_2627_ = v_isSharedCheck_2633_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2623_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2633_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2631_; 
v___x_2628_ = l_Lean_mkNatLit(v_k_2620_);
v___x_2629_ = l_Lean_mkAppB(v_a_2622_, v_a_2624_, v___x_2628_);
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 0, v___x_2629_);
v___x_2631_ = v___x_2626_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v___x_2629_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
else
{
lean_dec(v_a_2622_);
lean_dec(v_k_2620_);
return v___x_2623_;
}
}
else
{
lean_dec(v_k_2620_);
lean_dec_ref(v_a_2619_);
lean_dec(v_gen_2526_);
return v___x_2621_;
}
}
default: 
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
lean_dec_ref(v_a_2527_);
lean_dec(v_gen_2526_);
v___x_2634_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3);
v___x_2635_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6(v___x_2634_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_);
return v___x_2635_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___boxed(lean_object* v_gen_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_gen_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_);
lean_dec(v_a_2648_);
lean_dec_ref(v_a_2647_);
lean_dec(v_a_2646_);
lean_dec_ref(v_a_2645_);
lean_dec(v_a_2644_);
lean_dec_ref(v_a_2643_);
lean_dec(v_a_2642_);
lean_dec_ref(v_a_2641_);
lean_dec(v_a_2640_);
lean_dec(v_a_2639_);
lean_dec(v_a_2638_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7(lean_object* v_type_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
lean_object* v___x_2664_; 
v___x_2664_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg(v_type_2651_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___boxed(lean_object* v_type_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7(v_type_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec(v___y_2667_);
lean_dec(v___y_2666_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(lean_object* v_e_2679_, lean_object* v_gen_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_){
_start:
{
lean_object* v___x_2693_; 
v___x_2693_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_gen_2680_, v_e_2679_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2695_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2694_);
lean_dec_ref_known(v___x_2693_, 1);
v___x_2695_ = l_Lean_Meta_Sym_shareCommon(v_a_2694_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
return v___x_2695_;
}
else
{
return v___x_2693_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr___boxed(lean_object* v_e_2696_, lean_object* v_gen_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(v_e_2696_, v_gen_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_);
lean_dec(v_a_2708_);
lean_dec_ref(v_a_2707_);
lean_dec(v_a_2706_);
lean_dec_ref(v_a_2705_);
lean_dec(v_a_2704_);
lean_dec_ref(v_a_2703_);
lean_dec(v_a_2702_);
lean_dec_ref(v_a_2701_);
lean_dec(v_a_2700_);
lean_dec(v_a_2699_);
lean_dec(v_a_2698_);
return v_res_2710_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM = _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM);
l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM = _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM);
l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM = _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM);
l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM = _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(builtin);
}
#ifdef __cplusplus
}
#endif
