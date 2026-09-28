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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_161_; lean_object* v_env_162_; lean_object* v___x_163_; lean_object* v_toCold_164_; lean_object* v_mctx_165_; lean_object* v_lctx_166_; lean_object* v_options_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_161_ = lean_st_ref_get(v___y_159_);
v_env_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc_ref(v_env_162_);
lean_dec(v___x_161_);
v___x_163_ = lean_st_ref_get(v___y_157_);
v_toCold_164_ = lean_ctor_get(v___y_158_, 0);
v_mctx_165_ = lean_ctor_get(v___x_163_, 0);
lean_inc_ref(v_mctx_165_);
lean_dec(v___x_163_);
v_lctx_166_ = lean_ctor_get(v___y_156_, 2);
v_options_167_ = lean_ctor_get(v_toCold_164_, 2);
lean_inc_ref(v_options_167_);
lean_inc_ref(v_lctx_166_);
v___x_168_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_168_, 0, v_env_162_);
lean_ctor_set(v___x_168_, 1, v_mctx_165_);
lean_ctor_set(v___x_168_, 2, v_lctx_166_);
lean_ctor_set(v___x_168_, 3, v_options_167_);
v___x_169_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v_msgData_155_);
v___x_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0___boxed(lean_object* v_msgData_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0(v_msgData_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(lean_object* v_msg_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v_ref_184_; lean_object* v___x_185_; lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_194_; 
v_ref_184_ = lean_ctor_get(v___y_181_, 2);
v___x_185_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0(v_msg_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
v_a_186_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_194_ == 0)
{
v___x_188_ = v___x_185_;
v_isShared_189_ = v_isSharedCheck_194_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_185_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_194_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; lean_object* v___x_192_; 
lean_inc(v_ref_184_);
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v_ref_184_);
lean_ctor_set(v___x_190_, 1, v_a_186_);
if (v_isShared_189_ == 0)
{
lean_ctor_set_tag(v___x_188_, 1);
lean_ctor_set(v___x_188_, 0, v___x_190_);
v___x_192_ = v___x_188_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg___boxed(lean_object* v_msg_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v_msg_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
return v_res_201_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__0));
v___x_204_ = l_Lean_stringToMessageData(v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_211_, v_a_214_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_231_; 
v_a_218_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_231_ == 0)
{
v___x_220_ = v___x_217_;
v_isShared_221_ = v_isSharedCheck_231_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_231_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v_semirings_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v_semirings_222_ = lean_ctor_get(v_a_218_, 2);
lean_inc_ref(v_semirings_222_);
lean_dec(v_a_218_);
v___x_223_ = lean_array_get_size(v_semirings_222_);
v___x_224_ = lean_nat_dec_lt(v_a_205_, v___x_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; lean_object* v___x_226_; 
lean_dec_ref(v_semirings_222_);
lean_del_object(v___x_220_);
v___x_225_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1);
v___x_226_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v___x_225_, v_a_212_, v_a_213_, v_a_214_, v_a_215_);
return v___x_226_;
}
else
{
lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_227_ = lean_array_fget(v_semirings_222_, v_a_205_);
lean_dec_ref(v_semirings_222_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 0, v___x_227_);
v___x_229_ = v___x_220_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_227_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
else
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
v_a_232_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_239_ == 0)
{
v___x_234_ = v___x_217_;
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_217_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_232_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___boxed(lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec(v_a_241_);
lean_dec(v_a_240_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0(lean_object* v_00_u03b1_253_, lean_object* v_msg_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v_msg_254_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___boxed(lean_object* v_00_u03b1_268_, lean_object* v_msg_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0(v_00_u03b1_268_, v_msg_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec(v___y_271_);
lean_dec(v___y_270_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0(lean_object* v_a_283_, lean_object* v_f_284_, lean_object* v_s_285_){
_start:
{
lean_object* v_exp_286_; lean_object* v_rings_287_; lean_object* v_semirings_288_; lean_object* v_ncRings_289_; lean_object* v_ncSemirings_290_; lean_object* v_typeClassify_291_; lean_object* v_orders_292_; lean_object* v_typeOrderClassify_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v_exp_286_ = lean_ctor_get(v_s_285_, 0);
v_rings_287_ = lean_ctor_get(v_s_285_, 1);
v_semirings_288_ = lean_ctor_get(v_s_285_, 2);
v_ncRings_289_ = lean_ctor_get(v_s_285_, 3);
v_ncSemirings_290_ = lean_ctor_get(v_s_285_, 4);
v_typeClassify_291_ = lean_ctor_get(v_s_285_, 5);
v_orders_292_ = lean_ctor_get(v_s_285_, 6);
v_typeOrderClassify_293_ = lean_ctor_get(v_s_285_, 7);
v___x_294_ = lean_array_get_size(v_semirings_288_);
v___x_295_ = lean_nat_dec_lt(v_a_283_, v___x_294_);
if (v___x_295_ == 0)
{
lean_dec_ref(v_f_284_);
return v_s_285_;
}
else
{
lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_307_; 
lean_inc_ref(v_typeOrderClassify_293_);
lean_inc_ref(v_orders_292_);
lean_inc_ref(v_typeClassify_291_);
lean_inc_ref(v_ncSemirings_290_);
lean_inc_ref(v_ncRings_289_);
lean_inc_ref(v_semirings_288_);
lean_inc_ref(v_rings_287_);
lean_inc(v_exp_286_);
v_isSharedCheck_307_ = !lean_is_exclusive(v_s_285_);
if (v_isSharedCheck_307_ == 0)
{
lean_object* v_unused_308_; lean_object* v_unused_309_; lean_object* v_unused_310_; lean_object* v_unused_311_; lean_object* v_unused_312_; lean_object* v_unused_313_; lean_object* v_unused_314_; lean_object* v_unused_315_; 
v_unused_308_ = lean_ctor_get(v_s_285_, 7);
lean_dec(v_unused_308_);
v_unused_309_ = lean_ctor_get(v_s_285_, 6);
lean_dec(v_unused_309_);
v_unused_310_ = lean_ctor_get(v_s_285_, 5);
lean_dec(v_unused_310_);
v_unused_311_ = lean_ctor_get(v_s_285_, 4);
lean_dec(v_unused_311_);
v_unused_312_ = lean_ctor_get(v_s_285_, 3);
lean_dec(v_unused_312_);
v_unused_313_ = lean_ctor_get(v_s_285_, 2);
lean_dec(v_unused_313_);
v_unused_314_ = lean_ctor_get(v_s_285_, 1);
lean_dec(v_unused_314_);
v_unused_315_ = lean_ctor_get(v_s_285_, 0);
lean_dec(v_unused_315_);
v___x_297_ = v_s_285_;
v_isShared_298_ = v_isSharedCheck_307_;
goto v_resetjp_296_;
}
else
{
lean_dec(v_s_285_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_307_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v_v_299_; lean_object* v___x_300_; lean_object* v_xs_x27_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_305_; 
v_v_299_ = lean_array_fget(v_semirings_288_, v_a_283_);
v___x_300_ = lean_box(0);
v_xs_x27_301_ = lean_array_fset(v_semirings_288_, v_a_283_, v___x_300_);
v___x_302_ = lean_apply_1(v_f_284_, v_v_299_);
v___x_303_ = lean_array_fset(v_xs_x27_301_, v_a_283_, v___x_302_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 2, v___x_303_);
v___x_305_ = v___x_297_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_exp_286_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v_rings_287_);
lean_ctor_set(v_reuseFailAlloc_306_, 2, v___x_303_);
lean_ctor_set(v_reuseFailAlloc_306_, 3, v_ncRings_289_);
lean_ctor_set(v_reuseFailAlloc_306_, 4, v_ncSemirings_290_);
lean_ctor_set(v_reuseFailAlloc_306_, 5, v_typeClassify_291_);
lean_ctor_set(v_reuseFailAlloc_306_, 6, v_orders_292_);
lean_ctor_set(v_reuseFailAlloc_306_, 7, v_typeOrderClassify_293_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed(lean_object* v_a_316_, lean_object* v_f_317_, lean_object* v_s_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0(v_a_316_, v_f_317_, v_s_318_);
lean_dec(v_a_316_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg(lean_object* v_f_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v___f_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
lean_inc(v_a_321_);
v___f_324_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_324_, 0, v_a_321_);
lean_closure_set(v___f_324_, 1, v_f_320_);
v___x_325_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_326_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_325_, v___f_324_, v_a_322_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___boxed(lean_object* v_f_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg(v_f_327_, v_a_328_, v_a_329_);
lean_dec(v_a_329_);
lean_dec(v_a_328_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring(lean_object* v_f_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
lean_object* v___f_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
lean_inc(v_a_333_);
v___f_345_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_345_, 0, v_a_333_);
lean_closure_set(v___f_345_, 1, v_f_332_);
v___x_346_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_347_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_346_, v___f_345_, v_a_339_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___boxed(lean_object* v_f_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring(v_f_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec(v_a_351_);
lean_dec(v_a_350_);
lean_dec(v_a_349_);
return v_res_361_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_363_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__0));
v___x_364_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___boxed), 12, 0);
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v___x_363_);
return v___x_365_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM(void){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1);
return v___x_366_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__0));
v___x_369_ = l_Lean_stringToMessageData(v___x_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_376_, v_a_379_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; lean_object* v___x_384_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_a_383_);
lean_dec_ref_known(v___x_382_, 1);
v___x_384_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_399_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_399_ == 0)
{
v___x_387_ = v___x_384_;
v_isShared_388_ = v_isSharedCheck_399_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_384_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_399_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v_ringId_389_; lean_object* v_rings_390_; lean_object* v___x_391_; uint8_t v___x_392_; 
v_ringId_389_ = lean_ctor_get(v_a_385_, 1);
lean_inc(v_ringId_389_);
lean_dec(v_a_385_);
v_rings_390_ = lean_ctor_get(v_a_383_, 1);
lean_inc_ref(v_rings_390_);
lean_dec(v_a_383_);
v___x_391_ = lean_array_get_size(v_rings_390_);
v___x_392_ = lean_nat_dec_lt(v_ringId_389_, v___x_391_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec_ref(v_rings_390_);
lean_dec(v_ringId_389_);
lean_del_object(v___x_387_);
v___x_393_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1);
v___x_394_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v___x_393_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
return v___x_394_;
}
else
{
lean_object* v___x_395_; lean_object* v___x_397_; 
v___x_395_ = lean_array_fget(v_rings_390_, v_ringId_389_);
lean_dec(v_ringId_389_);
lean_dec_ref(v_rings_390_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v___x_395_);
v___x_397_ = v___x_387_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_395_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_dec(v_a_383_);
v_a_400_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_384_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_384_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
else
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
v_a_408_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v___x_382_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_382_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_a_408_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___boxed(lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
lean_dec(v_a_418_);
lean_dec(v_a_417_);
lean_dec(v_a_416_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0(lean_object* v_ringId_429_, lean_object* v_f_430_, lean_object* v_s_431_){
_start:
{
lean_object* v_exp_432_; lean_object* v_rings_433_; lean_object* v_semirings_434_; lean_object* v_ncRings_435_; lean_object* v_ncSemirings_436_; lean_object* v_typeClassify_437_; lean_object* v_orders_438_; lean_object* v_typeOrderClassify_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v_exp_432_ = lean_ctor_get(v_s_431_, 0);
v_rings_433_ = lean_ctor_get(v_s_431_, 1);
v_semirings_434_ = lean_ctor_get(v_s_431_, 2);
v_ncRings_435_ = lean_ctor_get(v_s_431_, 3);
v_ncSemirings_436_ = lean_ctor_get(v_s_431_, 4);
v_typeClassify_437_ = lean_ctor_get(v_s_431_, 5);
v_orders_438_ = lean_ctor_get(v_s_431_, 6);
v_typeOrderClassify_439_ = lean_ctor_get(v_s_431_, 7);
v___x_440_ = lean_array_get_size(v_rings_433_);
v___x_441_ = lean_nat_dec_lt(v_ringId_429_, v___x_440_);
if (v___x_441_ == 0)
{
lean_dec_ref(v_f_430_);
return v_s_431_;
}
else
{
lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_453_; 
lean_inc_ref(v_typeOrderClassify_439_);
lean_inc_ref(v_orders_438_);
lean_inc_ref(v_typeClassify_437_);
lean_inc_ref(v_ncSemirings_436_);
lean_inc_ref(v_ncRings_435_);
lean_inc_ref(v_semirings_434_);
lean_inc_ref(v_rings_433_);
lean_inc(v_exp_432_);
v_isSharedCheck_453_ = !lean_is_exclusive(v_s_431_);
if (v_isSharedCheck_453_ == 0)
{
lean_object* v_unused_454_; lean_object* v_unused_455_; lean_object* v_unused_456_; lean_object* v_unused_457_; lean_object* v_unused_458_; lean_object* v_unused_459_; lean_object* v_unused_460_; lean_object* v_unused_461_; 
v_unused_454_ = lean_ctor_get(v_s_431_, 7);
lean_dec(v_unused_454_);
v_unused_455_ = lean_ctor_get(v_s_431_, 6);
lean_dec(v_unused_455_);
v_unused_456_ = lean_ctor_get(v_s_431_, 5);
lean_dec(v_unused_456_);
v_unused_457_ = lean_ctor_get(v_s_431_, 4);
lean_dec(v_unused_457_);
v_unused_458_ = lean_ctor_get(v_s_431_, 3);
lean_dec(v_unused_458_);
v_unused_459_ = lean_ctor_get(v_s_431_, 2);
lean_dec(v_unused_459_);
v_unused_460_ = lean_ctor_get(v_s_431_, 1);
lean_dec(v_unused_460_);
v_unused_461_ = lean_ctor_get(v_s_431_, 0);
lean_dec(v_unused_461_);
v___x_443_ = v_s_431_;
v_isShared_444_ = v_isSharedCheck_453_;
goto v_resetjp_442_;
}
else
{
lean_dec(v_s_431_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_453_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v_v_445_; lean_object* v___x_446_; lean_object* v_xs_x27_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_451_; 
v_v_445_ = lean_array_fget(v_rings_433_, v_ringId_429_);
v___x_446_ = lean_box(0);
v_xs_x27_447_ = lean_array_fset(v_rings_433_, v_ringId_429_, v___x_446_);
v___x_448_ = lean_apply_1(v_f_430_, v_v_445_);
v___x_449_ = lean_array_fset(v_xs_x27_447_, v_ringId_429_, v___x_448_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 1, v___x_449_);
v___x_451_ = v___x_443_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_exp_432_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v___x_449_);
lean_ctor_set(v_reuseFailAlloc_452_, 2, v_semirings_434_);
lean_ctor_set(v_reuseFailAlloc_452_, 3, v_ncRings_435_);
lean_ctor_set(v_reuseFailAlloc_452_, 4, v_ncSemirings_436_);
lean_ctor_set(v_reuseFailAlloc_452_, 5, v_typeClassify_437_);
lean_ctor_set(v_reuseFailAlloc_452_, 6, v_orders_438_);
lean_ctor_set(v_reuseFailAlloc_452_, 7, v_typeOrderClassify_439_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0___boxed(lean_object* v_ringId_462_, lean_object* v_f_463_, lean_object* v_s_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0(v_ringId_462_, v_f_463_, v_s_464_);
lean_dec(v_ringId_462_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(lean_object* v_f_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v_ringId_481_; lean_object* v___f_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_480_);
lean_dec_ref_known(v___x_479_, 1);
v_ringId_481_ = lean_ctor_get(v_a_480_, 1);
lean_inc(v_ringId_481_);
lean_dec(v_a_480_);
v___f_482_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0___boxed), 3, 2);
lean_closure_set(v___f_482_, 0, v_ringId_481_);
lean_closure_set(v___f_482_, 1, v_f_466_);
v___x_483_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_484_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_483_, v___f_482_, v_a_473_);
return v___x_484_;
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
lean_dec_ref(v_f_466_);
v_a_485_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_479_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_479_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___boxed(lean_object* v_f_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v_f_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_);
lean_dec(v_a_504_);
lean_dec_ref(v_a_503_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
lean_dec(v_a_496_);
lean_dec(v_a_495_);
lean_dec(v_a_494_);
return v_res_506_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_508_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__0));
v___x_509_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___boxed), 12, 0);
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
lean_ctor_set(v___x_510_, 1, v___x_508_);
return v___x_510_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM(void){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState___redArg(lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_513_, v_a_514_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_525_; 
v_a_517_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_525_ == 0)
{
v___x_519_ = v___x_516_;
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_516_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_521_ = l_Lean_Meta_Grind_Arith_CommRing_State_getSemiring(v_a_517_, v_a_512_);
lean_dec(v_a_517_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 0, v___x_521_);
v___x_523_ = v___x_519_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
v_a_526_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_516_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_516_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState___redArg___boxed(lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState___redArg(v_a_534_, v_a_535_, v_a_536_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
lean_dec(v_a_534_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState(lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState___redArg(v_a_539_, v_a_540_, v_a_548_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState___boxed(lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState(v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
lean_dec(v_a_554_);
lean_dec(v_a_553_);
lean_dec(v_a_552_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg___lam__0(lean_object* v_a_565_, lean_object* v_f_566_, lean_object* v_s_567_){
_start:
{
lean_object* v_rings_568_; lean_object* v_exprToRingId_569_; lean_object* v_semirings_570_; lean_object* v_exprToSemiringId_571_; lean_object* v_ncRings_572_; lean_object* v_exprToNCRingId_573_; lean_object* v_ncSemirings_574_; lean_object* v_exprToNCSemiringId_575_; lean_object* v_steps_576_; uint8_t v_reportedMaxDegreeIssue_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_598_; 
v_rings_568_ = lean_ctor_get(v_s_567_, 0);
v_exprToRingId_569_ = lean_ctor_get(v_s_567_, 1);
v_semirings_570_ = lean_ctor_get(v_s_567_, 2);
v_exprToSemiringId_571_ = lean_ctor_get(v_s_567_, 3);
v_ncRings_572_ = lean_ctor_get(v_s_567_, 4);
v_exprToNCRingId_573_ = lean_ctor_get(v_s_567_, 5);
v_ncSemirings_574_ = lean_ctor_get(v_s_567_, 6);
v_exprToNCSemiringId_575_ = lean_ctor_get(v_s_567_, 7);
v_steps_576_ = lean_ctor_get(v_s_567_, 8);
v_reportedMaxDegreeIssue_577_ = lean_ctor_get_uint8(v_s_567_, sizeof(void*)*9);
v_isSharedCheck_598_ = !lean_is_exclusive(v_s_567_);
if (v_isSharedCheck_598_ == 0)
{
v___x_579_ = v_s_567_;
v_isShared_580_ = v_isSharedCheck_598_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_steps_576_);
lean_inc(v_exprToNCSemiringId_575_);
lean_inc(v_ncSemirings_574_);
lean_inc(v_exprToNCRingId_573_);
lean_inc(v_ncRings_572_);
lean_inc(v_exprToSemiringId_571_);
lean_inc(v_semirings_570_);
lean_inc(v_exprToRingId_569_);
lean_inc(v_rings_568_);
lean_dec(v_s_567_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_598_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_581_ = lean_unsigned_to_nat(1u);
v___x_582_ = lean_nat_add(v_a_565_, v___x_581_);
v___x_583_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default;
v___x_584_ = l_Array_rightpad___redArg(v___x_582_, v___x_583_, v_semirings_570_);
lean_dec(v___x_582_);
v___x_585_ = lean_array_get_size(v___x_584_);
v___x_586_ = lean_nat_dec_lt(v_a_565_, v___x_585_);
if (v___x_586_ == 0)
{
lean_object* v___x_588_; 
lean_dec_ref(v_f_566_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 2, v___x_584_);
v___x_588_ = v___x_579_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_rings_568_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_exprToRingId_569_);
lean_ctor_set(v_reuseFailAlloc_589_, 2, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_589_, 3, v_exprToSemiringId_571_);
lean_ctor_set(v_reuseFailAlloc_589_, 4, v_ncRings_572_);
lean_ctor_set(v_reuseFailAlloc_589_, 5, v_exprToNCRingId_573_);
lean_ctor_set(v_reuseFailAlloc_589_, 6, v_ncSemirings_574_);
lean_ctor_set(v_reuseFailAlloc_589_, 7, v_exprToNCSemiringId_575_);
lean_ctor_set(v_reuseFailAlloc_589_, 8, v_steps_576_);
lean_ctor_set_uint8(v_reuseFailAlloc_589_, sizeof(void*)*9, v_reportedMaxDegreeIssue_577_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
else
{
lean_object* v_v_590_; lean_object* v___x_591_; lean_object* v_xs_x27_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_596_; 
v_v_590_ = lean_array_fget(v___x_584_, v_a_565_);
v___x_591_ = lean_box(0);
v_xs_x27_592_ = lean_array_fset(v___x_584_, v_a_565_, v___x_591_);
v___x_593_ = lean_apply_1(v_f_566_, v_v_590_);
v___x_594_ = lean_array_fset(v_xs_x27_592_, v_a_565_, v___x_593_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 2, v___x_594_);
v___x_596_ = v___x_579_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_rings_568_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_exprToRingId_569_);
lean_ctor_set(v_reuseFailAlloc_597_, 2, v___x_594_);
lean_ctor_set(v_reuseFailAlloc_597_, 3, v_exprToSemiringId_571_);
lean_ctor_set(v_reuseFailAlloc_597_, 4, v_ncRings_572_);
lean_ctor_set(v_reuseFailAlloc_597_, 5, v_exprToNCRingId_573_);
lean_ctor_set(v_reuseFailAlloc_597_, 6, v_ncSemirings_574_);
lean_ctor_set(v_reuseFailAlloc_597_, 7, v_exprToNCSemiringId_575_);
lean_ctor_set(v_reuseFailAlloc_597_, 8, v_steps_576_);
lean_ctor_set_uint8(v_reuseFailAlloc_597_, sizeof(void*)*9, v_reportedMaxDegreeIssue_577_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg___lam__0___boxed(lean_object* v_a_599_, lean_object* v_f_600_, lean_object* v_s_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg___lam__0(v_a_599_, v_f_600_, v_s_601_);
lean_dec(v_a_599_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg(lean_object* v_f_603_, lean_object* v_a_604_, lean_object* v_a_605_){
_start:
{
lean_object* v___f_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
lean_inc(v_a_604_);
v___f_607_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_607_, 0, v_a_604_);
lean_closure_set(v___f_607_, 1, v_f_603_);
v___x_608_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_609_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_608_, v___f_607_, v_a_605_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg___boxed(lean_object* v_f_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg(v_f_610_, v_a_611_, v_a_612_);
lean_dec(v_a_612_);
lean_dec(v_a_611_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState(lean_object* v_f_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg(v_f_615_, v_a_616_, v_a_617_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___boxed(lean_object* v_f_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState(v_f_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_);
lean_dec(v_a_640_);
lean_dec_ref(v_a_639_);
lean_dec(v_a_638_);
lean_dec_ref(v_a_637_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_635_);
lean_dec(v_a_634_);
lean_dec_ref(v_a_633_);
lean_dec(v_a_632_);
lean_dec(v_a_631_);
lean_dec(v_a_630_);
return v_res_642_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM___closed__1(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM___closed__0));
v___x_645_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState___boxed), 12, 0);
v___x_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set(v___x_646_, 1, v___x_644_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM(void){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM___closed__1);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_648_, lean_object* v_vals_649_, lean_object* v_i_650_, lean_object* v_k_651_){
_start:
{
lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_652_ = lean_array_get_size(v_keys_648_);
v___x_653_ = lean_nat_dec_lt(v_i_650_, v___x_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; 
lean_dec(v_i_650_);
v___x_654_ = lean_box(0);
return v___x_654_;
}
else
{
lean_object* v_k_x27_655_; size_t v___x_656_; size_t v___x_657_; uint8_t v___x_658_; 
v_k_x27_655_ = lean_array_fget_borrowed(v_keys_648_, v_i_650_);
v___x_656_ = lean_ptr_addr(v_k_651_);
v___x_657_ = lean_ptr_addr(v_k_x27_655_);
v___x_658_ = lean_usize_dec_eq(v___x_656_, v___x_657_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_unsigned_to_nat(1u);
v___x_660_ = lean_nat_add(v_i_650_, v___x_659_);
lean_dec(v_i_650_);
v_i_650_ = v___x_660_;
goto _start;
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = lean_array_fget_borrowed(v_vals_649_, v_i_650_);
lean_dec(v_i_650_);
lean_inc(v___x_662_);
v___x_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
return v___x_663_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_664_, lean_object* v_vals_665_, lean_object* v_i_666_, lean_object* v_k_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_664_, v_vals_665_, v_i_666_, v_k_667_);
lean_dec_ref(v_k_667_);
lean_dec_ref(v_vals_665_);
lean_dec_ref(v_keys_664_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(lean_object* v_x_669_, size_t v_x_670_, lean_object* v_x_671_){
_start:
{
if (lean_obj_tag(v_x_669_) == 0)
{
lean_object* v_es_672_; lean_object* v___x_673_; size_t v___x_674_; size_t v___x_675_; lean_object* v_j_676_; lean_object* v___x_677_; 
v_es_672_ = lean_ctor_get(v_x_669_, 0);
v___x_673_ = lean_box(2);
v___x_674_ = ((size_t)31ULL);
v___x_675_ = lean_usize_land(v_x_670_, v___x_674_);
v_j_676_ = lean_usize_to_nat(v___x_675_);
v___x_677_ = lean_array_get_borrowed(v___x_673_, v_es_672_, v_j_676_);
lean_dec(v_j_676_);
switch(lean_obj_tag(v___x_677_))
{
case 0:
{
lean_object* v_key_678_; lean_object* v_val_679_; size_t v___x_680_; size_t v___x_681_; uint8_t v___x_682_; 
v_key_678_ = lean_ctor_get(v___x_677_, 0);
v_val_679_ = lean_ctor_get(v___x_677_, 1);
v___x_680_ = lean_ptr_addr(v_x_671_);
v___x_681_ = lean_ptr_addr(v_key_678_);
v___x_682_ = lean_usize_dec_eq(v___x_680_, v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; 
v___x_683_ = lean_box(0);
return v___x_683_;
}
else
{
lean_object* v___x_684_; 
lean_inc(v_val_679_);
v___x_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_684_, 0, v_val_679_);
return v___x_684_;
}
}
case 1:
{
lean_object* v_node_685_; size_t v___x_686_; size_t v___x_687_; 
v_node_685_ = lean_ctor_get(v___x_677_, 0);
v___x_686_ = ((size_t)5ULL);
v___x_687_ = lean_usize_shift_right(v_x_670_, v___x_686_);
v_x_669_ = v_node_685_;
v_x_670_ = v___x_687_;
goto _start;
}
default: 
{
lean_object* v___x_689_; 
v___x_689_ = lean_box(0);
return v___x_689_;
}
}
}
else
{
lean_object* v_ks_690_; lean_object* v_vs_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v_ks_690_ = lean_ctor_get(v_x_669_, 0);
v_vs_691_ = lean_ctor_get(v_x_669_, 1);
v___x_692_ = lean_unsigned_to_nat(0u);
v___x_693_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_690_, v_vs_691_, v___x_692_, v_x_671_);
return v___x_693_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_694_, lean_object* v_x_695_, lean_object* v_x_696_){
_start:
{
size_t v_x_905__boxed_697_; lean_object* v_res_698_; 
v_x_905__boxed_697_ = lean_unbox_usize(v_x_695_);
lean_dec(v_x_695_);
v_res_698_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_694_, v_x_905__boxed_697_, v_x_696_);
lean_dec_ref(v_x_696_);
lean_dec_ref(v_x_694_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(lean_object* v_x_699_, lean_object* v_x_700_){
_start:
{
size_t v___x_701_; size_t v___x_702_; size_t v___x_703_; uint64_t v___x_704_; size_t v___x_705_; lean_object* v___x_706_; 
v___x_701_ = lean_ptr_addr(v_x_700_);
v___x_702_ = ((size_t)3ULL);
v___x_703_ = lean_usize_shift_right(v___x_701_, v___x_702_);
v___x_704_ = lean_usize_to_uint64(v___x_703_);
v___x_705_ = lean_uint64_to_usize(v___x_704_);
v___x_706_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_699_, v___x_705_, v_x_700_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg___boxed(lean_object* v_x_707_, lean_object* v_x_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_x_707_, v_x_708_);
lean_dec_ref(v_x_708_);
lean_dec_ref(v_x_707_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(lean_object* v_e_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_711_, v_a_712_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_724_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_724_ == 0)
{
v___x_717_ = v___x_714_;
v_isShared_718_ = v_isSharedCheck_724_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_724_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v_exprToSemiringId_719_; lean_object* v___x_720_; lean_object* v___x_722_; 
v_exprToSemiringId_719_ = lean_ctor_get(v_a_715_, 3);
lean_inc_ref(v_exprToSemiringId_719_);
lean_dec(v_a_715_);
v___x_720_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_exprToSemiringId_719_, v_e_710_);
lean_dec_ref(v_exprToSemiringId_719_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_720_);
v___x_722_ = v___x_717_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
v_a_725_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_714_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_714_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg___boxed(lean_object* v_e_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_733_, v_a_734_, v_a_735_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_e_733_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f(lean_object* v_e_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_738_, v_a_739_, v_a_747_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___boxed(lean_object* v_e_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f(v_e_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_a_759_);
lean_dec_ref(v_a_758_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
lean_dec(v_a_753_);
lean_dec(v_a_752_);
lean_dec_ref(v_e_751_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0(lean_object* v_00_u03b2_764_, lean_object* v_x_765_, lean_object* v_x_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_x_765_, v_x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___boxed(lean_object* v_00_u03b2_768_, lean_object* v_x_769_, lean_object* v_x_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0(v_00_u03b2_768_, v_x_769_, v_x_770_);
lean_dec_ref(v_x_770_);
lean_dec_ref(v_x_769_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_772_, lean_object* v_x_773_, size_t v_x_774_, lean_object* v_x_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_773_, v_x_774_, v_x_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_777_, lean_object* v_x_778_, lean_object* v_x_779_, lean_object* v_x_780_){
_start:
{
size_t v_x_1026__boxed_781_; lean_object* v_res_782_; 
v_x_1026__boxed_781_ = lean_unbox_usize(v_x_779_);
lean_dec(v_x_779_);
v_res_782_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0(v_00_u03b2_777_, v_x_778_, v_x_1026__boxed_781_, v_x_780_);
lean_dec_ref(v_x_780_);
lean_dec_ref(v_x_778_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_783_, lean_object* v_keys_784_, lean_object* v_vals_785_, lean_object* v_heq_786_, lean_object* v_i_787_, lean_object* v_k_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_784_, v_vals_785_, v_i_787_, v_k_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_790_, lean_object* v_keys_791_, lean_object* v_vals_792_, lean_object* v_heq_793_, lean_object* v_i_794_, lean_object* v_k_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_790_, v_keys_791_, v_vals_792_, v_heq_793_, v_i_794_, v_k_795_);
lean_dec_ref(v_k_795_);
lean_dec_ref(v_vals_792_);
lean_dec_ref(v_keys_791_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_797_, lean_object* v_x_798_, lean_object* v_x_799_, lean_object* v_x_800_){
_start:
{
lean_object* v_ks_801_; lean_object* v_vs_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_828_; 
v_ks_801_ = lean_ctor_get(v_x_797_, 0);
v_vs_802_ = lean_ctor_get(v_x_797_, 1);
v_isSharedCheck_828_ = !lean_is_exclusive(v_x_797_);
if (v_isSharedCheck_828_ == 0)
{
v___x_804_ = v_x_797_;
v_isShared_805_ = v_isSharedCheck_828_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_vs_802_);
lean_inc(v_ks_801_);
lean_dec(v_x_797_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_828_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; uint8_t v___x_807_; 
v___x_806_ = lean_array_get_size(v_ks_801_);
v___x_807_ = lean_nat_dec_lt(v_x_798_, v___x_806_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_811_; 
lean_dec(v_x_798_);
v___x_808_ = lean_array_push(v_ks_801_, v_x_799_);
v___x_809_ = lean_array_push(v_vs_802_, v_x_800_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 1, v___x_809_);
lean_ctor_set(v___x_804_, 0, v___x_808_);
v___x_811_ = v___x_804_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
else
{
lean_object* v_k_x27_813_; size_t v___x_814_; size_t v___x_815_; uint8_t v___x_816_; 
v_k_x27_813_ = lean_array_fget_borrowed(v_ks_801_, v_x_798_);
v___x_814_ = lean_ptr_addr(v_x_799_);
v___x_815_ = lean_ptr_addr(v_k_x27_813_);
v___x_816_ = lean_usize_dec_eq(v___x_814_, v___x_815_);
if (v___x_816_ == 0)
{
lean_object* v___x_818_; 
if (v_isShared_805_ == 0)
{
v___x_818_ = v___x_804_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_ks_801_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_vs_802_);
v___x_818_ = v_reuseFailAlloc_822_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = lean_unsigned_to_nat(1u);
v___x_820_ = lean_nat_add(v_x_798_, v___x_819_);
lean_dec(v_x_798_);
v_x_797_ = v___x_818_;
v_x_798_ = v___x_820_;
goto _start;
}
}
else
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_826_; 
v___x_823_ = lean_array_fset(v_ks_801_, v_x_798_, v_x_799_);
v___x_824_ = lean_array_fset(v_vs_802_, v_x_798_, v_x_800_);
lean_dec(v_x_798_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 1, v___x_824_);
lean_ctor_set(v___x_804_, 0, v___x_823_);
v___x_826_ = v___x_804_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_823_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v___x_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_829_, lean_object* v_k_830_, lean_object* v_v_831_){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = lean_unsigned_to_nat(0u);
v___x_833_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_829_, v___x_832_, v_k_830_, v_v_831_);
return v___x_833_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(lean_object* v_x_835_, size_t v_x_836_, size_t v_x_837_, lean_object* v_x_838_, lean_object* v_x_839_){
_start:
{
if (lean_obj_tag(v_x_835_) == 0)
{
lean_object* v_es_840_; size_t v___x_841_; size_t v___x_842_; lean_object* v_j_843_; lean_object* v___x_844_; uint8_t v___x_845_; 
v_es_840_ = lean_ctor_get(v_x_835_, 0);
v___x_841_ = ((size_t)31ULL);
v___x_842_ = lean_usize_land(v_x_836_, v___x_841_);
v_j_843_ = lean_usize_to_nat(v___x_842_);
v___x_844_ = lean_array_get_size(v_es_840_);
v___x_845_ = lean_nat_dec_lt(v_j_843_, v___x_844_);
if (v___x_845_ == 0)
{
lean_dec(v_j_843_);
lean_dec(v_x_839_);
lean_dec_ref(v_x_838_);
return v_x_835_;
}
else
{
lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_886_; 
lean_inc_ref(v_es_840_);
v_isSharedCheck_886_ = !lean_is_exclusive(v_x_835_);
if (v_isSharedCheck_886_ == 0)
{
lean_object* v_unused_887_; 
v_unused_887_ = lean_ctor_get(v_x_835_, 0);
lean_dec(v_unused_887_);
v___x_847_ = v_x_835_;
v_isShared_848_ = v_isSharedCheck_886_;
goto v_resetjp_846_;
}
else
{
lean_dec(v_x_835_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_886_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v_v_849_; lean_object* v___x_850_; lean_object* v_xs_x27_851_; lean_object* v___y_853_; 
v_v_849_ = lean_array_fget(v_es_840_, v_j_843_);
v___x_850_ = lean_box(0);
v_xs_x27_851_ = lean_array_fset(v_es_840_, v_j_843_, v___x_850_);
switch(lean_obj_tag(v_v_849_))
{
case 0:
{
lean_object* v_key_858_; lean_object* v_val_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_871_; 
v_key_858_ = lean_ctor_get(v_v_849_, 0);
v_val_859_ = lean_ctor_get(v_v_849_, 1);
v_isSharedCheck_871_ = !lean_is_exclusive(v_v_849_);
if (v_isSharedCheck_871_ == 0)
{
v___x_861_ = v_v_849_;
v_isShared_862_ = v_isSharedCheck_871_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_val_859_);
lean_inc(v_key_858_);
lean_dec(v_v_849_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_871_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
size_t v___x_863_; size_t v___x_864_; uint8_t v___x_865_; 
v___x_863_ = lean_ptr_addr(v_x_838_);
v___x_864_ = lean_ptr_addr(v_key_858_);
v___x_865_ = lean_usize_dec_eq(v___x_863_, v___x_864_);
if (v___x_865_ == 0)
{
lean_object* v___x_866_; lean_object* v___x_867_; 
lean_del_object(v___x_861_);
v___x_866_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_858_, v_val_859_, v_x_838_, v_x_839_);
v___x_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
v___y_853_ = v___x_867_;
goto v___jp_852_;
}
else
{
lean_object* v___x_869_; 
lean_dec(v_val_859_);
lean_dec(v_key_858_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 1, v_x_839_);
lean_ctor_set(v___x_861_, 0, v_x_838_);
v___x_869_ = v___x_861_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_x_838_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_x_839_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
v___y_853_ = v___x_869_;
goto v___jp_852_;
}
}
}
}
case 1:
{
lean_object* v_node_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_884_; 
v_node_872_ = lean_ctor_get(v_v_849_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v_v_849_);
if (v_isSharedCheck_884_ == 0)
{
v___x_874_ = v_v_849_;
v_isShared_875_ = v_isSharedCheck_884_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_node_872_);
lean_dec(v_v_849_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_884_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
size_t v___x_876_; size_t v___x_877_; size_t v___x_878_; size_t v___x_879_; lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_876_ = ((size_t)5ULL);
v___x_877_ = lean_usize_shift_right(v_x_836_, v___x_876_);
v___x_878_ = ((size_t)1ULL);
v___x_879_ = lean_usize_add(v_x_837_, v___x_878_);
v___x_880_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_node_872_, v___x_877_, v___x_879_, v_x_838_, v_x_839_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_880_);
v___x_882_ = v___x_874_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_880_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
v___y_853_ = v___x_882_;
goto v___jp_852_;
}
}
}
default: 
{
lean_object* v___x_885_; 
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v_x_838_);
lean_ctor_set(v___x_885_, 1, v_x_839_);
v___y_853_ = v___x_885_;
goto v___jp_852_;
}
}
v___jp_852_:
{
lean_object* v___x_854_; lean_object* v___x_856_; 
v___x_854_ = lean_array_fset(v_xs_x27_851_, v_j_843_, v___y_853_);
lean_dec(v_j_843_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_854_);
v___x_856_ = v___x_847_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
}
else
{
lean_object* v_ks_888_; lean_object* v_vs_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_907_; 
v_ks_888_ = lean_ctor_get(v_x_835_, 0);
v_vs_889_ = lean_ctor_get(v_x_835_, 1);
v_isSharedCheck_907_ = !lean_is_exclusive(v_x_835_);
if (v_isSharedCheck_907_ == 0)
{
v___x_891_ = v_x_835_;
v_isShared_892_ = v_isSharedCheck_907_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_vs_889_);
lean_inc(v_ks_888_);
lean_dec(v_x_835_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_907_;
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
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_ks_888_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_vs_889_);
v___x_894_ = v_reuseFailAlloc_906_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v_newNode_895_; size_t v___x_896_; uint8_t v___x_897_; 
v_newNode_895_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(v___x_894_, v_x_838_, v_x_839_);
v___x_896_ = ((size_t)7ULL);
v___x_897_ = lean_usize_dec_le(v___x_896_, v_x_837_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; lean_object* v___x_899_; uint8_t v___x_900_; 
v___x_898_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_895_);
v___x_899_ = lean_unsigned_to_nat(4u);
v___x_900_ = lean_nat_dec_lt(v___x_898_, v___x_899_);
lean_dec(v___x_898_);
if (v___x_900_ == 0)
{
lean_object* v_ks_901_; lean_object* v_vs_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v_ks_901_ = lean_ctor_get(v_newNode_895_, 0);
lean_inc_ref(v_ks_901_);
v_vs_902_ = lean_ctor_get(v_newNode_895_, 1);
lean_inc_ref(v_vs_902_);
lean_dec_ref(v_newNode_895_);
v___x_903_ = lean_unsigned_to_nat(0u);
v___x_904_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0);
v___x_905_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_x_837_, v_ks_901_, v_vs_902_, v___x_903_, v___x_904_);
lean_dec_ref(v_vs_902_);
lean_dec_ref(v_ks_901_);
return v___x_905_;
}
else
{
return v_newNode_895_;
}
}
else
{
return v_newNode_895_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(size_t v_depth_908_, lean_object* v_keys_909_, lean_object* v_vals_910_, lean_object* v_i_911_, lean_object* v_entries_912_){
_start:
{
lean_object* v___x_913_; uint8_t v___x_914_; 
v___x_913_ = lean_array_get_size(v_keys_909_);
v___x_914_ = lean_nat_dec_lt(v_i_911_, v___x_913_);
if (v___x_914_ == 0)
{
lean_dec(v_i_911_);
return v_entries_912_;
}
else
{
lean_object* v_k_915_; lean_object* v_v_916_; size_t v___x_917_; size_t v___x_918_; size_t v___x_919_; uint64_t v___x_920_; size_t v_h_921_; size_t v___x_922_; lean_object* v___x_923_; size_t v___x_924_; size_t v___x_925_; size_t v___x_926_; size_t v_h_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v_k_915_ = lean_array_fget_borrowed(v_keys_909_, v_i_911_);
v_v_916_ = lean_array_fget_borrowed(v_vals_910_, v_i_911_);
v___x_917_ = lean_ptr_addr(v_k_915_);
v___x_918_ = ((size_t)3ULL);
v___x_919_ = lean_usize_shift_right(v___x_917_, v___x_918_);
v___x_920_ = lean_usize_to_uint64(v___x_919_);
v_h_921_ = lean_uint64_to_usize(v___x_920_);
v___x_922_ = ((size_t)5ULL);
v___x_923_ = lean_unsigned_to_nat(1u);
v___x_924_ = ((size_t)1ULL);
v___x_925_ = lean_usize_sub(v_depth_908_, v___x_924_);
v___x_926_ = lean_usize_mul(v___x_922_, v___x_925_);
v_h_927_ = lean_usize_shift_right(v_h_921_, v___x_926_);
v___x_928_ = lean_nat_add(v_i_911_, v___x_923_);
lean_dec(v_i_911_);
lean_inc(v_v_916_);
lean_inc(v_k_915_);
v___x_929_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_entries_912_, v_h_927_, v_depth_908_, v_k_915_, v_v_916_);
v_i_911_ = v___x_928_;
v_entries_912_ = v___x_929_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_931_, lean_object* v_keys_932_, lean_object* v_vals_933_, lean_object* v_i_934_, lean_object* v_entries_935_){
_start:
{
size_t v_depth_boxed_936_; lean_object* v_res_937_; 
v_depth_boxed_936_ = lean_unbox_usize(v_depth_931_);
lean_dec(v_depth_931_);
v_res_937_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_936_, v_keys_932_, v_vals_933_, v_i_934_, v_entries_935_);
lean_dec_ref(v_vals_933_);
lean_dec_ref(v_keys_932_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___boxed(lean_object* v_x_938_, lean_object* v_x_939_, lean_object* v_x_940_, lean_object* v_x_941_, lean_object* v_x_942_){
_start:
{
size_t v_x_6465__boxed_943_; size_t v_x_6466__boxed_944_; lean_object* v_res_945_; 
v_x_6465__boxed_943_ = lean_unbox_usize(v_x_939_);
lean_dec(v_x_939_);
v_x_6466__boxed_944_ = lean_unbox_usize(v_x_940_);
lean_dec(v_x_940_);
v_res_945_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_938_, v_x_6465__boxed_943_, v_x_6466__boxed_944_, v_x_941_, v_x_942_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(lean_object* v_x_946_, lean_object* v_x_947_, lean_object* v_x_948_){
_start:
{
size_t v___x_949_; size_t v___x_950_; size_t v___x_951_; uint64_t v___x_952_; size_t v___x_953_; size_t v___x_954_; lean_object* v___x_955_; 
v___x_949_ = lean_ptr_addr(v_x_947_);
v___x_950_ = ((size_t)3ULL);
v___x_951_ = lean_usize_shift_right(v___x_949_, v___x_950_);
v___x_952_ = lean_usize_to_uint64(v___x_951_);
v___x_953_ = lean_uint64_to_usize(v___x_952_);
v___x_954_ = ((size_t)1ULL);
v___x_955_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_946_, v___x_953_, v___x_954_, v_x_947_, v_x_948_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0(lean_object* v_e_956_, lean_object* v_a_957_, lean_object* v_s_958_){
_start:
{
lean_object* v_rings_959_; lean_object* v_exprToRingId_960_; lean_object* v_semirings_961_; lean_object* v_exprToSemiringId_962_; lean_object* v_ncRings_963_; lean_object* v_exprToNCRingId_964_; lean_object* v_ncSemirings_965_; lean_object* v_exprToNCSemiringId_966_; lean_object* v_steps_967_; uint8_t v_reportedMaxDegreeIssue_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_976_; 
v_rings_959_ = lean_ctor_get(v_s_958_, 0);
v_exprToRingId_960_ = lean_ctor_get(v_s_958_, 1);
v_semirings_961_ = lean_ctor_get(v_s_958_, 2);
v_exprToSemiringId_962_ = lean_ctor_get(v_s_958_, 3);
v_ncRings_963_ = lean_ctor_get(v_s_958_, 4);
v_exprToNCRingId_964_ = lean_ctor_get(v_s_958_, 5);
v_ncSemirings_965_ = lean_ctor_get(v_s_958_, 6);
v_exprToNCSemiringId_966_ = lean_ctor_get(v_s_958_, 7);
v_steps_967_ = lean_ctor_get(v_s_958_, 8);
v_reportedMaxDegreeIssue_968_ = lean_ctor_get_uint8(v_s_958_, sizeof(void*)*9);
v_isSharedCheck_976_ = !lean_is_exclusive(v_s_958_);
if (v_isSharedCheck_976_ == 0)
{
v___x_970_ = v_s_958_;
v_isShared_971_ = v_isSharedCheck_976_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_steps_967_);
lean_inc(v_exprToNCSemiringId_966_);
lean_inc(v_ncSemirings_965_);
lean_inc(v_exprToNCRingId_964_);
lean_inc(v_ncRings_963_);
lean_inc(v_exprToSemiringId_962_);
lean_inc(v_semirings_961_);
lean_inc(v_exprToRingId_960_);
lean_inc(v_rings_959_);
lean_dec(v_s_958_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_976_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v___x_974_; 
lean_inc(v_a_957_);
v___x_972_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_exprToSemiringId_962_, v_e_956_, v_a_957_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 3, v___x_972_);
v___x_974_ = v___x_970_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_rings_959_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_exprToRingId_960_);
lean_ctor_set(v_reuseFailAlloc_975_, 2, v_semirings_961_);
lean_ctor_set(v_reuseFailAlloc_975_, 3, v___x_972_);
lean_ctor_set(v_reuseFailAlloc_975_, 4, v_ncRings_963_);
lean_ctor_set(v_reuseFailAlloc_975_, 5, v_exprToNCRingId_964_);
lean_ctor_set(v_reuseFailAlloc_975_, 6, v_ncSemirings_965_);
lean_ctor_set(v_reuseFailAlloc_975_, 7, v_exprToNCSemiringId_966_);
lean_ctor_set(v_reuseFailAlloc_975_, 8, v_steps_967_);
lean_ctor_set_uint8(v_reuseFailAlloc_975_, sizeof(void*)*9, v_reportedMaxDegreeIssue_968_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0___boxed(lean_object* v_e_977_, lean_object* v_a_978_, lean_object* v_s_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0(v_e_977_, v_a_978_, v_s_979_);
lean_dec(v_a_978_);
return v_res_980_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1(void){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__0));
v___x_983_ = l_Lean_stringToMessageData(v___x_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(lean_object* v_e_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_){
_start:
{
lean_object* v___f_997_; lean_object* v___x_998_; 
lean_inc(v_a_985_);
lean_inc_ref(v_e_984_);
v___f_997_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_997_, 0, v_e_984_);
lean_closure_set(v___f_997_, 1, v_a_985_);
v___x_998_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_984_, v_a_986_, v_a_991_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref_known(v___x_998_, 1);
if (lean_obj_tag(v_a_999_) == 1)
{
lean_object* v_val_1000_; uint8_t v___x_1001_; 
lean_dec_ref(v___f_997_);
v_val_1000_ = lean_ctor_get(v_a_999_, 0);
lean_inc(v_val_1000_);
lean_dec_ref_known(v_a_999_, 1);
v___x_1001_ = lean_nat_dec_eq(v_val_1000_, v_a_985_);
lean_dec(v_val_1000_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1002_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1);
v___x_1003_ = l_Lean_indentExpr(v_e_984_);
v___x_1004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1002_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_987_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; uint8_t v_verbose_1007_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___x_1005_, 1);
v_verbose_1007_ = lean_ctor_get_uint8(v_a_1006_, 0);
lean_dec(v_a_1006_);
if (v_verbose_1007_ == 0)
{
lean_dec_ref_known(v___x_1004_, 2);
goto v___jp_994_;
}
else
{
lean_object* v___x_1008_; 
v___x_1008_ = l_Lean_Meta_Sym_reportIssue(v___x_1004_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_dec_ref_known(v___x_1008_, 1);
goto v___jp_994_;
}
else
{
return v___x_1008_;
}
}
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
lean_dec_ref_known(v___x_1004_, 2);
v_a_1009_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_1005_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1005_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
else
{
lean_dec_ref(v_e_984_);
goto v___jp_994_;
}
}
else
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
lean_dec(v_a_999_);
lean_dec_ref(v_e_984_);
v___x_1017_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1018_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1017_, v___f_997_, v_a_986_);
return v___x_1018_;
}
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec_ref(v___f_997_);
lean_dec_ref(v_e_984_);
v_a_1019_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_998_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_998_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
v___jp_994_:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = lean_box(0);
v___x_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
return v___x_996_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___boxed(lean_object* v_e_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
lean_dec(v_a_1033_);
lean_dec_ref(v_a_1032_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
lean_dec(v_a_1029_);
lean_dec(v_a_1028_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(lean_object* v_e_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1038_, v_a_1039_, v_a_1040_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___boxed(lean_object* v_e_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(v_e_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec(v_a_1054_);
lean_dec(v_a_1053_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0(lean_object* v_00_u03b2_1066_, lean_object* v_x_1067_, lean_object* v_x_1068_, lean_object* v_x_1069_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_x_1067_, v_x_1068_, v_x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(lean_object* v_00_u03b2_1071_, lean_object* v_x_1072_, size_t v_x_1073_, size_t v_x_1074_, lean_object* v_x_1075_, lean_object* v_x_1076_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_1072_, v_x_1073_, v_x_1074_, v_x_1075_, v_x_1076_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1078_, lean_object* v_x_1079_, lean_object* v_x_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_, lean_object* v_x_1083_){
_start:
{
size_t v_x_6751__boxed_1084_; size_t v_x_6752__boxed_1085_; lean_object* v_res_1086_; 
v_x_6751__boxed_1084_ = lean_unbox_usize(v_x_1080_);
lean_dec(v_x_1080_);
v_x_6752__boxed_1085_ = lean_unbox_usize(v_x_1081_);
lean_dec(v_x_1081_);
v_res_1086_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(v_00_u03b2_1078_, v_x_1079_, v_x_6751__boxed_1084_, v_x_6752__boxed_1085_, v_x_1082_, v_x_1083_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1087_, lean_object* v_n_1088_, lean_object* v_k_1089_, lean_object* v_v_1090_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(v_n_1088_, v_k_1089_, v_v_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1092_, size_t v_depth_1093_, lean_object* v_keys_1094_, lean_object* v_vals_1095_, lean_object* v_heq_1096_, lean_object* v_i_1097_, lean_object* v_entries_1098_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_1093_, v_keys_1094_, v_vals_1095_, v_i_1097_, v_entries_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1100_, lean_object* v_depth_1101_, lean_object* v_keys_1102_, lean_object* v_vals_1103_, lean_object* v_heq_1104_, lean_object* v_i_1105_, lean_object* v_entries_1106_){
_start:
{
size_t v_depth_boxed_1107_; lean_object* v_res_1108_; 
v_depth_boxed_1107_ = lean_unbox_usize(v_depth_1101_);
lean_dec(v_depth_1101_);
v_res_1108_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(v_00_u03b2_1100_, v_depth_boxed_1107_, v_keys_1102_, v_vals_1103_, v_heq_1104_, v_i_1105_, v_entries_1106_);
lean_dec_ref(v_vals_1103_);
lean_dec_ref(v_keys_1102_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1109_, lean_object* v_x_1110_, lean_object* v_x_1111_, lean_object* v_x_1112_, lean_object* v_x_1113_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1110_, v_x_1111_, v_x_1112_, v_x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0(lean_object* v_e_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1115_, v___y_1116_, v___y_1117_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0___boxed(lean_object* v_e_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0(v_e_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec(v___y_1130_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0(lean_object* v_e_1145_, lean_object* v___f_1146_, lean_object* v___f_1147_, lean_object* v_size_1148_, lean_object* v_s_1149_){
_start:
{
lean_object* v_denote_1150_; lean_object* v_vars_1151_; lean_object* v_varMap_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1161_; 
v_denote_1150_ = lean_ctor_get(v_s_1149_, 0);
v_vars_1151_ = lean_ctor_get(v_s_1149_, 1);
v_varMap_1152_ = lean_ctor_get(v_s_1149_, 2);
v_isSharedCheck_1161_ = !lean_is_exclusive(v_s_1149_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1154_ = v_s_1149_;
v_isShared_1155_ = v_isSharedCheck_1161_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_varMap_1152_);
lean_inc(v_vars_1151_);
lean_inc(v_denote_1150_);
lean_dec(v_s_1149_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1161_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1159_; 
lean_inc_ref(v_e_1145_);
v___x_1156_ = l_Lean_PersistentArray_push___redArg(v_vars_1151_, v_e_1145_);
v___x_1157_ = l_Lean_PersistentHashMap_insert___redArg(v___f_1146_, v___f_1147_, v_varMap_1152_, v_e_1145_, v_size_1148_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 2, v___x_1157_);
lean_ctor_set(v___x_1154_, 1, v___x_1156_);
v___x_1159_ = v___x_1154_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_denote_1150_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1160_, 2, v___x_1157_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__1(lean_object* v_toPure_1162_, lean_object* v_size_1163_, lean_object* v_____r_1164_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_apply_2(v_toPure_1162_, lean_box(0), v_size_1163_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2(lean_object* v_e_1166_, lean_object* v_inst_1167_, lean_object* v_toBind_1168_, lean_object* v___f_1169_, lean_object* v_____r_1170_){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1171_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1172_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SolverExtension_markTerm___boxed), 14, 3);
lean_closure_set(v___x_1172_, 0, lean_box(0));
lean_closure_set(v___x_1172_, 1, v___x_1171_);
lean_closure_set(v___x_1172_, 2, v_e_1166_);
v___x_1173_ = lean_apply_2(v_inst_1167_, lean_box(0), v___x_1172_);
v___x_1174_ = lean_apply_4(v_toBind_1168_, lean_box(0), lean_box(0), v___x_1173_, v___f_1169_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3(lean_object* v_inst_1175_, lean_object* v_e_1176_, lean_object* v_toBind_1177_, lean_object* v___f_1178_, lean_object* v_____r_1179_){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = lean_apply_1(v_inst_1175_, v_e_1176_);
v___x_1181_ = lean_apply_4(v_toBind_1177_, lean_box(0), lean_box(0), v___x_1180_, v___f_1178_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4(lean_object* v___f_1182_, lean_object* v___f_1183_, lean_object* v_e_1184_, lean_object* v_toPure_1185_, lean_object* v_inst_1186_, lean_object* v_toBind_1187_, lean_object* v_inst_1188_, lean_object* v_modifySemiringState_1189_, lean_object* v_s_1190_){
_start:
{
lean_object* v_vars_1191_; lean_object* v_varMap_1192_; lean_object* v___x_1193_; 
v_vars_1191_ = lean_ctor_get(v_s_1190_, 1);
lean_inc_ref(v_vars_1191_);
v_varMap_1192_ = lean_ctor_get(v_s_1190_, 2);
lean_inc_ref(v_varMap_1192_);
lean_dec_ref(v_s_1190_);
lean_inc_ref(v_e_1184_);
lean_inc_ref(v___f_1183_);
lean_inc_ref(v___f_1182_);
v___x_1193_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_1182_, v___f_1183_, v_varMap_1192_, v_e_1184_);
lean_dec_ref(v_varMap_1192_);
if (lean_obj_tag(v___x_1193_) == 1)
{
lean_object* v_val_1194_; lean_object* v___x_1195_; 
lean_dec_ref(v_vars_1191_);
lean_dec(v_modifySemiringState_1189_);
lean_dec(v_inst_1188_);
lean_dec(v_toBind_1187_);
lean_dec(v_inst_1186_);
lean_dec_ref(v_e_1184_);
lean_dec_ref(v___f_1183_);
lean_dec_ref(v___f_1182_);
v_val_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_val_1194_);
lean_dec_ref_known(v___x_1193_, 1);
v___x_1195_ = lean_apply_2(v_toPure_1185_, lean_box(0), v_val_1194_);
return v___x_1195_;
}
else
{
lean_object* v_size_1196_; lean_object* v___f_1197_; lean_object* v___f_1198_; lean_object* v___f_1199_; lean_object* v___f_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
lean_dec(v___x_1193_);
v_size_1196_ = lean_ctor_get(v_vars_1191_, 2);
lean_inc_n(v_size_1196_, 2);
lean_dec_ref(v_vars_1191_);
lean_inc_ref_n(v_e_1184_, 2);
v___f_1197_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1197_, 0, v_e_1184_);
lean_closure_set(v___f_1197_, 1, v___f_1182_);
lean_closure_set(v___f_1197_, 2, v___f_1183_);
lean_closure_set(v___f_1197_, 3, v_size_1196_);
v___f_1198_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1198_, 0, v_toPure_1185_);
lean_closure_set(v___f_1198_, 1, v_size_1196_);
lean_inc_n(v_toBind_1187_, 2);
v___f_1199_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1199_, 0, v_e_1184_);
lean_closure_set(v___f_1199_, 1, v_inst_1186_);
lean_closure_set(v___f_1199_, 2, v_toBind_1187_);
lean_closure_set(v___f_1199_, 3, v___f_1198_);
v___f_1200_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1200_, 0, v_inst_1188_);
lean_closure_set(v___f_1200_, 1, v_e_1184_);
lean_closure_set(v___f_1200_, 2, v_toBind_1187_);
lean_closure_set(v___f_1200_, 3, v___f_1199_);
v___x_1201_ = lean_apply_1(v_modifySemiringState_1189_, v___f_1197_);
v___x_1202_ = lean_apply_4(v_toBind_1187_, lean_box(0), lean_box(0), v___x_1201_, v___f_1200_);
return v___x_1202_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(lean_object* v_inst_1205_, lean_object* v_inst_1206_, lean_object* v_inst_1207_, lean_object* v_inst_1208_, lean_object* v_e_1209_){
_start:
{
lean_object* v_toApplicative_1210_; lean_object* v_toBind_1211_; lean_object* v_getSemiringState_1212_; lean_object* v_modifySemiringState_1213_; lean_object* v_toPure_1214_; lean_object* v___f_1215_; lean_object* v___f_1216_; lean_object* v___f_1217_; lean_object* v___x_1218_; 
v_toApplicative_1210_ = lean_ctor_get(v_inst_1206_, 0);
lean_inc_ref(v_toApplicative_1210_);
v_toBind_1211_ = lean_ctor_get(v_inst_1206_, 1);
lean_inc_n(v_toBind_1211_, 2);
lean_dec_ref(v_inst_1206_);
v_getSemiringState_1212_ = lean_ctor_get(v_inst_1207_, 0);
lean_inc(v_getSemiringState_1212_);
v_modifySemiringState_1213_ = lean_ctor_get(v_inst_1207_, 1);
lean_inc(v_modifySemiringState_1213_);
lean_dec_ref(v_inst_1207_);
v_toPure_1214_ = lean_ctor_get(v_toApplicative_1210_, 1);
lean_inc(v_toPure_1214_);
lean_dec_ref(v_toApplicative_1210_);
v___f_1215_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0));
v___f_1216_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1));
v___f_1217_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4), 9, 8);
lean_closure_set(v___f_1217_, 0, v___f_1215_);
lean_closure_set(v___f_1217_, 1, v___f_1216_);
lean_closure_set(v___f_1217_, 2, v_e_1209_);
lean_closure_set(v___f_1217_, 3, v_toPure_1214_);
lean_closure_set(v___f_1217_, 4, v_inst_1205_);
lean_closure_set(v___f_1217_, 5, v_toBind_1211_);
lean_closure_set(v___f_1217_, 6, v_inst_1208_);
lean_closure_set(v___f_1217_, 7, v_modifySemiringState_1213_);
v___x_1218_ = lean_apply_4(v_toBind_1211_, lean_box(0), lean_box(0), v_getSemiringState_1212_, v___f_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore(lean_object* v_m_1219_, lean_object* v_inst_1220_, lean_object* v_inst_1221_, lean_object* v_inst_1222_, lean_object* v_inst_1223_, lean_object* v_e_1224_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(v_inst_1220_, v_inst_1221_, v_inst_1222_, v_inst_1223_, v_e_1224_);
return v___x_1225_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0___closed__0));
v___x_1228_ = l_Lean_stringToMessageData(v___x_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0(lean_object* v___x_1229_, lean_object* v___x_1230_, lean_object* v___f_1231_, lean_object* v___x_1232_, lean_object* v___f_1233_, lean_object* v_e_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_1234_, v___y_1236_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; uint8_t v___x_1249_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_a_1248_);
lean_dec_ref_known(v___x_1247_, 1);
v___x_1249_ = lean_unbox(v_a_1248_);
lean_dec(v_a_1248_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1449__overap_1253_; lean_object* v___x_1254_; 
v___x_1250_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0___closed__1);
lean_inc_ref(v_e_1234_);
v___x_1251_ = l_Lean_indentExpr(v_e_1234_);
v___x_1252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1250_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
lean_inc_ref(v___x_1229_);
v___x_1449__overap_1253_ = l_Lean_throwError___redArg(v___x_1229_, v___x_1230_, v___x_1252_);
lean_inc(v___y_1245_);
lean_inc_ref(v___y_1244_);
lean_inc(v___y_1243_);
lean_inc_ref(v___y_1242_);
lean_inc(v___y_1241_);
lean_inc_ref(v___y_1240_);
lean_inc(v___y_1239_);
lean_inc_ref(v___y_1238_);
lean_inc(v___y_1237_);
lean_inc(v___y_1236_);
lean_inc(v___y_1235_);
v___x_1254_ = lean_apply_12(v___x_1449__overap_1253_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, lean_box(0));
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v___x_1452__overap_1255_; lean_object* v___x_1256_; 
lean_dec_ref_known(v___x_1254_, 1);
v___x_1452__overap_1255_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(v___f_1231_, v___x_1229_, v___x_1232_, v___f_1233_, v_e_1234_);
lean_inc(v___y_1245_);
lean_inc_ref(v___y_1244_);
lean_inc(v___y_1243_);
lean_inc_ref(v___y_1242_);
lean_inc(v___y_1241_);
lean_inc_ref(v___y_1240_);
lean_inc(v___y_1239_);
lean_inc_ref(v___y_1238_);
lean_inc(v___y_1237_);
lean_inc(v___y_1236_);
lean_inc(v___y_1235_);
v___x_1256_ = lean_apply_12(v___x_1452__overap_1255_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, lean_box(0));
return v___x_1256_;
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
lean_dec_ref(v_e_1234_);
lean_dec_ref(v___f_1233_);
lean_dec_ref(v___x_1232_);
lean_dec(v___f_1231_);
lean_dec_ref(v___x_1229_);
v_a_1257_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1254_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1254_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
else
{
lean_object* v___x_1456__overap_1265_; lean_object* v___x_1266_; 
lean_dec_ref(v___x_1230_);
v___x_1456__overap_1265_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(v___f_1231_, v___x_1229_, v___x_1232_, v___f_1233_, v_e_1234_);
lean_inc(v___y_1245_);
lean_inc_ref(v___y_1244_);
lean_inc(v___y_1243_);
lean_inc_ref(v___y_1242_);
lean_inc(v___y_1241_);
lean_inc_ref(v___y_1240_);
lean_inc(v___y_1239_);
lean_inc_ref(v___y_1238_);
lean_inc(v___y_1237_);
lean_inc(v___y_1236_);
lean_inc(v___y_1235_);
v___x_1266_ = lean_apply_12(v___x_1456__overap_1265_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, lean_box(0));
return v___x_1266_;
}
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_dec_ref(v_e_1234_);
lean_dec_ref(v___f_1233_);
lean_dec_ref(v___x_1232_);
lean_dec(v___f_1231_);
lean_dec_ref(v___x_1230_);
lean_dec_ref(v___x_1229_);
v_a_1267_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1247_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1247_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0___boxed(lean_object** _args){
lean_object* v___x_1275_ = _args[0];
lean_object* v___x_1276_ = _args[1];
lean_object* v___f_1277_ = _args[2];
lean_object* v___x_1278_ = _args[3];
lean_object* v___f_1279_ = _args[4];
lean_object* v_e_1280_ = _args[5];
lean_object* v___y_1281_ = _args[6];
lean_object* v___y_1282_ = _args[7];
lean_object* v___y_1283_ = _args[8];
lean_object* v___y_1284_ = _args[9];
lean_object* v___y_1285_ = _args[10];
lean_object* v___y_1286_ = _args[11];
lean_object* v___y_1287_ = _args[12];
lean_object* v___y_1288_ = _args[13];
lean_object* v___y_1289_ = _args[14];
lean_object* v___y_1290_ = _args[15];
lean_object* v___y_1291_ = _args[16];
lean_object* v___y_1292_ = _args[17];
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0(v___x_1275_, v___x_1276_, v___f_1277_, v___x_1278_, v___f_1279_, v_e_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec(v___y_1281_);
return v_res_1293_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__0(void){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = l_instMonadEIO___redArg();
return v___x_1294_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__1(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__0);
v___x_1296_ = l_StateRefT_x27_instMonad___redArg(v___x_1295_);
return v___x_1296_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__7(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___f_1303_; 
v___x_1302_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_1303_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1303_, 0, v___x_1302_);
return v___f_1303_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__8(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___f_1305_; 
v___x_1304_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_1305_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1305_, 0, v___x_1304_);
return v___f_1305_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__9(void){
_start:
{
lean_object* v___f_1306_; lean_object* v___f_1307_; lean_object* v___x_1308_; 
v___f_1306_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__8, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__8_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__8);
v___f_1307_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__7, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__7_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__7);
v___x_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___f_1307_);
lean_ctor_set(v___x_1308_, 1, v___f_1306_);
return v___x_1308_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__10(void){
_start:
{
lean_object* v___x_1309_; lean_object* v___f_1310_; 
v___x_1309_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__9, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__9_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__9);
v___f_1310_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1310_, 0, v___x_1309_);
return v___f_1310_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__11(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___f_1312_; 
v___x_1311_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__9, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__9_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__9);
v___f_1312_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1312_, 0, v___x_1311_);
return v___f_1312_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__12(void){
_start:
{
lean_object* v___f_1313_; lean_object* v___f_1314_; lean_object* v___x_1315_; 
v___f_1313_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__11, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__11_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__11);
v___f_1314_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__10, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__10_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__10);
v___x_1315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___f_1314_);
lean_ctor_set(v___x_1315_, 1, v___f_1313_);
return v___x_1315_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__13(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___f_1317_; 
v___x_1316_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__12);
v___f_1317_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1317_, 0, v___x_1316_);
return v___f_1317_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__14(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___f_1319_; 
v___x_1318_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__12);
v___f_1319_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1319_, 0, v___x_1318_);
return v___f_1319_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__15(void){
_start:
{
lean_object* v___f_1320_; lean_object* v___f_1321_; lean_object* v___x_1322_; 
v___f_1320_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__14, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__14_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__14);
v___f_1321_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__13, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__13_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__13);
v___x_1322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___f_1321_);
lean_ctor_set(v___x_1322_, 1, v___f_1320_);
return v___x_1322_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__16(void){
_start:
{
lean_object* v___x_1323_; lean_object* v___f_1324_; 
v___x_1323_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__15, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__15_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__15);
v___f_1324_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1324_, 0, v___x_1323_);
return v___f_1324_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__17(void){
_start:
{
lean_object* v___x_1325_; lean_object* v___f_1326_; 
v___x_1325_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__15, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__15_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__15);
v___f_1326_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1326_, 0, v___x_1325_);
return v___f_1326_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__18(void){
_start:
{
lean_object* v___f_1327_; lean_object* v___f_1328_; lean_object* v___x_1329_; 
v___f_1327_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__17, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__17_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__17);
v___f_1328_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__16, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__16_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__16);
v___x_1329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___f_1328_);
lean_ctor_set(v___x_1329_, 1, v___f_1327_);
return v___x_1329_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__19(void){
_start:
{
lean_object* v___x_1330_; lean_object* v___f_1331_; 
v___x_1330_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__18, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__18_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__18);
v___f_1331_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1331_, 0, v___x_1330_);
return v___f_1331_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__20(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___f_1333_; 
v___x_1332_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__18, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__18_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__18);
v___f_1333_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1333_, 0, v___x_1332_);
return v___f_1333_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__21(void){
_start:
{
lean_object* v___f_1334_; lean_object* v___f_1335_; lean_object* v___x_1336_; 
v___f_1334_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__20, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__20_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__20);
v___f_1335_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__19, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__19_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__19);
v___x_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___f_1335_);
lean_ctor_set(v___x_1336_, 1, v___f_1334_);
return v___x_1336_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__22(void){
_start:
{
lean_object* v___x_1337_; lean_object* v___f_1338_; 
v___x_1337_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__21, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__21_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__21);
v___f_1338_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1338_, 0, v___x_1337_);
return v___f_1338_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__23(void){
_start:
{
lean_object* v___x_1339_; lean_object* v___f_1340_; 
v___x_1339_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__21, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__21_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__21);
v___f_1340_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1340_, 0, v___x_1339_);
return v___f_1340_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__24(void){
_start:
{
lean_object* v___f_1341_; lean_object* v___f_1342_; lean_object* v___x_1343_; 
v___f_1341_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__23, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__23_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__23);
v___f_1342_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__22, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__22_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__22);
v___x_1343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1343_, 0, v___f_1342_);
lean_ctor_set(v___x_1343_, 1, v___f_1341_);
return v___x_1343_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__25(void){
_start:
{
lean_object* v___x_1344_; lean_object* v___f_1345_; 
v___x_1344_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__24, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__24_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__24);
v___f_1345_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1345_, 0, v___x_1344_);
return v___f_1345_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__26(void){
_start:
{
lean_object* v___x_1346_; lean_object* v___f_1347_; 
v___x_1346_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__24, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__24_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__24);
v___f_1347_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1347_, 0, v___x_1346_);
return v___f_1347_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__27(void){
_start:
{
lean_object* v___f_1348_; lean_object* v___f_1349_; lean_object* v___x_1350_; 
v___f_1348_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__26, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__26_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__26);
v___f_1349_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__25, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__25_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__25);
v___x_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___f_1349_);
lean_ctor_set(v___x_1350_, 1, v___f_1348_);
return v___x_1350_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__28(void){
_start:
{
lean_object* v___x_1351_; lean_object* v___f_1352_; 
v___x_1351_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__27, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__27_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__27);
v___f_1352_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1352_, 0, v___x_1351_);
return v___f_1352_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__29(void){
_start:
{
lean_object* v___x_1353_; lean_object* v___f_1354_; 
v___x_1353_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__27, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__27_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__27);
v___f_1354_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1354_, 0, v___x_1353_);
return v___f_1354_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__30(void){
_start:
{
lean_object* v___f_1355_; lean_object* v___f_1356_; lean_object* v___x_1357_; 
v___f_1355_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__29, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__29_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__29);
v___f_1356_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__28, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__28_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__28);
v___x_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___f_1356_);
lean_ctor_set(v___x_1357_, 1, v___f_1355_);
return v___x_1357_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__31(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___f_1359_; 
v___x_1358_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__30, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__30_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__30);
v___f_1359_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1359_, 0, v___x_1358_);
return v___f_1359_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__32(void){
_start:
{
lean_object* v___x_1360_; lean_object* v___f_1361_; 
v___x_1360_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__30, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__30_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__30);
v___f_1361_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1361_, 0, v___x_1360_);
return v___f_1361_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__33(void){
_start:
{
lean_object* v___f_1362_; lean_object* v___f_1363_; lean_object* v___x_1364_; 
v___f_1362_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__32, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__32_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__32);
v___f_1363_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__31, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__31_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__31);
v___x_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___f_1363_);
lean_ctor_set(v___x_1364_, 1, v___f_1362_);
return v___x_1364_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__37(void){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1368_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1369_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__36));
v___x_1370_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__35));
v___x_1371_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1370_, v___x_1369_, v___x_1368_);
return v___x_1371_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__38(void){
_start:
{
lean_object* v___x_1372_; lean_object* v___f_1373_; lean_object* v___f_1374_; lean_object* v___x_1375_; 
v___x_1372_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__37, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__37_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__37);
v___f_1373_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6));
v___f_1374_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__34));
v___x_1375_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1374_, v___f_1373_, v___x_1372_);
return v___x_1375_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__39(void){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1376_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__38, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__38_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__38);
v___x_1377_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__36));
v___x_1378_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__35));
v___x_1379_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1378_, v___x_1377_, v___x_1376_);
return v___x_1379_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__40(void){
_start:
{
lean_object* v___x_1380_; lean_object* v___f_1381_; lean_object* v___f_1382_; lean_object* v___x_1383_; 
v___x_1380_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__39, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__39_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__39);
v___f_1381_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6));
v___f_1382_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__34));
v___x_1383_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1382_, v___f_1381_, v___x_1380_);
return v___x_1383_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__41(void){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1384_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__40, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__40_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__40);
v___x_1385_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__36));
v___x_1386_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__35));
v___x_1387_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1386_, v___x_1385_, v___x_1384_);
return v___x_1387_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__42(void){
_start:
{
lean_object* v___x_1388_; lean_object* v___f_1389_; lean_object* v___f_1390_; lean_object* v___x_1391_; 
v___x_1388_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__41, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__41_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__41);
v___f_1389_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6));
v___f_1390_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__34));
v___x_1391_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1390_, v___f_1389_, v___x_1388_);
return v___x_1391_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__43(void){
_start:
{
lean_object* v___x_1392_; lean_object* v___f_1393_; lean_object* v___f_1394_; lean_object* v___x_1395_; 
v___x_1392_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__42, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__42_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__42);
v___f_1393_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6));
v___f_1394_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__34));
v___x_1395_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1394_, v___f_1393_, v___x_1392_);
return v___x_1395_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__44(void){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1396_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__43, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__43_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__43);
v___x_1397_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__36));
v___x_1398_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__35));
v___x_1399_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1398_, v___x_1397_, v___x_1396_);
return v___x_1399_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__45(void){
_start:
{
lean_object* v___x_1400_; lean_object* v___f_1401_; lean_object* v___f_1402_; lean_object* v___x_1403_; 
v___x_1400_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__44, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__44_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__44);
v___f_1401_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6));
v___f_1402_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__34));
v___x_1403_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1402_, v___f_1401_, v___x_1400_);
return v___x_1403_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__48(void){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___f_1410_; 
v___x_1408_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__36));
v___x_1409_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_1410_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1410_, 0, v___x_1409_);
lean_closure_set(v___f_1410_, 1, v___x_1408_);
return v___f_1410_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__49(void){
_start:
{
lean_object* v___f_1411_; lean_object* v___f_1412_; lean_object* v___f_1413_; 
v___f_1411_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6));
v___f_1412_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__48, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__48_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__48);
v___f_1413_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1413_, 0, v___f_1412_);
lean_closure_set(v___f_1413_, 1, v___f_1411_);
return v___f_1413_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__50(void){
_start:
{
lean_object* v___x_1414_; lean_object* v___f_1415_; lean_object* v___f_1416_; 
v___x_1414_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__36));
v___f_1415_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__49, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__49_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__49);
v___f_1416_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1416_, 0, v___f_1415_);
lean_closure_set(v___f_1416_, 1, v___x_1414_);
return v___f_1416_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__51(void){
_start:
{
lean_object* v___f_1417_; lean_object* v___f_1418_; lean_object* v___f_1419_; 
v___f_1417_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6));
v___f_1418_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__50, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__50_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__50);
v___f_1419_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1419_, 0, v___f_1418_);
lean_closure_set(v___f_1419_, 1, v___f_1417_);
return v___f_1419_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__52(void){
_start:
{
lean_object* v___f_1420_; lean_object* v___f_1421_; lean_object* v___f_1422_; 
v___f_1420_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6));
v___f_1421_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__51, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__51_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__51);
v___f_1422_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1422_, 0, v___f_1421_);
lean_closure_set(v___f_1422_, 1, v___f_1420_);
return v___f_1422_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__53(void){
_start:
{
lean_object* v___x_1423_; lean_object* v___f_1424_; lean_object* v___f_1425_; 
v___x_1423_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__36));
v___f_1424_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__52, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__52_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__52);
v___f_1425_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1425_, 0, v___f_1424_);
lean_closure_set(v___f_1425_, 1, v___x_1423_);
return v___f_1425_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__54(void){
_start:
{
lean_object* v___f_1426_; lean_object* v___f_1427_; lean_object* v___f_1428_; 
v___f_1426_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6));
v___f_1427_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__53, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__53_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__53);
v___f_1428_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1428_, 0, v___f_1427_);
lean_closure_set(v___f_1428_, 1, v___f_1426_);
return v___f_1428_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM(void){
_start:
{
lean_object* v___x_1429_; lean_object* v_toApplicative_1430_; lean_object* v_toFunctor_1431_; lean_object* v_toSeq_1432_; lean_object* v_toSeqLeft_1433_; lean_object* v_toSeqRight_1434_; lean_object* v___f_1435_; lean_object* v___f_1436_; lean_object* v___f_1437_; lean_object* v___f_1438_; lean_object* v___x_1439_; lean_object* v___f_1440_; lean_object* v___f_1441_; lean_object* v___f_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v_toApplicative_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1490_; 
v___x_1429_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__1);
v_toApplicative_1430_ = lean_ctor_get(v___x_1429_, 0);
v_toFunctor_1431_ = lean_ctor_get(v_toApplicative_1430_, 0);
v_toSeq_1432_ = lean_ctor_get(v_toApplicative_1430_, 2);
v_toSeqLeft_1433_ = lean_ctor_get(v_toApplicative_1430_, 3);
v_toSeqRight_1434_ = lean_ctor_get(v_toApplicative_1430_, 4);
v___f_1435_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__2));
v___f_1436_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__3));
lean_inc_ref_n(v_toFunctor_1431_, 2);
v___f_1437_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1437_, 0, v_toFunctor_1431_);
v___f_1438_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1438_, 0, v_toFunctor_1431_);
v___x_1439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___f_1437_);
lean_ctor_set(v___x_1439_, 1, v___f_1438_);
lean_inc(v_toSeqRight_1434_);
v___f_1440_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1440_, 0, v_toSeqRight_1434_);
lean_inc(v_toSeqLeft_1433_);
v___f_1441_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1441_, 0, v_toSeqLeft_1433_);
lean_inc(v_toSeq_1432_);
v___f_1442_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1442_, 0, v_toSeq_1432_);
v___x_1443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1439_);
lean_ctor_set(v___x_1443_, 1, v___f_1435_);
lean_ctor_set(v___x_1443_, 2, v___f_1442_);
lean_ctor_set(v___x_1443_, 3, v___f_1441_);
lean_ctor_set(v___x_1443_, 4, v___f_1440_);
v___x_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
lean_ctor_set(v___x_1444_, 1, v___f_1436_);
v___x_1445_ = l_StateRefT_x27_instMonad___redArg(v___x_1444_);
v_toApplicative_1446_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1490_ == 0)
{
lean_object* v_unused_1491_; 
v_unused_1491_ = lean_ctor_get(v___x_1445_, 1);
lean_dec(v_unused_1491_);
v___x_1448_ = v___x_1445_;
v_isShared_1449_ = v_isSharedCheck_1490_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_toApplicative_1446_);
lean_dec(v___x_1445_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1490_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v_toFunctor_1450_; lean_object* v_toSeq_1451_; lean_object* v_toSeqLeft_1452_; lean_object* v_toSeqRight_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1488_; 
v_toFunctor_1450_ = lean_ctor_get(v_toApplicative_1446_, 0);
v_toSeq_1451_ = lean_ctor_get(v_toApplicative_1446_, 2);
v_toSeqLeft_1452_ = lean_ctor_get(v_toApplicative_1446_, 3);
v_toSeqRight_1453_ = lean_ctor_get(v_toApplicative_1446_, 4);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_toApplicative_1446_);
if (v_isSharedCheck_1488_ == 0)
{
lean_object* v_unused_1489_; 
v_unused_1489_ = lean_ctor_get(v_toApplicative_1446_, 1);
lean_dec(v_unused_1489_);
v___x_1455_ = v_toApplicative_1446_;
v_isShared_1456_ = v_isSharedCheck_1488_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_toSeqRight_1453_);
lean_inc(v_toSeqLeft_1452_);
lean_inc(v_toSeq_1451_);
lean_inc(v_toFunctor_1450_);
lean_dec(v_toApplicative_1446_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1488_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___f_1457_; lean_object* v___f_1458_; lean_object* v___f_1459_; lean_object* v___f_1460_; lean_object* v___x_1461_; lean_object* v___f_1462_; lean_object* v___f_1463_; lean_object* v___f_1464_; lean_object* v___x_1466_; 
v___f_1457_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__4));
v___f_1458_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__5));
lean_inc_ref(v_toFunctor_1450_);
v___f_1459_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1459_, 0, v_toFunctor_1450_);
v___f_1460_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1460_, 0, v_toFunctor_1450_);
v___x_1461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___f_1459_);
lean_ctor_set(v___x_1461_, 1, v___f_1460_);
v___f_1462_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1462_, 0, v_toSeqRight_1453_);
v___f_1463_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1463_, 0, v_toSeqLeft_1452_);
v___f_1464_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1464_, 0, v_toSeq_1451_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 4, v___f_1462_);
lean_ctor_set(v___x_1455_, 3, v___f_1463_);
lean_ctor_set(v___x_1455_, 2, v___f_1464_);
lean_ctor_set(v___x_1455_, 1, v___f_1457_);
lean_ctor_set(v___x_1455_, 0, v___x_1461_);
v___x_1466_ = v___x_1455_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1461_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v___f_1457_);
lean_ctor_set(v_reuseFailAlloc_1487_, 2, v___f_1464_);
lean_ctor_set(v_reuseFailAlloc_1487_, 3, v___f_1463_);
lean_ctor_set(v_reuseFailAlloc_1487_, 4, v___f_1462_);
v___x_1466_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
lean_object* v___x_1468_; 
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 1, v___f_1458_);
lean_ctor_set(v___x_1448_, 0, v___x_1466_);
v___x_1468_ = v___x_1448_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1466_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v___f_1458_);
v___x_1468_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v_toMonadRef_1479_; lean_object* v___f_1480_; lean_object* v___f_1481_; lean_object* v___f_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___f_1485_; 
v___x_1469_ = l_StateRefT_x27_instMonad___redArg(v___x_1468_);
v___x_1470_ = l_ReaderT_instMonad___redArg(v___x_1469_);
v___x_1471_ = l_StateRefT_x27_instMonad___redArg(v___x_1470_);
v___x_1472_ = l_ReaderT_instMonad___redArg(v___x_1471_);
v___x_1473_ = l_ReaderT_instMonad___redArg(v___x_1472_);
v___x_1474_ = l_StateRefT_x27_instMonad___redArg(v___x_1473_);
v___x_1475_ = l_ReaderT_instMonad___redArg(v___x_1474_);
v___x_1476_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM;
v___x_1477_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__33, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__33_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__33);
v___x_1478_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__45, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__45_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__45);
v_toMonadRef_1479_ = lean_ctor_get(v___x_1478_, 0);
v___f_1480_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__47));
v___f_1481_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___closed__0));
v___f_1482_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__54, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__54_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__54);
lean_inc_ref(v___x_1475_);
v___x_1483_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1482_, v___x_1475_);
lean_inc_ref(v_toMonadRef_1479_);
v___x_1484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1477_);
lean_ctor_set(v___x_1484_, 1, v_toMonadRef_1479_);
lean_ctor_set(v___x_1484_, 2, v___x_1483_);
v___f_1485_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0___boxed), 18, 5);
lean_closure_set(v___f_1485_, 0, v___x_1475_);
lean_closure_set(v___f_1485_, 1, v___x_1484_);
lean_closure_set(v___f_1485_, 2, v___f_1480_);
lean_closure_set(v___f_1485_, 3, v___x_1476_);
lean_closure_set(v___f_1485_, 4, v___f_1481_);
return v___f_1485_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__1(lean_object* v_a_1492_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_nat_to_int(v_a_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0(lean_object* v___y_1494_, lean_object* v_a_1495_, lean_object* v_s_1496_){
_start:
{
lean_object* v_exp_1497_; lean_object* v_rings_1498_; lean_object* v_semirings_1499_; lean_object* v_ncRings_1500_; lean_object* v_ncSemirings_1501_; lean_object* v_typeClassify_1502_; lean_object* v_orders_1503_; lean_object* v_typeOrderClassify_1504_; lean_object* v___x_1505_; uint8_t v___x_1506_; 
v_exp_1497_ = lean_ctor_get(v_s_1496_, 0);
v_rings_1498_ = lean_ctor_get(v_s_1496_, 1);
v_semirings_1499_ = lean_ctor_get(v_s_1496_, 2);
v_ncRings_1500_ = lean_ctor_get(v_s_1496_, 3);
v_ncSemirings_1501_ = lean_ctor_get(v_s_1496_, 4);
v_typeClassify_1502_ = lean_ctor_get(v_s_1496_, 5);
v_orders_1503_ = lean_ctor_get(v_s_1496_, 6);
v_typeOrderClassify_1504_ = lean_ctor_get(v_s_1496_, 7);
v___x_1505_ = lean_array_get_size(v_semirings_1499_);
v___x_1506_ = lean_nat_dec_lt(v___y_1494_, v___x_1505_);
if (v___x_1506_ == 0)
{
lean_dec_ref(v_a_1495_);
return v_s_1496_;
}
else
{
lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1530_; 
lean_inc_ref(v_typeOrderClassify_1504_);
lean_inc_ref(v_orders_1503_);
lean_inc_ref(v_typeClassify_1502_);
lean_inc_ref(v_ncSemirings_1501_);
lean_inc_ref(v_ncRings_1500_);
lean_inc_ref(v_semirings_1499_);
lean_inc_ref(v_rings_1498_);
lean_inc(v_exp_1497_);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_s_1496_);
if (v_isSharedCheck_1530_ == 0)
{
lean_object* v_unused_1531_; lean_object* v_unused_1532_; lean_object* v_unused_1533_; lean_object* v_unused_1534_; lean_object* v_unused_1535_; lean_object* v_unused_1536_; lean_object* v_unused_1537_; lean_object* v_unused_1538_; 
v_unused_1531_ = lean_ctor_get(v_s_1496_, 7);
lean_dec(v_unused_1531_);
v_unused_1532_ = lean_ctor_get(v_s_1496_, 6);
lean_dec(v_unused_1532_);
v_unused_1533_ = lean_ctor_get(v_s_1496_, 5);
lean_dec(v_unused_1533_);
v_unused_1534_ = lean_ctor_get(v_s_1496_, 4);
lean_dec(v_unused_1534_);
v_unused_1535_ = lean_ctor_get(v_s_1496_, 3);
lean_dec(v_unused_1535_);
v_unused_1536_ = lean_ctor_get(v_s_1496_, 2);
lean_dec(v_unused_1536_);
v_unused_1537_ = lean_ctor_get(v_s_1496_, 1);
lean_dec(v_unused_1537_);
v_unused_1538_ = lean_ctor_get(v_s_1496_, 0);
lean_dec(v_unused_1538_);
v___x_1508_ = v_s_1496_;
v_isShared_1509_ = v_isSharedCheck_1530_;
goto v_resetjp_1507_;
}
else
{
lean_dec(v_s_1496_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1530_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v_v_1510_; lean_object* v_toSemiring_1511_; lean_object* v_ringId_1512_; lean_object* v_commSemiringInst_1513_; lean_object* v_addRightCancelInst_x3f_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1528_; 
v_v_1510_ = lean_array_fget(v_semirings_1499_, v___y_1494_);
v_toSemiring_1511_ = lean_ctor_get(v_v_1510_, 0);
v_ringId_1512_ = lean_ctor_get(v_v_1510_, 1);
v_commSemiringInst_1513_ = lean_ctor_get(v_v_1510_, 2);
v_addRightCancelInst_x3f_1514_ = lean_ctor_get(v_v_1510_, 3);
v_isSharedCheck_1528_ = !lean_is_exclusive(v_v_1510_);
if (v_isSharedCheck_1528_ == 0)
{
lean_object* v_unused_1529_; 
v_unused_1529_ = lean_ctor_get(v_v_1510_, 4);
lean_dec(v_unused_1529_);
v___x_1516_ = v_v_1510_;
v_isShared_1517_ = v_isSharedCheck_1528_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_addRightCancelInst_x3f_1514_);
lean_inc(v_commSemiringInst_1513_);
lean_inc(v_ringId_1512_);
lean_inc(v_toSemiring_1511_);
lean_dec(v_v_1510_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1528_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1518_; lean_object* v_xs_x27_1519_; lean_object* v___x_1520_; lean_object* v___x_1522_; 
v___x_1518_ = lean_box(0);
v_xs_x27_1519_ = lean_array_fset(v_semirings_1499_, v___y_1494_, v___x_1518_);
v___x_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1520_, 0, v_a_1495_);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 4, v___x_1520_);
v___x_1522_ = v___x_1516_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_toSemiring_1511_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_ringId_1512_);
lean_ctor_set(v_reuseFailAlloc_1527_, 2, v_commSemiringInst_1513_);
lean_ctor_set(v_reuseFailAlloc_1527_, 3, v_addRightCancelInst_x3f_1514_);
lean_ctor_set(v_reuseFailAlloc_1527_, 4, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1523_ = lean_array_fset(v_xs_x27_1519_, v___y_1494_, v___x_1522_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 2, v___x_1523_);
v___x_1525_ = v___x_1508_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_exp_1497_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v_rings_1498_);
lean_ctor_set(v_reuseFailAlloc_1526_, 2, v___x_1523_);
lean_ctor_set(v_reuseFailAlloc_1526_, 3, v_ncRings_1500_);
lean_ctor_set(v_reuseFailAlloc_1526_, 4, v_ncSemirings_1501_);
lean_ctor_set(v_reuseFailAlloc_1526_, 5, v_typeClassify_1502_);
lean_ctor_set(v_reuseFailAlloc_1526_, 6, v_orders_1503_);
lean_ctor_set(v_reuseFailAlloc_1526_, 7, v_typeOrderClassify_1504_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0___boxed(lean_object* v___y_1539_, lean_object* v_a_1540_, lean_object* v_s_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0(v___y_1539_, v_a_1540_, v_s_1541_);
lean_dec(v___y_1539_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v___y_1567_; lean_object* v___x_1588_; 
v___x_1588_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1610_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1591_ = v___x_1588_;
v_isShared_1592_ = v_isSharedCheck_1610_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1588_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1610_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v_toQFn_x3f_1593_; 
v_toQFn_x3f_1593_ = lean_ctor_get(v_a_1589_, 4);
if (lean_obj_tag(v_toQFn_x3f_1593_) == 1)
{
lean_object* v_val_1594_; lean_object* v___x_1596_; 
lean_inc_ref(v_toQFn_x3f_1593_);
lean_dec(v_a_1589_);
v_val_1594_ = lean_ctor_get(v_toQFn_x3f_1593_, 0);
lean_inc(v_val_1594_);
lean_dec_ref_known(v_toQFn_x3f_1593_, 1);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v_val_1594_);
v___x_1596_ = v___x_1591_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_val_1594_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
else
{
lean_object* v_toSemiring_1598_; lean_object* v_type_1599_; lean_object* v_u_1600_; lean_object* v_semiringInst_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
lean_del_object(v___x_1591_);
v_toSemiring_1598_ = lean_ctor_get(v_a_1589_, 0);
lean_inc_ref(v_toSemiring_1598_);
lean_dec(v_a_1589_);
v_type_1599_ = lean_ctor_get(v_toSemiring_1598_, 1);
lean_inc_ref(v_type_1599_);
v_u_1600_ = lean_ctor_get(v_toSemiring_1598_, 2);
lean_inc(v_u_1600_);
v_semiringInst_1601_ = lean_ctor_get(v_toSemiring_1598_, 3);
lean_inc_ref(v_semiringInst_1601_);
lean_dec_ref(v_toSemiring_1598_);
v___x_1602_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__5));
v___x_1603_ = lean_box(0);
v___x_1604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1604_, 0, v_u_1600_);
lean_ctor_set(v___x_1604_, 1, v___x_1603_);
v___x_1605_ = l_Lean_mkConst(v___x_1602_, v___x_1604_);
v___x_1606_ = l_Lean_mkAppB(v___x_1605_, v_type_1599_, v_semiringInst_1601_);
v___x_1607_ = l_Lean_Meta_Sym_canon(v___x_1606_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; lean_object* v___x_1609_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1608_);
lean_dec_ref_known(v___x_1607_, 1);
v___x_1609_ = l_Lean_Meta_Sym_shareCommon(v_a_1608_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
v___y_1567_ = v___x_1609_;
goto v___jp_1566_;
}
else
{
v___y_1567_ = v___x_1607_;
goto v___jp_1566_;
}
}
}
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
v_a_1611_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1588_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1588_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
v___jp_1566_:
{
if (lean_obj_tag(v___y_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___f_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v_a_1568_ = lean_ctor_get(v___y_1567_, 0);
lean_inc_n(v_a_1568_, 2);
lean_dec_ref_known(v___y_1567_, 1);
lean_inc(v___y_1554_);
v___f_1569_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1569_, 0, v___y_1554_);
lean_closure_set(v___f_1569_, 1, v_a_1568_);
v___x_1570_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_1571_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_1570_, v___f_1569_, v___y_1560_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1578_ == 0)
{
lean_object* v_unused_1579_; 
v_unused_1579_ = lean_ctor_get(v___x_1571_, 0);
lean_dec(v_unused_1579_);
v___x_1573_ = v___x_1571_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_dec(v___x_1571_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v_a_1568_);
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1568_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec(v_a_1568_);
v_a_1580_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1571_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1571_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
else
{
return v___y_1567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___boxed(lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec(v___y_1619_);
return v_res_1631_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6___closed__0(void){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6(lean_object* v_msg_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v___x_1646_; lean_object* v___f_1647_; lean_object* v___x_39303__overap_1648_; lean_object* v___x_1649_; 
v___x_1646_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6___closed__0);
v___f_1647_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1647_, 0, v___x_1646_);
v___x_39303__overap_1648_ = lean_panic_fn_borrowed(v___f_1647_, v_msg_1633_);
lean_dec_ref(v___f_1647_);
lean_inc(v___y_1644_);
lean_inc_ref(v___y_1643_);
lean_inc(v___y_1642_);
lean_inc_ref(v___y_1641_);
lean_inc(v___y_1640_);
lean_inc_ref(v___y_1639_);
lean_inc(v___y_1638_);
lean_inc_ref(v___y_1637_);
lean_inc(v___y_1636_);
lean_inc(v___y_1635_);
lean_inc(v___y_1634_);
v___x_1649_ = lean_apply_12(v___x_39303__overap_1648_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, lean_box(0));
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6___boxed(lean_object* v_msg_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6(v_msg_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec(v___y_1651_);
return v_res_1663_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1665_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg___closed__0));
v___x_1666_ = l_Lean_stringToMessageData(v___x_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg(lean_object* v_type_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v___x_1674_; 
lean_inc_ref(v_type_1667_);
v___x_1674_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1687_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1677_ = v___x_1674_;
v_isShared_1678_ = v_isSharedCheck_1687_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1674_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1687_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
if (lean_obj_tag(v_a_1675_) == 1)
{
lean_object* v_val_1679_; lean_object* v___x_1681_; 
lean_dec_ref(v_type_1667_);
v_val_1679_ = lean_ctor_get(v_a_1675_, 0);
lean_inc(v_val_1679_);
lean_dec_ref_known(v_a_1675_, 1);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v_val_1679_);
v___x_1681_ = v___x_1677_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_val_1679_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
else
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
lean_del_object(v___x_1677_);
lean_dec(v_a_1675_);
v___x_1683_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg___closed__1, &l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg___closed__1_once, _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg___closed__1);
v___x_1684_ = l_Lean_indentExpr(v_type_1667_);
v___x_1685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1683_);
lean_ctor_set(v___x_1685_, 1, v___x_1684_);
v___x_1686_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v___x_1685_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
return v___x_1686_;
}
}
}
else
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
lean_dec_ref(v_type_1667_);
v_a_1688_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_1674_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1674_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_type_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg(v_type_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__4(lean_object* v_type_1704_, lean_object* v_u_1705_, lean_object* v_instDeclName_1706_, lean_object* v_declName_1707_, lean_object* v_expectedInst_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1721_ = lean_box(0);
v___x_1722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1722_, 0, v_u_1705_);
lean_ctor_set(v___x_1722_, 1, v___x_1721_);
lean_inc_ref(v___x_1722_);
v___x_1723_ = l_Lean_mkConst(v_instDeclName_1706_, v___x_1722_);
lean_inc_ref(v_type_1704_);
v___x_1724_ = l_Lean_Expr_app___override(v___x_1723_, v_type_1704_);
v___x_1725_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg(v___x_1724_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1727_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc_n(v_a_1726_, 2);
lean_dec_ref_known(v___x_1725_, 1);
lean_inc(v_declName_1707_);
v___x_1727_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v_declName_1707_, v_a_1726_, v_expectedInst_1708_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
lean_dec_ref_known(v___x_1727_, 1);
v___x_1728_ = l_Lean_mkConst(v_declName_1707_, v___x_1722_);
v___x_1729_ = l_Lean_mkAppB(v___x_1728_, v_type_1704_, v_a_1726_);
v___x_1730_ = l_Lean_Meta_Sym_canon(v___x_1729_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_a_1731_; lean_object* v___x_1732_; 
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_a_1731_);
lean_dec_ref_known(v___x_1730_, 1);
v___x_1732_ = l_Lean_Meta_Sym_shareCommon(v_a_1731_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
return v___x_1732_;
}
else
{
return v___x_1730_;
}
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_dec(v_a_1726_);
lean_dec_ref_known(v___x_1722_, 2);
lean_dec(v_declName_1707_);
lean_dec_ref(v_type_1704_);
v_a_1733_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1727_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1727_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
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
else
{
lean_dec_ref_known(v___x_1722_, 2);
lean_dec_ref(v_expectedInst_1708_);
lean_dec(v_declName_1707_);
lean_dec_ref(v_type_1704_);
return v___x_1725_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__4___boxed(lean_object** _args){
lean_object* v_type_1741_ = _args[0];
lean_object* v_u_1742_ = _args[1];
lean_object* v_instDeclName_1743_ = _args[2];
lean_object* v_declName_1744_ = _args[3];
lean_object* v_expectedInst_1745_ = _args[4];
lean_object* v___y_1746_ = _args[5];
lean_object* v___y_1747_ = _args[6];
lean_object* v___y_1748_ = _args[7];
lean_object* v___y_1749_ = _args[8];
lean_object* v___y_1750_ = _args[9];
lean_object* v___y_1751_ = _args[10];
lean_object* v___y_1752_ = _args[11];
lean_object* v___y_1753_ = _args[12];
lean_object* v___y_1754_ = _args[13];
lean_object* v___y_1755_ = _args[14];
lean_object* v___y_1756_ = _args[15];
lean_object* v___y_1757_ = _args[16];
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__4(v_type_1741_, v_u_1742_, v_instDeclName_1743_, v_declName_1744_, v_expectedInst_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec(v___y_1747_);
lean_dec(v___y_1746_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___lam__0(lean_object* v_a_1759_, lean_object* v_s_1760_){
_start:
{
lean_object* v_toRing_1761_; lean_object* v_invFn_x3f_1762_; lean_object* v_divFn_x3f_1763_; lean_object* v_semiringId_x3f_1764_; lean_object* v_commSemiringInst_1765_; lean_object* v_commRingInst_1766_; lean_object* v_noZeroDivInst_x3f_1767_; lean_object* v_fieldInst_x3f_1768_; lean_object* v_powIdentityInst_x3f_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1800_; 
v_toRing_1761_ = lean_ctor_get(v_s_1760_, 0);
v_invFn_x3f_1762_ = lean_ctor_get(v_s_1760_, 1);
v_divFn_x3f_1763_ = lean_ctor_get(v_s_1760_, 2);
v_semiringId_x3f_1764_ = lean_ctor_get(v_s_1760_, 3);
v_commSemiringInst_1765_ = lean_ctor_get(v_s_1760_, 4);
v_commRingInst_1766_ = lean_ctor_get(v_s_1760_, 5);
v_noZeroDivInst_x3f_1767_ = lean_ctor_get(v_s_1760_, 6);
v_fieldInst_x3f_1768_ = lean_ctor_get(v_s_1760_, 7);
v_powIdentityInst_x3f_1769_ = lean_ctor_get(v_s_1760_, 8);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_s_1760_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1771_ = v_s_1760_;
v_isShared_1772_ = v_isSharedCheck_1800_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_powIdentityInst_x3f_1769_);
lean_inc(v_fieldInst_x3f_1768_);
lean_inc(v_noZeroDivInst_x3f_1767_);
lean_inc(v_commRingInst_1766_);
lean_inc(v_commSemiringInst_1765_);
lean_inc(v_semiringId_x3f_1764_);
lean_inc(v_divFn_x3f_1763_);
lean_inc(v_invFn_x3f_1762_);
lean_inc(v_toRing_1761_);
lean_dec(v_s_1760_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1800_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v_id_1773_; lean_object* v_type_1774_; lean_object* v_u_1775_; lean_object* v_ringInst_1776_; lean_object* v_semiringInst_1777_; lean_object* v_charInst_x3f_1778_; lean_object* v_addFn_x3f_1779_; lean_object* v_mulFn_x3f_1780_; lean_object* v_subFn_x3f_1781_; lean_object* v_powFn_x3f_1782_; lean_object* v_intCastFn_x3f_1783_; lean_object* v_natCastFn_x3f_1784_; lean_object* v_natSMulFn_x3f_1785_; lean_object* v_intSMulFn_x3f_1786_; lean_object* v_one_x3f_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1798_; 
v_id_1773_ = lean_ctor_get(v_toRing_1761_, 0);
v_type_1774_ = lean_ctor_get(v_toRing_1761_, 1);
v_u_1775_ = lean_ctor_get(v_toRing_1761_, 2);
v_ringInst_1776_ = lean_ctor_get(v_toRing_1761_, 3);
v_semiringInst_1777_ = lean_ctor_get(v_toRing_1761_, 4);
v_charInst_x3f_1778_ = lean_ctor_get(v_toRing_1761_, 5);
v_addFn_x3f_1779_ = lean_ctor_get(v_toRing_1761_, 6);
v_mulFn_x3f_1780_ = lean_ctor_get(v_toRing_1761_, 7);
v_subFn_x3f_1781_ = lean_ctor_get(v_toRing_1761_, 8);
v_powFn_x3f_1782_ = lean_ctor_get(v_toRing_1761_, 10);
v_intCastFn_x3f_1783_ = lean_ctor_get(v_toRing_1761_, 11);
v_natCastFn_x3f_1784_ = lean_ctor_get(v_toRing_1761_, 12);
v_natSMulFn_x3f_1785_ = lean_ctor_get(v_toRing_1761_, 13);
v_intSMulFn_x3f_1786_ = lean_ctor_get(v_toRing_1761_, 14);
v_one_x3f_1787_ = lean_ctor_get(v_toRing_1761_, 15);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_toRing_1761_);
if (v_isSharedCheck_1798_ == 0)
{
lean_object* v_unused_1799_; 
v_unused_1799_ = lean_ctor_get(v_toRing_1761_, 9);
lean_dec(v_unused_1799_);
v___x_1789_ = v_toRing_1761_;
v_isShared_1790_ = v_isSharedCheck_1798_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_one_x3f_1787_);
lean_inc(v_intSMulFn_x3f_1786_);
lean_inc(v_natSMulFn_x3f_1785_);
lean_inc(v_natCastFn_x3f_1784_);
lean_inc(v_intCastFn_x3f_1783_);
lean_inc(v_powFn_x3f_1782_);
lean_inc(v_subFn_x3f_1781_);
lean_inc(v_mulFn_x3f_1780_);
lean_inc(v_addFn_x3f_1779_);
lean_inc(v_charInst_x3f_1778_);
lean_inc(v_semiringInst_1777_);
lean_inc(v_ringInst_1776_);
lean_inc(v_u_1775_);
lean_inc(v_type_1774_);
lean_inc(v_id_1773_);
lean_dec(v_toRing_1761_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1798_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1791_; lean_object* v___x_1793_; 
v___x_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1791_, 0, v_a_1759_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 9, v___x_1791_);
v___x_1793_ = v___x_1789_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_id_1773_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v_type_1774_);
lean_ctor_set(v_reuseFailAlloc_1797_, 2, v_u_1775_);
lean_ctor_set(v_reuseFailAlloc_1797_, 3, v_ringInst_1776_);
lean_ctor_set(v_reuseFailAlloc_1797_, 4, v_semiringInst_1777_);
lean_ctor_set(v_reuseFailAlloc_1797_, 5, v_charInst_x3f_1778_);
lean_ctor_set(v_reuseFailAlloc_1797_, 6, v_addFn_x3f_1779_);
lean_ctor_set(v_reuseFailAlloc_1797_, 7, v_mulFn_x3f_1780_);
lean_ctor_set(v_reuseFailAlloc_1797_, 8, v_subFn_x3f_1781_);
lean_ctor_set(v_reuseFailAlloc_1797_, 9, v___x_1791_);
lean_ctor_set(v_reuseFailAlloc_1797_, 10, v_powFn_x3f_1782_);
lean_ctor_set(v_reuseFailAlloc_1797_, 11, v_intCastFn_x3f_1783_);
lean_ctor_set(v_reuseFailAlloc_1797_, 12, v_natCastFn_x3f_1784_);
lean_ctor_set(v_reuseFailAlloc_1797_, 13, v_natSMulFn_x3f_1785_);
lean_ctor_set(v_reuseFailAlloc_1797_, 14, v_intSMulFn_x3f_1786_);
lean_ctor_set(v_reuseFailAlloc_1797_, 15, v_one_x3f_1787_);
v___x_1793_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
lean_object* v___x_1795_; 
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v___x_1793_);
v___x_1795_ = v___x_1771_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1793_);
lean_ctor_set(v_reuseFailAlloc_1796_, 1, v_invFn_x3f_1762_);
lean_ctor_set(v_reuseFailAlloc_1796_, 2, v_divFn_x3f_1763_);
lean_ctor_set(v_reuseFailAlloc_1796_, 3, v_semiringId_x3f_1764_);
lean_ctor_set(v_reuseFailAlloc_1796_, 4, v_commSemiringInst_1765_);
lean_ctor_set(v_reuseFailAlloc_1796_, 5, v_commRingInst_1766_);
lean_ctor_set(v_reuseFailAlloc_1796_, 6, v_noZeroDivInst_x3f_1767_);
lean_ctor_set(v_reuseFailAlloc_1796_, 7, v_fieldInst_x3f_1768_);
lean_ctor_set(v_reuseFailAlloc_1796_, 8, v_powIdentityInst_x3f_1769_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1867_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1829_ = v___x_1826_;
v_isShared_1830_ = v_isSharedCheck_1867_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1826_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1867_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v_toRing_1831_; lean_object* v_negFn_x3f_1832_; 
v_toRing_1831_ = lean_ctor_get(v_a_1827_, 0);
lean_inc_ref(v_toRing_1831_);
lean_dec(v_a_1827_);
v_negFn_x3f_1832_ = lean_ctor_get(v_toRing_1831_, 9);
if (lean_obj_tag(v_negFn_x3f_1832_) == 1)
{
lean_object* v_val_1833_; lean_object* v___x_1835_; 
lean_inc_ref(v_negFn_x3f_1832_);
lean_dec_ref(v_toRing_1831_);
v_val_1833_ = lean_ctor_get(v_negFn_x3f_1832_, 0);
lean_inc(v_val_1833_);
lean_dec_ref_known(v_negFn_x3f_1832_, 1);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v_val_1833_);
v___x_1835_ = v___x_1829_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_val_1833_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
else
{
lean_object* v_type_1837_; lean_object* v_u_1838_; lean_object* v_ringInst_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v_expectedInst_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
lean_del_object(v___x_1829_);
v_type_1837_ = lean_ctor_get(v_toRing_1831_, 1);
lean_inc_ref_n(v_type_1837_, 2);
v_u_1838_ = lean_ctor_get(v_toRing_1831_, 2);
lean_inc_n(v_u_1838_, 2);
v_ringInst_1839_ = lean_ctor_get(v_toRing_1831_, 3);
lean_inc_ref(v_ringInst_1839_);
lean_dec_ref(v_toRing_1831_);
v___x_1840_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1));
v___x_1841_ = lean_box(0);
v___x_1842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1842_, 0, v_u_1838_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
v___x_1843_ = l_Lean_mkConst(v___x_1840_, v___x_1842_);
v_expectedInst_1844_ = l_Lean_mkAppB(v___x_1843_, v_type_1837_, v_ringInst_1839_);
v___x_1845_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__3));
v___x_1846_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5));
v___x_1847_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__4(v_type_1837_, v_u_1838_, v___x_1845_, v___x_1846_, v_expectedInst_1844_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___f_1849_; lean_object* v___x_1850_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc_n(v_a_1848_, 2);
lean_dec_ref_known(v___x_1847_, 1);
v___f_1849_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_1849_, 0, v_a_1848_);
v___x_1850_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_1849_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1857_ == 0)
{
lean_object* v_unused_1858_; 
v_unused_1858_ = lean_ctor_get(v___x_1850_, 0);
lean_dec(v_unused_1858_);
v___x_1852_ = v___x_1850_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_dec(v___x_1850_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 0, v_a_1848_);
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1848_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_dec(v_a_1848_);
v_a_1859_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1850_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1850_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
else
{
return v___x_1847_;
}
}
}
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
v_a_1868_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1826_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1826_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___boxed(lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec(v___y_1876_);
return v_res_1888_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = lean_unsigned_to_nat(0u);
v___x_1897_ = lean_nat_to_int(v___x_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(lean_object* v_k_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1978_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1920_ = v___x_1917_;
v_isShared_1921_ = v_isSharedCheck_1978_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1917_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1978_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v_toRing_1922_; lean_object* v_type_1923_; lean_object* v_u_1924_; lean_object* v_semiringInst_1925_; lean_object* v___x_1926_; lean_object* v_n_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v_ofNatInst_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v_toRing_1922_ = lean_ctor_get(v_a_1918_, 0);
lean_inc_ref(v_toRing_1922_);
lean_dec(v_a_1918_);
v_type_1923_ = lean_ctor_get(v_toRing_1922_, 1);
lean_inc_ref_n(v_type_1923_, 2);
v_u_1924_ = lean_ctor_get(v_toRing_1922_, 2);
lean_inc(v_u_1924_);
v_semiringInst_1925_ = lean_ctor_get(v_toRing_1922_, 4);
lean_inc_ref(v_semiringInst_1925_);
lean_dec_ref(v_toRing_1922_);
v___x_1926_ = lean_nat_abs(v_k_1904_);
v_n_1927_ = l_Lean_mkRawNatLit(v___x_1926_);
v___x_1928_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__1));
v___x_1929_ = lean_box(0);
v___x_1930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1930_, 0, v_u_1924_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
lean_inc_ref(v___x_1930_);
v___x_1962_ = l_Lean_mkConst(v___x_1928_, v___x_1930_);
lean_inc_ref(v_n_1927_);
v___x_1963_ = l_Lean_mkAppB(v___x_1962_, v_type_1923_, v_n_1927_);
v___x_1964_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1963_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_a_1965_);
lean_dec_ref_known(v___x_1964_, 1);
if (lean_obj_tag(v_a_1965_) == 1)
{
lean_object* v_val_1966_; 
lean_dec_ref(v_semiringInst_1925_);
v_val_1966_ = lean_ctor_get(v_a_1965_, 0);
lean_inc(v_val_1966_);
lean_dec_ref_known(v_a_1965_, 1);
v_ofNatInst_1932_ = v_val_1966_;
v___y_1933_ = v___y_1905_;
v___y_1934_ = v___y_1906_;
v___y_1935_ = v___y_1907_;
v___y_1936_ = v___y_1908_;
v___y_1937_ = v___y_1909_;
v___y_1938_ = v___y_1910_;
v___y_1939_ = v___y_1911_;
v___y_1940_ = v___y_1912_;
v___y_1941_ = v___y_1913_;
v___y_1942_ = v___y_1914_;
v___y_1943_ = v___y_1915_;
goto v___jp_1931_;
}
else
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
lean_dec(v_a_1965_);
v___x_1967_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__6));
lean_inc_ref(v___x_1930_);
v___x_1968_ = l_Lean_mkConst(v___x_1967_, v___x_1930_);
lean_inc_ref(v_n_1927_);
lean_inc_ref(v_type_1923_);
v___x_1969_ = l_Lean_mkApp3(v___x_1968_, v_type_1923_, v_semiringInst_1925_, v_n_1927_);
v_ofNatInst_1932_ = v___x_1969_;
v___y_1933_ = v___y_1905_;
v___y_1934_ = v___y_1906_;
v___y_1935_ = v___y_1907_;
v___y_1936_ = v___y_1908_;
v___y_1937_ = v___y_1909_;
v___y_1938_ = v___y_1910_;
v___y_1939_ = v___y_1911_;
v___y_1940_ = v___y_1912_;
v___y_1941_ = v___y_1913_;
v___y_1942_ = v___y_1914_;
v___y_1943_ = v___y_1915_;
goto v___jp_1931_;
}
}
else
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
lean_dec_ref_known(v___x_1930_, 2);
lean_dec_ref(v_n_1927_);
lean_dec_ref(v_semiringInst_1925_);
lean_dec_ref(v_type_1923_);
lean_del_object(v___x_1920_);
v_a_1970_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1964_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1964_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
v___jp_1931_:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v_e_1946_; lean_object* v___x_1947_; uint8_t v___x_1948_; 
v___x_1944_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3));
v___x_1945_ = l_Lean_mkConst(v___x_1944_, v___x_1930_);
v_e_1946_ = l_Lean_mkApp3(v___x_1945_, v_type_1923_, v_n_1927_, v_ofNatInst_1932_);
v___x_1947_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4, &l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4_once, _init_l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4);
v___x_1948_ = lean_int_dec_lt(v_k_1904_, v___x_1947_);
if (v___x_1948_ == 0)
{
lean_object* v___x_1950_; 
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v_e_1946_);
v___x_1950_ = v___x_1920_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_e_1946_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
else
{
lean_object* v___x_1952_; 
lean_del_object(v___x_1920_);
v___x_1952_ = l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1961_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1955_ = v___x_1952_;
v_isShared_1956_ = v_isSharedCheck_1961_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1952_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1961_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1957_; lean_object* v___x_1959_; 
v___x_1957_ = l_Lean_Expr_app___override(v_a_1953_, v_e_1946_);
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 0, v___x_1957_);
v___x_1959_ = v___x_1955_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1957_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
else
{
lean_dec_ref(v_e_1946_);
return v___x_1952_;
}
}
}
}
}
else
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1986_; 
v_a_1979_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1981_ = v___x_1917_;
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1917_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1979_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___boxed(lean_object* v_k_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v_k_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec(v_k_1987_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___lam__0(lean_object* v_a_2001_, lean_object* v_s_2002_){
_start:
{
lean_object* v_toRing_2003_; lean_object* v_invFn_x3f_2004_; lean_object* v_divFn_x3f_2005_; lean_object* v_semiringId_x3f_2006_; lean_object* v_commSemiringInst_2007_; lean_object* v_commRingInst_2008_; lean_object* v_noZeroDivInst_x3f_2009_; lean_object* v_fieldInst_x3f_2010_; lean_object* v_powIdentityInst_x3f_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2042_; 
v_toRing_2003_ = lean_ctor_get(v_s_2002_, 0);
v_invFn_x3f_2004_ = lean_ctor_get(v_s_2002_, 1);
v_divFn_x3f_2005_ = lean_ctor_get(v_s_2002_, 2);
v_semiringId_x3f_2006_ = lean_ctor_get(v_s_2002_, 3);
v_commSemiringInst_2007_ = lean_ctor_get(v_s_2002_, 4);
v_commRingInst_2008_ = lean_ctor_get(v_s_2002_, 5);
v_noZeroDivInst_x3f_2009_ = lean_ctor_get(v_s_2002_, 6);
v_fieldInst_x3f_2010_ = lean_ctor_get(v_s_2002_, 7);
v_powIdentityInst_x3f_2011_ = lean_ctor_get(v_s_2002_, 8);
v_isSharedCheck_2042_ = !lean_is_exclusive(v_s_2002_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2013_ = v_s_2002_;
v_isShared_2014_ = v_isSharedCheck_2042_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_powIdentityInst_x3f_2011_);
lean_inc(v_fieldInst_x3f_2010_);
lean_inc(v_noZeroDivInst_x3f_2009_);
lean_inc(v_commRingInst_2008_);
lean_inc(v_commSemiringInst_2007_);
lean_inc(v_semiringId_x3f_2006_);
lean_inc(v_divFn_x3f_2005_);
lean_inc(v_invFn_x3f_2004_);
lean_inc(v_toRing_2003_);
lean_dec(v_s_2002_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2042_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v_id_2015_; lean_object* v_type_2016_; lean_object* v_u_2017_; lean_object* v_ringInst_2018_; lean_object* v_semiringInst_2019_; lean_object* v_charInst_x3f_2020_; lean_object* v_addFn_x3f_2021_; lean_object* v_mulFn_x3f_2022_; lean_object* v_subFn_x3f_2023_; lean_object* v_negFn_x3f_2024_; lean_object* v_intCastFn_x3f_2025_; lean_object* v_natCastFn_x3f_2026_; lean_object* v_natSMulFn_x3f_2027_; lean_object* v_intSMulFn_x3f_2028_; lean_object* v_one_x3f_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2040_; 
v_id_2015_ = lean_ctor_get(v_toRing_2003_, 0);
v_type_2016_ = lean_ctor_get(v_toRing_2003_, 1);
v_u_2017_ = lean_ctor_get(v_toRing_2003_, 2);
v_ringInst_2018_ = lean_ctor_get(v_toRing_2003_, 3);
v_semiringInst_2019_ = lean_ctor_get(v_toRing_2003_, 4);
v_charInst_x3f_2020_ = lean_ctor_get(v_toRing_2003_, 5);
v_addFn_x3f_2021_ = lean_ctor_get(v_toRing_2003_, 6);
v_mulFn_x3f_2022_ = lean_ctor_get(v_toRing_2003_, 7);
v_subFn_x3f_2023_ = lean_ctor_get(v_toRing_2003_, 8);
v_negFn_x3f_2024_ = lean_ctor_get(v_toRing_2003_, 9);
v_intCastFn_x3f_2025_ = lean_ctor_get(v_toRing_2003_, 11);
v_natCastFn_x3f_2026_ = lean_ctor_get(v_toRing_2003_, 12);
v_natSMulFn_x3f_2027_ = lean_ctor_get(v_toRing_2003_, 13);
v_intSMulFn_x3f_2028_ = lean_ctor_get(v_toRing_2003_, 14);
v_one_x3f_2029_ = lean_ctor_get(v_toRing_2003_, 15);
v_isSharedCheck_2040_ = !lean_is_exclusive(v_toRing_2003_);
if (v_isSharedCheck_2040_ == 0)
{
lean_object* v_unused_2041_; 
v_unused_2041_ = lean_ctor_get(v_toRing_2003_, 10);
lean_dec(v_unused_2041_);
v___x_2031_ = v_toRing_2003_;
v_isShared_2032_ = v_isSharedCheck_2040_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_one_x3f_2029_);
lean_inc(v_intSMulFn_x3f_2028_);
lean_inc(v_natSMulFn_x3f_2027_);
lean_inc(v_natCastFn_x3f_2026_);
lean_inc(v_intCastFn_x3f_2025_);
lean_inc(v_negFn_x3f_2024_);
lean_inc(v_subFn_x3f_2023_);
lean_inc(v_mulFn_x3f_2022_);
lean_inc(v_addFn_x3f_2021_);
lean_inc(v_charInst_x3f_2020_);
lean_inc(v_semiringInst_2019_);
lean_inc(v_ringInst_2018_);
lean_inc(v_u_2017_);
lean_inc(v_type_2016_);
lean_inc(v_id_2015_);
lean_dec(v_toRing_2003_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2040_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2033_; lean_object* v___x_2035_; 
v___x_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2033_, 0, v_a_2001_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 10, v___x_2033_);
v___x_2035_ = v___x_2031_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_id_2015_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v_type_2016_);
lean_ctor_set(v_reuseFailAlloc_2039_, 2, v_u_2017_);
lean_ctor_set(v_reuseFailAlloc_2039_, 3, v_ringInst_2018_);
lean_ctor_set(v_reuseFailAlloc_2039_, 4, v_semiringInst_2019_);
lean_ctor_set(v_reuseFailAlloc_2039_, 5, v_charInst_x3f_2020_);
lean_ctor_set(v_reuseFailAlloc_2039_, 6, v_addFn_x3f_2021_);
lean_ctor_set(v_reuseFailAlloc_2039_, 7, v_mulFn_x3f_2022_);
lean_ctor_set(v_reuseFailAlloc_2039_, 8, v_subFn_x3f_2023_);
lean_ctor_set(v_reuseFailAlloc_2039_, 9, v_negFn_x3f_2024_);
lean_ctor_set(v_reuseFailAlloc_2039_, 10, v___x_2033_);
lean_ctor_set(v_reuseFailAlloc_2039_, 11, v_intCastFn_x3f_2025_);
lean_ctor_set(v_reuseFailAlloc_2039_, 12, v_natCastFn_x3f_2026_);
lean_ctor_set(v_reuseFailAlloc_2039_, 13, v_natSMulFn_x3f_2027_);
lean_ctor_set(v_reuseFailAlloc_2039_, 14, v_intSMulFn_x3f_2028_);
lean_ctor_set(v_reuseFailAlloc_2039_, 15, v_one_x3f_2029_);
v___x_2035_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
lean_object* v___x_2037_; 
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 0, v___x_2035_);
v___x_2037_ = v___x_2013_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2038_, 1, v_invFn_x3f_2004_);
lean_ctor_set(v_reuseFailAlloc_2038_, 2, v_divFn_x3f_2005_);
lean_ctor_set(v_reuseFailAlloc_2038_, 3, v_semiringId_x3f_2006_);
lean_ctor_set(v_reuseFailAlloc_2038_, 4, v_commSemiringInst_2007_);
lean_ctor_set(v_reuseFailAlloc_2038_, 5, v_commRingInst_2008_);
lean_ctor_set(v_reuseFailAlloc_2038_, 6, v_noZeroDivInst_x3f_2009_);
lean_ctor_set(v_reuseFailAlloc_2038_, 7, v_fieldInst_x3f_2010_);
lean_ctor_set(v_reuseFailAlloc_2038_, 8, v_powIdentityInst_x3f_2011_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__2(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = lean_unsigned_to_nat(0u);
v___x_2047_ = l_Lean_Level_ofNat(v___x_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7(lean_object* v_u_2058_, lean_object* v_type_2059_, lean_object* v_semiringInst_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2073_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__1));
v___x_2074_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__2, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__2);
v___x_2075_ = lean_box(0);
lean_inc(v_u_2058_);
v___x_2076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2076_, 0, v_u_2058_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
lean_inc_ref(v___x_2076_);
v___x_2077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2074_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
v___x_2078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2078_, 0, v_u_2058_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
lean_inc_ref(v___x_2078_);
v___x_2079_ = l_Lean_mkConst(v___x_2073_, v___x_2078_);
v___x_2080_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2059_, 2);
v___x_2081_ = l_Lean_mkApp3(v___x_2079_, v_type_2059_, v___x_2080_, v_type_2059_);
v___x_2082_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg(v___x_2081_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v_inst_x27_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc_n(v_a_2083_, 2);
lean_dec_ref_known(v___x_2082_, 1);
v___x_2084_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__4));
v___x_2085_ = l_Lean_mkConst(v___x_2084_, v___x_2076_);
lean_inc_ref(v_type_2059_);
v_inst_x27_2086_ = l_Lean_mkAppB(v___x_2085_, v_type_2059_, v_semiringInst_2060_);
v___x_2087_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__6));
v___x_2088_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v___x_2087_, v_a_2083_, v_inst_x27_2086_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
lean_dec_ref_known(v___x_2088_, 1);
v___x_2089_ = l_Lean_mkConst(v___x_2087_, v___x_2078_);
lean_inc_ref(v_type_2059_);
v___x_2090_ = l_Lean_mkApp4(v___x_2089_, v_type_2059_, v___x_2080_, v_type_2059_, v_a_2083_);
v___x_2091_ = l_Lean_Meta_Sym_canon(v___x_2090_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2093_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
lean_dec_ref_known(v___x_2091_, 1);
v___x_2093_ = l_Lean_Meta_Sym_shareCommon(v_a_2092_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
return v___x_2093_;
}
else
{
return v___x_2091_;
}
}
else
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2101_; 
lean_dec(v_a_2083_);
lean_dec_ref_known(v___x_2078_, 2);
lean_dec_ref(v_type_2059_);
v_a_2094_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2096_ = v___x_2088_;
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2088_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2097_ == 0)
{
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2078_, 2);
lean_dec_ref_known(v___x_2076_, 2);
lean_dec_ref(v_semiringInst_2060_);
lean_dec_ref(v_type_2059_);
return v___x_2082_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___boxed(lean_object* v_u_2102_, lean_object* v_type_2103_, lean_object* v_semiringInst_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7(v_u_2102_, v_type_2103_, v_semiringInst_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec(v___y_2105_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v___x_2130_; 
v___x_2130_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2164_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2133_ = v___x_2130_;
v_isShared_2134_ = v_isSharedCheck_2164_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2130_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2164_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v_toRing_2135_; lean_object* v_powFn_x3f_2136_; 
v_toRing_2135_ = lean_ctor_get(v_a_2131_, 0);
lean_inc_ref(v_toRing_2135_);
lean_dec(v_a_2131_);
v_powFn_x3f_2136_ = lean_ctor_get(v_toRing_2135_, 10);
if (lean_obj_tag(v_powFn_x3f_2136_) == 1)
{
lean_object* v_val_2137_; lean_object* v___x_2139_; 
lean_inc_ref(v_powFn_x3f_2136_);
lean_dec_ref(v_toRing_2135_);
v_val_2137_ = lean_ctor_get(v_powFn_x3f_2136_, 0);
lean_inc(v_val_2137_);
lean_dec_ref_known(v_powFn_x3f_2136_, 1);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 0, v_val_2137_);
v___x_2139_ = v___x_2133_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_val_2137_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
else
{
lean_object* v_type_2141_; lean_object* v_u_2142_; lean_object* v_semiringInst_2143_; lean_object* v___x_2144_; 
lean_del_object(v___x_2133_);
v_type_2141_ = lean_ctor_get(v_toRing_2135_, 1);
lean_inc_ref(v_type_2141_);
v_u_2142_ = lean_ctor_get(v_toRing_2135_, 2);
lean_inc(v_u_2142_);
v_semiringInst_2143_ = lean_ctor_get(v_toRing_2135_, 4);
lean_inc_ref(v_semiringInst_2143_);
lean_dec_ref(v_toRing_2135_);
v___x_2144_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7(v_u_2142_, v_type_2141_, v_semiringInst_2143_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___f_2146_; lean_object* v___x_2147_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc_n(v_a_2145_, 2);
lean_dec_ref_known(v___x_2144_, 1);
v___f_2146_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___lam__0), 2, 1);
lean_closure_set(v___f_2146_, 0, v_a_2145_);
v___x_2147_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2146_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2154_ == 0)
{
lean_object* v_unused_2155_; 
v_unused_2155_ = lean_ctor_get(v___x_2147_, 0);
lean_dec(v_unused_2155_);
v___x_2149_ = v___x_2147_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_dec(v___x_2147_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 0, v_a_2145_);
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2145_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_dec(v_a_2145_);
v_a_2156_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2147_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2147_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
else
{
return v___x_2144_;
}
}
}
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
v_a_2165_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2130_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2130_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___boxed(lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec(v___y_2173_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4(lean_object* v_type_2186_, lean_object* v_u_2187_, lean_object* v_instDeclName_2188_, lean_object* v_declName_2189_, lean_object* v_expectedInst_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2203_ = lean_box(0);
lean_inc_n(v_u_2187_, 2);
v___x_2204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2204_, 0, v_u_2187_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
v___x_2205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2205_, 0, v_u_2187_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
v___x_2206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2206_, 0, v_u_2187_);
lean_ctor_set(v___x_2206_, 1, v___x_2205_);
lean_inc_ref(v___x_2206_);
v___x_2207_ = l_Lean_mkConst(v_instDeclName_2188_, v___x_2206_);
lean_inc_ref_n(v_type_2186_, 3);
v___x_2208_ = l_Lean_mkApp3(v___x_2207_, v_type_2186_, v_type_2186_, v_type_2186_);
v___x_2209_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg(v___x_2208_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; lean_object* v___x_2211_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc_n(v_a_2210_, 2);
lean_dec_ref_known(v___x_2209_, 1);
lean_inc(v_declName_2189_);
v___x_2211_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v_declName_2189_, v_a_2210_, v_expectedInst_2190_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
lean_dec_ref_known(v___x_2211_, 1);
v___x_2212_ = l_Lean_mkConst(v_declName_2189_, v___x_2206_);
lean_inc_ref_n(v_type_2186_, 2);
v___x_2213_ = l_Lean_mkApp4(v___x_2212_, v_type_2186_, v_type_2186_, v_type_2186_, v_a_2210_);
v___x_2214_ = l_Lean_Meta_Sym_canon(v___x_2213_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2215_; lean_object* v___x_2216_; 
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2215_);
lean_dec_ref_known(v___x_2214_, 1);
v___x_2216_ = l_Lean_Meta_Sym_shareCommon(v_a_2215_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
return v___x_2216_;
}
else
{
return v___x_2214_;
}
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec(v_a_2210_);
lean_dec_ref_known(v___x_2206_, 2);
lean_dec(v_declName_2189_);
lean_dec_ref(v_type_2186_);
v_a_2217_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2211_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2211_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2206_, 2);
lean_dec_ref(v_expectedInst_2190_);
lean_dec(v_declName_2189_);
lean_dec_ref(v_type_2186_);
return v___x_2209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4___boxed(lean_object** _args){
lean_object* v_type_2225_ = _args[0];
lean_object* v_u_2226_ = _args[1];
lean_object* v_instDeclName_2227_ = _args[2];
lean_object* v_declName_2228_ = _args[3];
lean_object* v_expectedInst_2229_ = _args[4];
lean_object* v___y_2230_ = _args[5];
lean_object* v___y_2231_ = _args[6];
lean_object* v___y_2232_ = _args[7];
lean_object* v___y_2233_ = _args[8];
lean_object* v___y_2234_ = _args[9];
lean_object* v___y_2235_ = _args[10];
lean_object* v___y_2236_ = _args[11];
lean_object* v___y_2237_ = _args[12];
lean_object* v___y_2238_ = _args[13];
lean_object* v___y_2239_ = _args[14];
lean_object* v___y_2240_ = _args[15];
lean_object* v___y_2241_ = _args[16];
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4(v_type_2225_, v_u_2226_, v_instDeclName_2227_, v_declName_2228_, v_expectedInst_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec(v___y_2230_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0(lean_object* v_a_2243_, lean_object* v_s_2244_){
_start:
{
lean_object* v_toRing_2245_; lean_object* v_invFn_x3f_2246_; lean_object* v_divFn_x3f_2247_; lean_object* v_semiringId_x3f_2248_; lean_object* v_commSemiringInst_2249_; lean_object* v_commRingInst_2250_; lean_object* v_noZeroDivInst_x3f_2251_; lean_object* v_fieldInst_x3f_2252_; lean_object* v_powIdentityInst_x3f_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2284_; 
v_toRing_2245_ = lean_ctor_get(v_s_2244_, 0);
v_invFn_x3f_2246_ = lean_ctor_get(v_s_2244_, 1);
v_divFn_x3f_2247_ = lean_ctor_get(v_s_2244_, 2);
v_semiringId_x3f_2248_ = lean_ctor_get(v_s_2244_, 3);
v_commSemiringInst_2249_ = lean_ctor_get(v_s_2244_, 4);
v_commRingInst_2250_ = lean_ctor_get(v_s_2244_, 5);
v_noZeroDivInst_x3f_2251_ = lean_ctor_get(v_s_2244_, 6);
v_fieldInst_x3f_2252_ = lean_ctor_get(v_s_2244_, 7);
v_powIdentityInst_x3f_2253_ = lean_ctor_get(v_s_2244_, 8);
v_isSharedCheck_2284_ = !lean_is_exclusive(v_s_2244_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2255_ = v_s_2244_;
v_isShared_2256_ = v_isSharedCheck_2284_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_powIdentityInst_x3f_2253_);
lean_inc(v_fieldInst_x3f_2252_);
lean_inc(v_noZeroDivInst_x3f_2251_);
lean_inc(v_commRingInst_2250_);
lean_inc(v_commSemiringInst_2249_);
lean_inc(v_semiringId_x3f_2248_);
lean_inc(v_divFn_x3f_2247_);
lean_inc(v_invFn_x3f_2246_);
lean_inc(v_toRing_2245_);
lean_dec(v_s_2244_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2284_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v_id_2257_; lean_object* v_type_2258_; lean_object* v_u_2259_; lean_object* v_ringInst_2260_; lean_object* v_semiringInst_2261_; lean_object* v_charInst_x3f_2262_; lean_object* v_mulFn_x3f_2263_; lean_object* v_subFn_x3f_2264_; lean_object* v_negFn_x3f_2265_; lean_object* v_powFn_x3f_2266_; lean_object* v_intCastFn_x3f_2267_; lean_object* v_natCastFn_x3f_2268_; lean_object* v_natSMulFn_x3f_2269_; lean_object* v_intSMulFn_x3f_2270_; lean_object* v_one_x3f_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2282_; 
v_id_2257_ = lean_ctor_get(v_toRing_2245_, 0);
v_type_2258_ = lean_ctor_get(v_toRing_2245_, 1);
v_u_2259_ = lean_ctor_get(v_toRing_2245_, 2);
v_ringInst_2260_ = lean_ctor_get(v_toRing_2245_, 3);
v_semiringInst_2261_ = lean_ctor_get(v_toRing_2245_, 4);
v_charInst_x3f_2262_ = lean_ctor_get(v_toRing_2245_, 5);
v_mulFn_x3f_2263_ = lean_ctor_get(v_toRing_2245_, 7);
v_subFn_x3f_2264_ = lean_ctor_get(v_toRing_2245_, 8);
v_negFn_x3f_2265_ = lean_ctor_get(v_toRing_2245_, 9);
v_powFn_x3f_2266_ = lean_ctor_get(v_toRing_2245_, 10);
v_intCastFn_x3f_2267_ = lean_ctor_get(v_toRing_2245_, 11);
v_natCastFn_x3f_2268_ = lean_ctor_get(v_toRing_2245_, 12);
v_natSMulFn_x3f_2269_ = lean_ctor_get(v_toRing_2245_, 13);
v_intSMulFn_x3f_2270_ = lean_ctor_get(v_toRing_2245_, 14);
v_one_x3f_2271_ = lean_ctor_get(v_toRing_2245_, 15);
v_isSharedCheck_2282_ = !lean_is_exclusive(v_toRing_2245_);
if (v_isSharedCheck_2282_ == 0)
{
lean_object* v_unused_2283_; 
v_unused_2283_ = lean_ctor_get(v_toRing_2245_, 6);
lean_dec(v_unused_2283_);
v___x_2273_ = v_toRing_2245_;
v_isShared_2274_ = v_isSharedCheck_2282_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_one_x3f_2271_);
lean_inc(v_intSMulFn_x3f_2270_);
lean_inc(v_natSMulFn_x3f_2269_);
lean_inc(v_natCastFn_x3f_2268_);
lean_inc(v_intCastFn_x3f_2267_);
lean_inc(v_powFn_x3f_2266_);
lean_inc(v_negFn_x3f_2265_);
lean_inc(v_subFn_x3f_2264_);
lean_inc(v_mulFn_x3f_2263_);
lean_inc(v_charInst_x3f_2262_);
lean_inc(v_semiringInst_2261_);
lean_inc(v_ringInst_2260_);
lean_inc(v_u_2259_);
lean_inc(v_type_2258_);
lean_inc(v_id_2257_);
lean_dec(v_toRing_2245_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2282_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2275_; lean_object* v___x_2277_; 
v___x_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2275_, 0, v_a_2243_);
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 6, v___x_2275_);
v___x_2277_ = v___x_2273_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_id_2257_);
lean_ctor_set(v_reuseFailAlloc_2281_, 1, v_type_2258_);
lean_ctor_set(v_reuseFailAlloc_2281_, 2, v_u_2259_);
lean_ctor_set(v_reuseFailAlloc_2281_, 3, v_ringInst_2260_);
lean_ctor_set(v_reuseFailAlloc_2281_, 4, v_semiringInst_2261_);
lean_ctor_set(v_reuseFailAlloc_2281_, 5, v_charInst_x3f_2262_);
lean_ctor_set(v_reuseFailAlloc_2281_, 6, v___x_2275_);
lean_ctor_set(v_reuseFailAlloc_2281_, 7, v_mulFn_x3f_2263_);
lean_ctor_set(v_reuseFailAlloc_2281_, 8, v_subFn_x3f_2264_);
lean_ctor_set(v_reuseFailAlloc_2281_, 9, v_negFn_x3f_2265_);
lean_ctor_set(v_reuseFailAlloc_2281_, 10, v_powFn_x3f_2266_);
lean_ctor_set(v_reuseFailAlloc_2281_, 11, v_intCastFn_x3f_2267_);
lean_ctor_set(v_reuseFailAlloc_2281_, 12, v_natCastFn_x3f_2268_);
lean_ctor_set(v_reuseFailAlloc_2281_, 13, v_natSMulFn_x3f_2269_);
lean_ctor_set(v_reuseFailAlloc_2281_, 14, v_intSMulFn_x3f_2270_);
lean_ctor_set(v_reuseFailAlloc_2281_, 15, v_one_x3f_2271_);
v___x_2277_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
lean_object* v___x_2279_; 
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 0, v___x_2277_);
v___x_2279_ = v___x_2255_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2277_);
lean_ctor_set(v_reuseFailAlloc_2280_, 1, v_invFn_x3f_2246_);
lean_ctor_set(v_reuseFailAlloc_2280_, 2, v_divFn_x3f_2247_);
lean_ctor_set(v_reuseFailAlloc_2280_, 3, v_semiringId_x3f_2248_);
lean_ctor_set(v_reuseFailAlloc_2280_, 4, v_commSemiringInst_2249_);
lean_ctor_set(v_reuseFailAlloc_2280_, 5, v_commRingInst_2250_);
lean_ctor_set(v_reuseFailAlloc_2280_, 6, v_noZeroDivInst_x3f_2251_);
lean_ctor_set(v_reuseFailAlloc_2280_, 7, v_fieldInst_x3f_2252_);
lean_ctor_set(v_reuseFailAlloc_2280_, 8, v_powIdentityInst_x3f_2253_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2357_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2316_ = v___x_2313_;
v_isShared_2317_ = v_isSharedCheck_2357_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2313_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2357_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v_toRing_2318_; lean_object* v_addFn_x3f_2319_; 
v_toRing_2318_ = lean_ctor_get(v_a_2314_, 0);
lean_inc_ref(v_toRing_2318_);
lean_dec(v_a_2314_);
v_addFn_x3f_2319_ = lean_ctor_get(v_toRing_2318_, 6);
if (lean_obj_tag(v_addFn_x3f_2319_) == 1)
{
lean_object* v_val_2320_; lean_object* v___x_2322_; 
lean_inc_ref(v_addFn_x3f_2319_);
lean_dec_ref(v_toRing_2318_);
v_val_2320_ = lean_ctor_get(v_addFn_x3f_2319_, 0);
lean_inc(v_val_2320_);
lean_dec_ref_known(v_addFn_x3f_2319_, 1);
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 0, v_val_2320_);
v___x_2322_ = v___x_2316_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_val_2320_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
else
{
lean_object* v_type_2324_; lean_object* v_u_2325_; lean_object* v_semiringInst_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v_expectedInst_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
lean_del_object(v___x_2316_);
v_type_2324_ = lean_ctor_get(v_toRing_2318_, 1);
lean_inc_ref_n(v_type_2324_, 3);
v_u_2325_ = lean_ctor_get(v_toRing_2318_, 2);
lean_inc_n(v_u_2325_, 2);
v_semiringInst_2326_ = lean_ctor_get(v_toRing_2318_, 4);
lean_inc_ref(v_semiringInst_2326_);
lean_dec_ref(v_toRing_2318_);
v___x_2327_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__1));
v___x_2328_ = lean_box(0);
v___x_2329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2329_, 0, v_u_2325_);
lean_ctor_set(v___x_2329_, 1, v___x_2328_);
lean_inc_ref(v___x_2329_);
v___x_2330_ = l_Lean_mkConst(v___x_2327_, v___x_2329_);
v___x_2331_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__3));
v___x_2332_ = l_Lean_mkConst(v___x_2331_, v___x_2329_);
v___x_2333_ = l_Lean_mkAppB(v___x_2332_, v_type_2324_, v_semiringInst_2326_);
v_expectedInst_2334_ = l_Lean_mkAppB(v___x_2330_, v_type_2324_, v___x_2333_);
v___x_2335_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__5));
v___x_2336_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__7));
v___x_2337_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4(v_type_2324_, v_u_2325_, v___x_2335_, v___x_2336_, v_expectedInst_2334_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v___f_2339_; lean_object* v___x_2340_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc_n(v_a_2338_, 2);
lean_dec_ref_known(v___x_2337_, 1);
v___f_2339_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_2339_, 0, v_a_2338_);
v___x_2340_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2339_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2347_ == 0)
{
lean_object* v_unused_2348_; 
v_unused_2348_ = lean_ctor_get(v___x_2340_, 0);
lean_dec(v_unused_2348_);
v___x_2342_ = v___x_2340_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_dec(v___x_2340_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 0, v_a_2338_);
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2338_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
else
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
lean_dec(v_a_2338_);
v_a_2349_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2340_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2340_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2349_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
else
{
return v___x_2337_;
}
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
v_a_2358_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2313_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2313_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___boxed(lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec(v___y_2367_);
lean_dec(v___y_2366_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___lam__0(lean_object* v_a_2379_, lean_object* v_s_2380_){
_start:
{
lean_object* v_toRing_2381_; lean_object* v_invFn_x3f_2382_; lean_object* v_divFn_x3f_2383_; lean_object* v_semiringId_x3f_2384_; lean_object* v_commSemiringInst_2385_; lean_object* v_commRingInst_2386_; lean_object* v_noZeroDivInst_x3f_2387_; lean_object* v_fieldInst_x3f_2388_; lean_object* v_powIdentityInst_x3f_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2420_; 
v_toRing_2381_ = lean_ctor_get(v_s_2380_, 0);
v_invFn_x3f_2382_ = lean_ctor_get(v_s_2380_, 1);
v_divFn_x3f_2383_ = lean_ctor_get(v_s_2380_, 2);
v_semiringId_x3f_2384_ = lean_ctor_get(v_s_2380_, 3);
v_commSemiringInst_2385_ = lean_ctor_get(v_s_2380_, 4);
v_commRingInst_2386_ = lean_ctor_get(v_s_2380_, 5);
v_noZeroDivInst_x3f_2387_ = lean_ctor_get(v_s_2380_, 6);
v_fieldInst_x3f_2388_ = lean_ctor_get(v_s_2380_, 7);
v_powIdentityInst_x3f_2389_ = lean_ctor_get(v_s_2380_, 8);
v_isSharedCheck_2420_ = !lean_is_exclusive(v_s_2380_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2391_ = v_s_2380_;
v_isShared_2392_ = v_isSharedCheck_2420_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_powIdentityInst_x3f_2389_);
lean_inc(v_fieldInst_x3f_2388_);
lean_inc(v_noZeroDivInst_x3f_2387_);
lean_inc(v_commRingInst_2386_);
lean_inc(v_commSemiringInst_2385_);
lean_inc(v_semiringId_x3f_2384_);
lean_inc(v_divFn_x3f_2383_);
lean_inc(v_invFn_x3f_2382_);
lean_inc(v_toRing_2381_);
lean_dec(v_s_2380_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2420_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v_id_2393_; lean_object* v_type_2394_; lean_object* v_u_2395_; lean_object* v_ringInst_2396_; lean_object* v_semiringInst_2397_; lean_object* v_charInst_x3f_2398_; lean_object* v_addFn_x3f_2399_; lean_object* v_subFn_x3f_2400_; lean_object* v_negFn_x3f_2401_; lean_object* v_powFn_x3f_2402_; lean_object* v_intCastFn_x3f_2403_; lean_object* v_natCastFn_x3f_2404_; lean_object* v_natSMulFn_x3f_2405_; lean_object* v_intSMulFn_x3f_2406_; lean_object* v_one_x3f_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2418_; 
v_id_2393_ = lean_ctor_get(v_toRing_2381_, 0);
v_type_2394_ = lean_ctor_get(v_toRing_2381_, 1);
v_u_2395_ = lean_ctor_get(v_toRing_2381_, 2);
v_ringInst_2396_ = lean_ctor_get(v_toRing_2381_, 3);
v_semiringInst_2397_ = lean_ctor_get(v_toRing_2381_, 4);
v_charInst_x3f_2398_ = lean_ctor_get(v_toRing_2381_, 5);
v_addFn_x3f_2399_ = lean_ctor_get(v_toRing_2381_, 6);
v_subFn_x3f_2400_ = lean_ctor_get(v_toRing_2381_, 8);
v_negFn_x3f_2401_ = lean_ctor_get(v_toRing_2381_, 9);
v_powFn_x3f_2402_ = lean_ctor_get(v_toRing_2381_, 10);
v_intCastFn_x3f_2403_ = lean_ctor_get(v_toRing_2381_, 11);
v_natCastFn_x3f_2404_ = lean_ctor_get(v_toRing_2381_, 12);
v_natSMulFn_x3f_2405_ = lean_ctor_get(v_toRing_2381_, 13);
v_intSMulFn_x3f_2406_ = lean_ctor_get(v_toRing_2381_, 14);
v_one_x3f_2407_ = lean_ctor_get(v_toRing_2381_, 15);
v_isSharedCheck_2418_ = !lean_is_exclusive(v_toRing_2381_);
if (v_isSharedCheck_2418_ == 0)
{
lean_object* v_unused_2419_; 
v_unused_2419_ = lean_ctor_get(v_toRing_2381_, 7);
lean_dec(v_unused_2419_);
v___x_2409_ = v_toRing_2381_;
v_isShared_2410_ = v_isSharedCheck_2418_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_one_x3f_2407_);
lean_inc(v_intSMulFn_x3f_2406_);
lean_inc(v_natSMulFn_x3f_2405_);
lean_inc(v_natCastFn_x3f_2404_);
lean_inc(v_intCastFn_x3f_2403_);
lean_inc(v_powFn_x3f_2402_);
lean_inc(v_negFn_x3f_2401_);
lean_inc(v_subFn_x3f_2400_);
lean_inc(v_addFn_x3f_2399_);
lean_inc(v_charInst_x3f_2398_);
lean_inc(v_semiringInst_2397_);
lean_inc(v_ringInst_2396_);
lean_inc(v_u_2395_);
lean_inc(v_type_2394_);
lean_inc(v_id_2393_);
lean_dec(v_toRing_2381_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2418_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2411_; lean_object* v___x_2413_; 
v___x_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2411_, 0, v_a_2379_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 7, v___x_2411_);
v___x_2413_ = v___x_2409_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_id_2393_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v_type_2394_);
lean_ctor_set(v_reuseFailAlloc_2417_, 2, v_u_2395_);
lean_ctor_set(v_reuseFailAlloc_2417_, 3, v_ringInst_2396_);
lean_ctor_set(v_reuseFailAlloc_2417_, 4, v_semiringInst_2397_);
lean_ctor_set(v_reuseFailAlloc_2417_, 5, v_charInst_x3f_2398_);
lean_ctor_set(v_reuseFailAlloc_2417_, 6, v_addFn_x3f_2399_);
lean_ctor_set(v_reuseFailAlloc_2417_, 7, v___x_2411_);
lean_ctor_set(v_reuseFailAlloc_2417_, 8, v_subFn_x3f_2400_);
lean_ctor_set(v_reuseFailAlloc_2417_, 9, v_negFn_x3f_2401_);
lean_ctor_set(v_reuseFailAlloc_2417_, 10, v_powFn_x3f_2402_);
lean_ctor_set(v_reuseFailAlloc_2417_, 11, v_intCastFn_x3f_2403_);
lean_ctor_set(v_reuseFailAlloc_2417_, 12, v_natCastFn_x3f_2404_);
lean_ctor_set(v_reuseFailAlloc_2417_, 13, v_natSMulFn_x3f_2405_);
lean_ctor_set(v_reuseFailAlloc_2417_, 14, v_intSMulFn_x3f_2406_);
lean_ctor_set(v_reuseFailAlloc_2417_, 15, v_one_x3f_2407_);
v___x_2413_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
lean_object* v___x_2415_; 
if (v_isShared_2392_ == 0)
{
lean_ctor_set(v___x_2391_, 0, v___x_2413_);
v___x_2415_ = v___x_2391_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2413_);
lean_ctor_set(v_reuseFailAlloc_2416_, 1, v_invFn_x3f_2382_);
lean_ctor_set(v_reuseFailAlloc_2416_, 2, v_divFn_x3f_2383_);
lean_ctor_set(v_reuseFailAlloc_2416_, 3, v_semiringId_x3f_2384_);
lean_ctor_set(v_reuseFailAlloc_2416_, 4, v_commSemiringInst_2385_);
lean_ctor_set(v_reuseFailAlloc_2416_, 5, v_commRingInst_2386_);
lean_ctor_set(v_reuseFailAlloc_2416_, 6, v_noZeroDivInst_x3f_2387_);
lean_ctor_set(v_reuseFailAlloc_2416_, 7, v_fieldInst_x3f_2388_);
lean_ctor_set(v_reuseFailAlloc_2416_, 8, v_powIdentityInst_x3f_2389_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v___x_2449_; 
v___x_2449_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2493_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2452_ = v___x_2449_;
v_isShared_2453_ = v_isSharedCheck_2493_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2449_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2493_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v_toRing_2454_; lean_object* v_mulFn_x3f_2455_; 
v_toRing_2454_ = lean_ctor_get(v_a_2450_, 0);
lean_inc_ref(v_toRing_2454_);
lean_dec(v_a_2450_);
v_mulFn_x3f_2455_ = lean_ctor_get(v_toRing_2454_, 7);
if (lean_obj_tag(v_mulFn_x3f_2455_) == 1)
{
lean_object* v_val_2456_; lean_object* v___x_2458_; 
lean_inc_ref(v_mulFn_x3f_2455_);
lean_dec_ref(v_toRing_2454_);
v_val_2456_ = lean_ctor_get(v_mulFn_x3f_2455_, 0);
lean_inc(v_val_2456_);
lean_dec_ref_known(v_mulFn_x3f_2455_, 1);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 0, v_val_2456_);
v___x_2458_ = v___x_2452_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_val_2456_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
else
{
lean_object* v_type_2460_; lean_object* v_u_2461_; lean_object* v_semiringInst_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v_expectedInst_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
lean_del_object(v___x_2452_);
v_type_2460_ = lean_ctor_get(v_toRing_2454_, 1);
lean_inc_ref_n(v_type_2460_, 3);
v_u_2461_ = lean_ctor_get(v_toRing_2454_, 2);
lean_inc_n(v_u_2461_, 2);
v_semiringInst_2462_ = lean_ctor_get(v_toRing_2454_, 4);
lean_inc_ref(v_semiringInst_2462_);
lean_dec_ref(v_toRing_2454_);
v___x_2463_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__1));
v___x_2464_ = lean_box(0);
v___x_2465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2465_, 0, v_u_2461_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
lean_inc_ref(v___x_2465_);
v___x_2466_ = l_Lean_mkConst(v___x_2463_, v___x_2465_);
v___x_2467_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__3));
v___x_2468_ = l_Lean_mkConst(v___x_2467_, v___x_2465_);
v___x_2469_ = l_Lean_mkAppB(v___x_2468_, v_type_2460_, v_semiringInst_2462_);
v_expectedInst_2470_ = l_Lean_mkAppB(v___x_2466_, v_type_2460_, v___x_2469_);
v___x_2471_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__5));
v___x_2472_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__7));
v___x_2473_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4(v_type_2460_, v_u_2461_, v___x_2471_, v___x_2472_, v_expectedInst_2470_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2474_; lean_object* v___f_2475_; lean_object* v___x_2476_; 
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc_n(v_a_2474_, 2);
lean_dec_ref_known(v___x_2473_, 1);
v___f_2475_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___lam__0), 2, 1);
lean_closure_set(v___f_2475_, 0, v_a_2474_);
v___x_2476_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2475_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2483_ == 0)
{
lean_object* v_unused_2484_; 
v_unused_2484_ = lean_ctor_get(v___x_2476_, 0);
lean_dec(v_unused_2484_);
v___x_2478_ = v___x_2476_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_dec(v___x_2476_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
lean_ctor_set(v___x_2478_, 0, v_a_2474_);
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2474_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
else
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
lean_dec(v_a_2474_);
v_a_2485_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2476_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2476_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
else
{
return v___x_2473_;
}
}
}
}
else
{
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
v_a_2494_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___x_2449_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2449_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2499_; 
if (v_isShared_2497_ == 0)
{
v___x_2499_ = v___x_2496_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___boxed(lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec(v___y_2502_);
return v_res_2514_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3(void){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2518_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__2));
v___x_2519_ = lean_unsigned_to_nat(39u);
v___x_2520_ = lean_unsigned_to_nat(124u);
v___x_2521_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__1));
v___x_2522_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__0));
v___x_2523_ = l_mkPanicMessageWithDecl(v___x_2522_, v___x_2521_, v___x_2520_, v___x_2519_, v___x_2518_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_){
_start:
{
switch(lean_obj_tag(v_a_2524_))
{
case 0:
{
lean_object* v_k_2537_; lean_object* v___x_2538_; 
v_k_2537_ = lean_ctor_get(v_a_2524_, 0);
lean_inc(v_k_2537_);
lean_dec_ref_known(v_a_2524_, 1);
v___x_2538_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v_k_2537_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_);
lean_dec(v_k_2537_);
return v___x_2538_;
}
case 1:
{
lean_object* v_k_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v_k_2539_ = lean_ctor_get(v_a_2524_, 0);
lean_inc(v_k_2539_);
lean_dec_ref_known(v_a_2524_, 1);
v___x_2540_ = lean_nat_to_int(v_k_2539_);
v___x_2541_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v___x_2540_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_);
lean_dec(v___x_2540_);
return v___x_2541_;
}
case 3:
{
lean_object* v_i_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v_i_2542_ = lean_ctor_get(v_a_2524_, 0);
lean_inc(v_i_2542_);
lean_dec_ref_known(v_a_2524_, 1);
v___x_2543_ = l_Lean_instInhabitedExpr;
v___x_2544_ = l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; lean_object* v___x_2546_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_a_2545_);
lean_dec_ref_known(v___x_2544_, 1);
v___x_2546_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState___redArg(v_a_2525_, v_a_2526_, v_a_2534_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2562_; 
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2549_ = v___x_2546_;
v_isShared_2550_ = v_isSharedCheck_2562_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2546_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2562_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___y_2552_; lean_object* v_vars_2557_; lean_object* v_size_2558_; uint8_t v___x_2559_; 
v_vars_2557_ = lean_ctor_get(v_a_2547_, 1);
lean_inc_ref(v_vars_2557_);
lean_dec(v_a_2547_);
v_size_2558_ = lean_ctor_get(v_vars_2557_, 2);
v___x_2559_ = lean_nat_dec_lt(v_i_2542_, v_size_2558_);
if (v___x_2559_ == 0)
{
lean_object* v___x_2560_; 
lean_dec_ref(v_vars_2557_);
lean_dec(v_i_2542_);
v___x_2560_ = l_outOfBounds___redArg(v___x_2543_);
v___y_2552_ = v___x_2560_;
goto v___jp_2551_;
}
else
{
lean_object* v___x_2561_; 
v___x_2561_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2543_, v_vars_2557_, v_i_2542_);
lean_dec(v_i_2542_);
lean_dec_ref(v_vars_2557_);
v___y_2552_ = v___x_2561_;
goto v___jp_2551_;
}
v___jp_2551_:
{
lean_object* v___x_2553_; lean_object* v___x_2555_; 
v___x_2553_ = l_Lean_Expr_app___override(v_a_2545_, v___y_2552_);
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 0, v___x_2553_);
v___x_2555_ = v___x_2549_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2553_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
lean_dec(v_a_2545_);
lean_dec(v_i_2542_);
v_a_2563_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2546_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2546_);
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
else
{
lean_dec(v_i_2542_);
return v___x_2544_;
}
}
case 5:
{
lean_object* v_a_2571_; lean_object* v_b_2572_; lean_object* v___x_2573_; 
v_a_2571_ = lean_ctor_get(v_a_2524_, 0);
lean_inc_ref(v_a_2571_);
v_b_2572_ = lean_ctor_get(v_a_2524_, 1);
lean_inc_ref(v_b_2572_);
lean_dec_ref_known(v_a_2524_, 2);
v___x_2573_ = l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; lean_object* v___x_2575_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_a_2574_);
lean_dec_ref_known(v___x_2573_, 1);
v___x_2575_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2571_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_a_2576_; lean_object* v___x_2577_; 
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
lean_inc(v_a_2576_);
lean_dec_ref_known(v___x_2575_, 1);
v___x_2577_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_b_2572_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2586_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2580_ = v___x_2577_;
v_isShared_2581_ = v_isSharedCheck_2586_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2586_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2582_; lean_object* v___x_2584_; 
v___x_2582_ = l_Lean_mkAppB(v_a_2574_, v_a_2576_, v_a_2578_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v___x_2582_);
v___x_2584_ = v___x_2580_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2582_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
else
{
lean_dec(v_a_2576_);
lean_dec(v_a_2574_);
return v___x_2577_;
}
}
else
{
lean_dec(v_a_2574_);
lean_dec_ref(v_b_2572_);
return v___x_2575_;
}
}
else
{
lean_dec_ref(v_b_2572_);
lean_dec_ref(v_a_2571_);
return v___x_2573_;
}
}
case 7:
{
lean_object* v_a_2587_; lean_object* v_b_2588_; lean_object* v___x_2589_; 
v_a_2587_ = lean_ctor_get(v_a_2524_, 0);
lean_inc_ref(v_a_2587_);
v_b_2588_ = lean_ctor_get(v_a_2524_, 1);
lean_inc_ref(v_b_2588_);
lean_dec_ref_known(v_a_2524_, 2);
v___x_2589_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; lean_object* v___x_2591_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_a_2590_);
lean_dec_ref_known(v___x_2589_, 1);
v___x_2591_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2587_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v___x_2593_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref_known(v___x_2591_, 1);
v___x_2593_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_b_2588_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_);
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
return v___x_2591_;
}
}
else
{
lean_dec_ref(v_b_2588_);
lean_dec_ref(v_a_2587_);
return v___x_2589_;
}
}
case 8:
{
lean_object* v_a_2603_; lean_object* v_k_2604_; lean_object* v___x_2605_; 
v_a_2603_ = lean_ctor_get(v_a_2524_, 0);
lean_inc_ref(v_a_2603_);
v_k_2604_ = lean_ctor_get(v_a_2524_, 1);
lean_inc(v_k_2604_);
lean_dec_ref_known(v_a_2524_, 2);
v___x_2605_ = l_Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; lean_object* v___x_2607_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
lean_inc(v_a_2606_);
lean_dec_ref_known(v___x_2605_, 1);
v___x_2607_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2603_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2617_; 
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2610_ = v___x_2607_;
v_isShared_2611_ = v_isSharedCheck_2617_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2607_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2617_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2615_; 
v___x_2612_ = l_Lean_mkNatLit(v_k_2604_);
v___x_2613_ = l_Lean_mkAppB(v_a_2606_, v_a_2608_, v___x_2612_);
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 0, v___x_2613_);
v___x_2615_ = v___x_2610_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2613_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
else
{
lean_dec(v_a_2606_);
lean_dec(v_k_2604_);
return v___x_2607_;
}
}
else
{
lean_dec(v_k_2604_);
lean_dec_ref(v_a_2603_);
return v___x_2605_;
}
}
default: 
{
lean_object* v___x_2618_; lean_object* v___x_2619_; 
lean_dec_ref(v_a_2524_);
v___x_2618_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3);
v___x_2619_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6(v___x_2618_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_);
return v___x_2619_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___boxed(lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_);
lean_dec(v_a_2631_);
lean_dec_ref(v_a_2630_);
lean_dec(v_a_2629_);
lean_dec_ref(v_a_2628_);
lean_dec(v_a_2627_);
lean_dec_ref(v_a_2626_);
lean_dec(v_a_2625_);
lean_dec_ref(v_a_2624_);
lean_dec(v_a_2623_);
lean_dec(v_a_2622_);
lean_dec(v_a_2621_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7(lean_object* v_type_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v___x_2647_; 
v___x_2647_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg(v_type_2634_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___boxed(lean_object* v_type_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7(v_type_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec(v___y_2649_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(lean_object* v_e_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_){
_start:
{
lean_object* v___x_2675_; 
v___x_2675_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_e_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v___x_2677_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2676_);
lean_dec_ref_known(v___x_2675_, 1);
v___x_2677_ = l_Lean_Meta_Sym_shareCommon(v_a_2676_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_);
return v___x_2677_;
}
else
{
return v___x_2675_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr___boxed(lean_object* v_e_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_){
_start:
{
lean_object* v_res_2691_; 
v_res_2691_ = l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(v_e_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_);
lean_dec(v_a_2689_);
lean_dec_ref(v_a_2688_);
lean_dec(v_a_2687_);
lean_dec_ref(v_a_2686_);
lean_dec(v_a_2685_);
lean_dec_ref(v_a_2684_);
lean_dec(v_a_2683_);
lean_dec_ref(v_a_2682_);
lean_dec(v_a_2681_);
lean_dec(v_a_2680_);
lean_dec(v_a_2679_);
return v_res_2691_;
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
