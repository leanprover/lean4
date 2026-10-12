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
lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___redArg(lean_object* v_semiringId_1_, lean_object* v_x_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
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
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_semiringId_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_a_6_ = stack[5].m_obj;
lean_object* v_a_7_ = stack[6].m_obj;
lean_object* v_a_8_ = stack[7].m_obj;
lean_object* v_a_9_ = stack[8].m_obj;
lean_object* v_a_10_ = stack[9].m_obj;
lean_object* v_a_11_ = stack[10].m_obj;
lean_object* v_a_12_ = stack[11].m_obj;
lean_object* v_res_15_;
v_res_15_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___redArg(v_semiringId_1_, v_x_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
stack->m_obj
 = v_res_15_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___redArg___boxed(lean_object* v_semiringId_16_, lean_object* v_x_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___redArg(v_semiringId_16_, v_x_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_, v_a_27_);
lean_dec(v_a_27_);
lean_dec_ref(v_a_26_);
lean_dec(v_a_25_);
lean_dec_ref(v_a_24_);
lean_dec(v_a_23_);
lean_dec_ref(v_a_22_);
lean_dec(v_a_21_);
lean_dec_ref(v_a_20_);
lean_dec(v_a_19_);
lean_dec(v_a_18_);
return v_res_29_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run(lean_object* v_00_u03b1_30_, lean_object* v_semiringId_31_, lean_object* v_x_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_){
_start:
{
lean_object* v___x_44_; 
lean_inc(v_a_42_);
lean_inc_ref(v_a_41_);
lean_inc(v_a_40_);
lean_inc_ref(v_a_39_);
lean_inc(v_a_38_);
lean_inc_ref(v_a_37_);
lean_inc(v_a_36_);
lean_inc_ref(v_a_35_);
lean_inc(v_a_34_);
lean_inc(v_a_33_);
v___x_44_ = lean_apply_12(v_x_32_, v_semiringId_31_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, lean_box(0));
return v___x_44_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_semiringId_31_ = stack[1].m_obj;
lean_object* v_x_32_ = stack[2].m_obj;
lean_object* v_a_33_ = stack[3].m_obj;
lean_object* v_a_34_ = stack[4].m_obj;
lean_object* v_a_35_ = stack[5].m_obj;
lean_object* v_a_36_ = stack[6].m_obj;
lean_object* v_a_37_ = stack[7].m_obj;
lean_object* v_a_38_ = stack[8].m_obj;
lean_object* v_a_39_ = stack[9].m_obj;
lean_object* v_a_40_ = stack[10].m_obj;
lean_object* v_a_41_ = stack[11].m_obj;
lean_object* v_a_42_ = stack[12].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run(lean_box(0), v_semiringId_31_, v_x_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___boxed(lean_object* v_00_u03b1_46_, lean_object* v_semiringId_47_, lean_object* v_x_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run(v_00_u03b1_46_, v_semiringId_47_, v_x_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_);
lean_dec(v_a_58_);
lean_dec_ref(v_a_57_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
lean_dec(v_a_54_);
lean_dec_ref(v_a_53_);
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
lean_dec(v_a_49_);
return v_res_60_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___redArg(lean_object* v_a_61_){
_start:
{
lean_object* v___x_63_; 
lean_inc(v_a_61_);
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v_a_61_);
return v___x_63_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_61_ = stack[0].m_obj;
lean_object* v_res_64_;
v_res_64_ = l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___redArg(v_a_61_);
stack->m_obj
 = v_res_64_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___redArg___boxed(lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___redArg(v_a_65_);
lean_dec(v_a_65_);
return v_res_67_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiringId(lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
lean_object* v___x_80_; 
lean_inc(v_a_68_);
v___x_80_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_80_, 0, v_a_68_);
return v___x_80_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_getSemiringId_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_68_ = stack[0].m_obj;
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
v_res_81_ = l_Lean_Meta_Grind_Arith_CommRing_getSemiringId(v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___boxed(lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_Meta_Grind_Arith_CommRing_getSemiringId(v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_);
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
lean_dec(v_a_82_);
return v_res_94_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0(lean_object* v_e_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_Meta_Sym_canon(v_e_95_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v_a_109_; lean_object* v___x_110_; 
v_a_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc(v_a_109_);
lean_dec_ref_known(v___x_108_, 1);
v___x_110_ = l_Lean_Meta_Sym_shareCommon(v_a_109_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
return v___x_110_;
}
else
{
return v___x_108_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_95_ = stack[0].m_obj;
lean_object* v___y_96_ = stack[1].m_obj;
lean_object* v___y_97_ = stack[2].m_obj;
lean_object* v___y_98_ = stack[3].m_obj;
lean_object* v___y_99_ = stack[4].m_obj;
lean_object* v___y_100_ = stack[5].m_obj;
lean_object* v___y_101_ = stack[6].m_obj;
lean_object* v___y_102_ = stack[7].m_obj;
lean_object* v___y_103_ = stack[8].m_obj;
lean_object* v___y_104_ = stack[9].m_obj;
lean_object* v___y_105_ = stack[10].m_obj;
lean_object* v___y_106_ = stack[11].m_obj;
lean_object* v_res_111_;
v_res_111_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0(v_e_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
stack->m_obj
 = v_res_111_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0___boxed(lean_object* v_e_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0(v_e_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
lean_dec(v___y_114_);
lean_dec(v___y_113_);
return v_res_125_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1(lean_object* v_e_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_e_126_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
return v___x_139_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_126_ = stack[0].m_obj;
lean_object* v___y_127_ = stack[1].m_obj;
lean_object* v___y_128_ = stack[2].m_obj;
lean_object* v___y_129_ = stack[3].m_obj;
lean_object* v___y_130_ = stack[4].m_obj;
lean_object* v___y_131_ = stack[5].m_obj;
lean_object* v___y_132_ = stack[6].m_obj;
lean_object* v___y_133_ = stack[7].m_obj;
lean_object* v___y_134_ = stack[8].m_obj;
lean_object* v___y_135_ = stack[9].m_obj;
lean_object* v___y_136_ = stack[10].m_obj;
lean_object* v___y_137_ = stack[11].m_obj;
lean_object* v_res_140_;
v_res_140_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1(v_e_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
stack->m_obj
 = v_res_140_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1___boxed(lean_object* v_e_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1(v_e_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec(v___y_143_);
lean_dec(v___y_142_);
return v_res_154_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0(lean_object* v_msgData_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v___x_167_; lean_object* v_env_168_; uint8_t v___x_169_; lean_object* v_env_170_; lean_object* v___x_171_; lean_object* v_toCold_172_; lean_object* v_mctx_173_; lean_object* v_lctx_174_; lean_object* v_options_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_167_ = lean_st_ref_get(v___y_165_);
v_env_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc_ref(v_env_168_);
lean_dec(v___x_167_);
v___x_169_ = 0;
v_env_170_ = l_Lean_Environment_setRecordingDeps(v_env_168_, v___x_169_);
v___x_171_ = lean_st_ref_get(v___y_163_);
v_toCold_172_ = lean_ctor_get(v___y_164_, 0);
v_mctx_173_ = lean_ctor_get(v___x_171_, 0);
lean_inc_ref(v_mctx_173_);
lean_dec(v___x_171_);
v_lctx_174_ = lean_ctor_get(v___y_162_, 2);
v_options_175_ = lean_ctor_get(v_toCold_172_, 2);
lean_inc_ref(v_options_175_);
lean_inc_ref(v_lctx_174_);
v___x_176_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_176_, 0, v_env_170_);
lean_ctor_set(v___x_176_, 1, v_mctx_173_);
lean_ctor_set(v___x_176_, 2, v_lctx_174_);
lean_ctor_set(v___x_176_, 3, v_options_175_);
v___x_177_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v_msgData_161_);
v___x_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
return v___x_178_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_161_ = stack[0].m_obj;
lean_object* v___y_162_ = stack[1].m_obj;
lean_object* v___y_163_ = stack[2].m_obj;
lean_object* v___y_164_ = stack[3].m_obj;
lean_object* v___y_165_ = stack[4].m_obj;
lean_object* v_res_179_;
v_res_179_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0(v_msgData_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
stack->m_obj
 = v_res_179_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0___boxed(lean_object* v_msgData_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0(v_msgData_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
return v_res_186_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(lean_object* v_msg_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_ref_193_; lean_object* v___x_194_; lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_203_; 
v_ref_193_ = lean_ctor_get(v___y_190_, 2);
v___x_194_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0(v_msg_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
v_a_195_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_203_ == 0)
{
v___x_197_ = v___x_194_;
v_isShared_198_ = v_isSharedCheck_203_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_194_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_203_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; lean_object* v___x_201_; 
lean_inc(v_ref_193_);
v___x_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_199_, 0, v_ref_193_);
lean_ctor_set(v___x_199_, 1, v_a_195_);
if (v_isShared_198_ == 0)
{
lean_ctor_set_tag(v___x_197_, 1);
lean_ctor_set(v___x_197_, 0, v___x_199_);
v___x_201_ = v___x_197_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_199_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_187_ = stack[0].m_obj;
lean_object* v___y_188_ = stack[1].m_obj;
lean_object* v___y_189_ = stack[2].m_obj;
lean_object* v___y_190_ = stack[3].m_obj;
lean_object* v___y_191_ = stack[4].m_obj;
lean_object* v_res_204_;
v_res_204_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v_msg_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
stack->m_obj
 = v_res_204_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg___boxed(lean_object* v_msg_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v_msg_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
return v_res_211_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__0));
v___x_214_ = l_Lean_stringToMessageData(v___x_213_);
return v___x_214_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_221_, v_a_224_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_241_; 
v_a_228_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_241_ == 0)
{
v___x_230_ = v___x_227_;
v_isShared_231_ = v_isSharedCheck_241_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_227_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_241_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v_semirings_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v_semirings_232_ = lean_ctor_get(v_a_228_, 2);
lean_inc_ref(v_semirings_232_);
lean_dec(v_a_228_);
v___x_233_ = lean_array_get_size(v_semirings_232_);
v___x_234_ = lean_nat_dec_lt(v_a_215_, v___x_233_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; lean_object* v___x_236_; 
lean_dec_ref(v_semirings_232_);
lean_del_object(v___x_230_);
v___x_235_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1);
v___x_236_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v___x_235_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
return v___x_236_;
}
else
{
lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_237_ = lean_array_fget(v_semirings_232_, v_a_215_);
lean_dec_ref(v_semirings_232_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 0, v___x_237_);
v___x_239_ = v___x_230_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_237_);
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
else
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
v_a_242_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v___x_227_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_227_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_a_242_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_215_ = stack[0].m_obj;
lean_object* v_a_216_ = stack[1].m_obj;
lean_object* v_a_217_ = stack[2].m_obj;
lean_object* v_a_218_ = stack[3].m_obj;
lean_object* v_a_219_ = stack[4].m_obj;
lean_object* v_a_220_ = stack[5].m_obj;
lean_object* v_a_221_ = stack[6].m_obj;
lean_object* v_a_222_ = stack[7].m_obj;
lean_object* v_a_223_ = stack[8].m_obj;
lean_object* v_a_224_ = stack[9].m_obj;
lean_object* v_a_225_ = stack[10].m_obj;
lean_object* v_res_250_;
v_res_250_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
stack->m_obj
 = v_res_250_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___boxed(lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_);
lean_dec(v_a_261_);
lean_dec_ref(v_a_260_);
lean_dec(v_a_259_);
lean_dec_ref(v_a_258_);
lean_dec(v_a_257_);
lean_dec_ref(v_a_256_);
lean_dec(v_a_255_);
lean_dec_ref(v_a_254_);
lean_dec(v_a_253_);
lean_dec(v_a_252_);
lean_dec(v_a_251_);
return v_res_263_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0(lean_object* v_00_u03b1_264_, lean_object* v_msg_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v_msg_265_, v___y_273_, v___y_274_, v___y_275_, v___y_276_);
return v___x_278_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_265_ = stack[1].m_obj;
lean_object* v___y_266_ = stack[2].m_obj;
lean_object* v___y_267_ = stack[3].m_obj;
lean_object* v___y_268_ = stack[4].m_obj;
lean_object* v___y_269_ = stack[5].m_obj;
lean_object* v___y_270_ = stack[6].m_obj;
lean_object* v___y_271_ = stack[7].m_obj;
lean_object* v___y_272_ = stack[8].m_obj;
lean_object* v___y_273_ = stack[9].m_obj;
lean_object* v___y_274_ = stack[10].m_obj;
lean_object* v___y_275_ = stack[11].m_obj;
lean_object* v___y_276_ = stack[12].m_obj;
lean_object* v_res_279_;
v_res_279_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0(lean_box(0), v_msg_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_);
stack->m_obj
 = v_res_279_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___boxed(lean_object* v_00_u03b1_280_, lean_object* v_msg_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0(v_00_u03b1_280_, v_msg_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec(v___y_283_);
lean_dec(v___y_282_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0(lean_object* v_a_295_, lean_object* v_f_296_, lean_object* v_s_297_){
_start:
{
lean_object* v_exp_298_; lean_object* v_rings_299_; lean_object* v_semirings_300_; lean_object* v_ncRings_301_; lean_object* v_ncSemirings_302_; lean_object* v_typeClassify_303_; lean_object* v_orders_304_; lean_object* v_typeOrderClassify_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v_exp_298_ = lean_ctor_get(v_s_297_, 0);
v_rings_299_ = lean_ctor_get(v_s_297_, 1);
v_semirings_300_ = lean_ctor_get(v_s_297_, 2);
v_ncRings_301_ = lean_ctor_get(v_s_297_, 3);
v_ncSemirings_302_ = lean_ctor_get(v_s_297_, 4);
v_typeClassify_303_ = lean_ctor_get(v_s_297_, 5);
v_orders_304_ = lean_ctor_get(v_s_297_, 6);
v_typeOrderClassify_305_ = lean_ctor_get(v_s_297_, 7);
v___x_306_ = lean_array_get_size(v_semirings_300_);
v___x_307_ = lean_nat_dec_lt(v_a_295_, v___x_306_);
if (v___x_307_ == 0)
{
lean_dec_ref(v_f_296_);
return v_s_297_;
}
else
{
lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_319_; 
lean_inc_ref(v_typeOrderClassify_305_);
lean_inc_ref(v_orders_304_);
lean_inc_ref(v_typeClassify_303_);
lean_inc_ref(v_ncSemirings_302_);
lean_inc_ref(v_ncRings_301_);
lean_inc_ref(v_semirings_300_);
lean_inc_ref(v_rings_299_);
lean_inc(v_exp_298_);
v_isSharedCheck_319_ = !lean_is_exclusive(v_s_297_);
if (v_isSharedCheck_319_ == 0)
{
lean_object* v_unused_320_; lean_object* v_unused_321_; lean_object* v_unused_322_; lean_object* v_unused_323_; lean_object* v_unused_324_; lean_object* v_unused_325_; lean_object* v_unused_326_; lean_object* v_unused_327_; 
v_unused_320_ = lean_ctor_get(v_s_297_, 7);
lean_dec(v_unused_320_);
v_unused_321_ = lean_ctor_get(v_s_297_, 6);
lean_dec(v_unused_321_);
v_unused_322_ = lean_ctor_get(v_s_297_, 5);
lean_dec(v_unused_322_);
v_unused_323_ = lean_ctor_get(v_s_297_, 4);
lean_dec(v_unused_323_);
v_unused_324_ = lean_ctor_get(v_s_297_, 3);
lean_dec(v_unused_324_);
v_unused_325_ = lean_ctor_get(v_s_297_, 2);
lean_dec(v_unused_325_);
v_unused_326_ = lean_ctor_get(v_s_297_, 1);
lean_dec(v_unused_326_);
v_unused_327_ = lean_ctor_get(v_s_297_, 0);
lean_dec(v_unused_327_);
v___x_309_ = v_s_297_;
v_isShared_310_ = v_isSharedCheck_319_;
goto v_resetjp_308_;
}
else
{
lean_dec(v_s_297_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_319_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v_v_311_; lean_object* v___x_312_; lean_object* v_xs_x27_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_317_; 
v_v_311_ = lean_array_fget(v_semirings_300_, v_a_295_);
v___x_312_ = lean_box(0);
v_xs_x27_313_ = lean_array_fset(v_semirings_300_, v_a_295_, v___x_312_);
v___x_314_ = lean_apply_1(v_f_296_, v_v_311_);
v___x_315_ = lean_array_fset(v_xs_x27_313_, v_a_295_, v___x_314_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 2, v___x_315_);
v___x_317_ = v___x_309_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_exp_298_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_rings_299_);
lean_ctor_set(v_reuseFailAlloc_318_, 2, v___x_315_);
lean_ctor_set(v_reuseFailAlloc_318_, 3, v_ncRings_301_);
lean_ctor_set(v_reuseFailAlloc_318_, 4, v_ncSemirings_302_);
lean_ctor_set(v_reuseFailAlloc_318_, 5, v_typeClassify_303_);
lean_ctor_set(v_reuseFailAlloc_318_, 6, v_orders_304_);
lean_ctor_set(v_reuseFailAlloc_318_, 7, v_typeOrderClassify_305_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed(lean_object* v_a_328_, lean_object* v_f_329_, lean_object* v_s_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0(v_a_328_, v_f_329_, v_s_330_);
lean_dec(v_a_328_);
return v_res_331_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg(lean_object* v_f_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v___f_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
lean_inc(v_a_333_);
v___f_336_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_336_, 0, v_a_333_);
lean_closure_set(v___f_336_, 1, v_f_332_);
v___x_337_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_338_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_337_, v___f_336_, v_a_334_);
return v___x_338_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_332_ = stack[0].m_obj;
lean_object* v_a_333_ = stack[1].m_obj;
lean_object* v_a_334_ = stack[2].m_obj;
lean_object* v_res_339_;
v_res_339_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg(v_f_332_, v_a_333_, v_a_334_);
stack->m_obj
 = v_res_339_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___boxed(lean_object* v_f_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg(v_f_340_, v_a_341_, v_a_342_);
lean_dec(v_a_342_);
lean_dec(v_a_341_);
return v_res_344_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring(lean_object* v_f_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v___f_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
lean_inc(v_a_346_);
v___f_358_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_358_, 0, v_a_346_);
lean_closure_set(v___f_358_, 1, v_f_345_);
v___x_359_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_360_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_359_, v___f_358_, v_a_352_);
return v___x_360_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_345_ = stack[0].m_obj;
lean_object* v_a_346_ = stack[1].m_obj;
lean_object* v_a_347_ = stack[2].m_obj;
lean_object* v_a_348_ = stack[3].m_obj;
lean_object* v_a_349_ = stack[4].m_obj;
lean_object* v_a_350_ = stack[5].m_obj;
lean_object* v_a_351_ = stack[6].m_obj;
lean_object* v_a_352_ = stack[7].m_obj;
lean_object* v_a_353_ = stack[8].m_obj;
lean_object* v_a_354_ = stack[9].m_obj;
lean_object* v_a_355_ = stack[10].m_obj;
lean_object* v_a_356_ = stack[11].m_obj;
lean_object* v_res_361_;
v_res_361_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring(v_f_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
stack->m_obj
 = v_res_361_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___boxed(lean_object* v_f_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring(v_f_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
lean_dec(v_a_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
lean_dec(v_a_365_);
lean_dec(v_a_364_);
lean_dec(v_a_363_);
return v_res_375_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_377_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__0));
v___x_378_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___boxed), 12, 0);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v___x_377_);
return v___x_379_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM(void){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1);
return v___x_380_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__0));
v___x_383_ = l_Lean_stringToMessageData(v___x_382_);
return v___x_383_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_390_, v_a_393_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; lean_object* v___x_398_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
lean_inc(v_a_397_);
lean_dec_ref_known(v___x_396_, 1);
v___x_398_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_413_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_413_ == 0)
{
v___x_401_ = v___x_398_;
v_isShared_402_ = v_isSharedCheck_413_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_398_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_413_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v_ringId_403_; lean_object* v_rings_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v_ringId_403_ = lean_ctor_get(v_a_399_, 1);
lean_inc(v_ringId_403_);
lean_dec(v_a_399_);
v_rings_404_ = lean_ctor_get(v_a_397_, 1);
lean_inc_ref(v_rings_404_);
lean_dec(v_a_397_);
v___x_405_ = lean_array_get_size(v_rings_404_);
v___x_406_ = lean_nat_dec_lt(v_ringId_403_, v___x_405_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; lean_object* v___x_408_; 
lean_dec_ref(v_rings_404_);
lean_dec(v_ringId_403_);
lean_del_object(v___x_401_);
v___x_407_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1);
v___x_408_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v___x_407_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
return v___x_408_;
}
else
{
lean_object* v___x_409_; lean_object* v___x_411_; 
v___x_409_ = lean_array_fget(v_rings_404_, v_ringId_403_);
lean_dec(v_ringId_403_);
lean_dec_ref(v_rings_404_);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v___x_409_);
v___x_411_ = v___x_401_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec(v_a_397_);
v_a_414_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_398_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_398_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
v_a_422_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_396_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_396_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_384_ = stack[0].m_obj;
lean_object* v_a_385_ = stack[1].m_obj;
lean_object* v_a_386_ = stack[2].m_obj;
lean_object* v_a_387_ = stack[3].m_obj;
lean_object* v_a_388_ = stack[4].m_obj;
lean_object* v_a_389_ = stack[5].m_obj;
lean_object* v_a_390_ = stack[6].m_obj;
lean_object* v_a_391_ = stack[7].m_obj;
lean_object* v_a_392_ = stack[8].m_obj;
lean_object* v_a_393_ = stack[9].m_obj;
lean_object* v_a_394_ = stack[10].m_obj;
lean_object* v_res_430_;
v_res_430_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
stack->m_obj
 = v_res_430_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___boxed(lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec(v_a_432_);
lean_dec(v_a_431_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0(lean_object* v_ringId_444_, lean_object* v_f_445_, lean_object* v_s_446_){
_start:
{
lean_object* v_exp_447_; lean_object* v_rings_448_; lean_object* v_semirings_449_; lean_object* v_ncRings_450_; lean_object* v_ncSemirings_451_; lean_object* v_typeClassify_452_; lean_object* v_orders_453_; lean_object* v_typeOrderClassify_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v_exp_447_ = lean_ctor_get(v_s_446_, 0);
v_rings_448_ = lean_ctor_get(v_s_446_, 1);
v_semirings_449_ = lean_ctor_get(v_s_446_, 2);
v_ncRings_450_ = lean_ctor_get(v_s_446_, 3);
v_ncSemirings_451_ = lean_ctor_get(v_s_446_, 4);
v_typeClassify_452_ = lean_ctor_get(v_s_446_, 5);
v_orders_453_ = lean_ctor_get(v_s_446_, 6);
v_typeOrderClassify_454_ = lean_ctor_get(v_s_446_, 7);
v___x_455_ = lean_array_get_size(v_rings_448_);
v___x_456_ = lean_nat_dec_lt(v_ringId_444_, v___x_455_);
if (v___x_456_ == 0)
{
lean_dec_ref(v_f_445_);
return v_s_446_;
}
else
{
lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_468_; 
lean_inc_ref(v_typeOrderClassify_454_);
lean_inc_ref(v_orders_453_);
lean_inc_ref(v_typeClassify_452_);
lean_inc_ref(v_ncSemirings_451_);
lean_inc_ref(v_ncRings_450_);
lean_inc_ref(v_semirings_449_);
lean_inc_ref(v_rings_448_);
lean_inc(v_exp_447_);
v_isSharedCheck_468_ = !lean_is_exclusive(v_s_446_);
if (v_isSharedCheck_468_ == 0)
{
lean_object* v_unused_469_; lean_object* v_unused_470_; lean_object* v_unused_471_; lean_object* v_unused_472_; lean_object* v_unused_473_; lean_object* v_unused_474_; lean_object* v_unused_475_; lean_object* v_unused_476_; 
v_unused_469_ = lean_ctor_get(v_s_446_, 7);
lean_dec(v_unused_469_);
v_unused_470_ = lean_ctor_get(v_s_446_, 6);
lean_dec(v_unused_470_);
v_unused_471_ = lean_ctor_get(v_s_446_, 5);
lean_dec(v_unused_471_);
v_unused_472_ = lean_ctor_get(v_s_446_, 4);
lean_dec(v_unused_472_);
v_unused_473_ = lean_ctor_get(v_s_446_, 3);
lean_dec(v_unused_473_);
v_unused_474_ = lean_ctor_get(v_s_446_, 2);
lean_dec(v_unused_474_);
v_unused_475_ = lean_ctor_get(v_s_446_, 1);
lean_dec(v_unused_475_);
v_unused_476_ = lean_ctor_get(v_s_446_, 0);
lean_dec(v_unused_476_);
v___x_458_ = v_s_446_;
v_isShared_459_ = v_isSharedCheck_468_;
goto v_resetjp_457_;
}
else
{
lean_dec(v_s_446_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_468_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v_v_460_; lean_object* v___x_461_; lean_object* v_xs_x27_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
v_v_460_ = lean_array_fget(v_rings_448_, v_ringId_444_);
v___x_461_ = lean_box(0);
v_xs_x27_462_ = lean_array_fset(v_rings_448_, v_ringId_444_, v___x_461_);
v___x_463_ = lean_apply_1(v_f_445_, v_v_460_);
v___x_464_ = lean_array_fset(v_xs_x27_462_, v_ringId_444_, v___x_463_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 1, v___x_464_);
v___x_466_ = v___x_458_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_exp_447_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_467_, 2, v_semirings_449_);
lean_ctor_set(v_reuseFailAlloc_467_, 3, v_ncRings_450_);
lean_ctor_set(v_reuseFailAlloc_467_, 4, v_ncSemirings_451_);
lean_ctor_set(v_reuseFailAlloc_467_, 5, v_typeClassify_452_);
lean_ctor_set(v_reuseFailAlloc_467_, 6, v_orders_453_);
lean_ctor_set(v_reuseFailAlloc_467_, 7, v_typeOrderClassify_454_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0___boxed(lean_object* v_ringId_477_, lean_object* v_f_478_, lean_object* v_s_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0(v_ringId_477_, v_f_478_, v_s_479_);
lean_dec(v_ringId_477_);
return v_res_480_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(lean_object* v_f_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v_a_495_; lean_object* v_ringId_496_; lean_object* v___f_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v_a_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_a_495_);
lean_dec_ref_known(v___x_494_, 1);
v_ringId_496_ = lean_ctor_get(v_a_495_, 1);
lean_inc(v_ringId_496_);
lean_dec(v_a_495_);
v___f_497_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0___boxed), 3, 2);
lean_closure_set(v___f_497_, 0, v_ringId_496_);
lean_closure_set(v___f_497_, 1, v_f_481_);
v___x_498_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_499_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_498_, v___f_497_, v_a_488_);
return v___x_499_;
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
lean_dec_ref(v_f_481_);
v_a_500_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_494_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_494_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_481_ = stack[0].m_obj;
lean_object* v_a_482_ = stack[1].m_obj;
lean_object* v_a_483_ = stack[2].m_obj;
lean_object* v_a_484_ = stack[3].m_obj;
lean_object* v_a_485_ = stack[4].m_obj;
lean_object* v_a_486_ = stack[5].m_obj;
lean_object* v_a_487_ = stack[6].m_obj;
lean_object* v_a_488_ = stack[7].m_obj;
lean_object* v_a_489_ = stack[8].m_obj;
lean_object* v_a_490_ = stack[9].m_obj;
lean_object* v_a_491_ = stack[10].m_obj;
lean_object* v_a_492_ = stack[11].m_obj;
lean_object* v_res_508_;
v_res_508_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v_f_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
stack->m_obj
 = v_res_508_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___boxed(lean_object* v_f_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v_f_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec(v_a_512_);
lean_dec(v_a_511_);
lean_dec(v_a_510_);
return v_res_522_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_524_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__0));
v___x_525_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___boxed), 12, 0);
v___x_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
lean_ctor_set(v___x_526_, 1, v___x_524_);
return v___x_526_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM(void){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1);
return v___x_527_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState___redArg(lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_529_, v_a_530_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_541_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_541_ == 0)
{
v___x_535_ = v___x_532_;
v_isShared_536_ = v_isSharedCheck_541_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_532_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_541_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; lean_object* v___x_539_; 
v___x_537_ = l_Lean_Meta_Grind_Arith_CommRing_State_getSemiring(v_a_533_, v_a_528_);
lean_dec(v_a_533_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v___x_537_);
v___x_539_ = v___x_535_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_537_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
v_a_542_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_532_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_532_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_528_ = stack[0].m_obj;
lean_object* v_a_529_ = stack[1].m_obj;
lean_object* v_a_530_ = stack[2].m_obj;
lean_object* v_res_550_;
v_res_550_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState___redArg(v_a_528_, v_a_529_, v_a_530_);
stack->m_obj
 = v_res_550_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState___redArg___boxed(lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState___redArg(v_a_551_, v_a_552_, v_a_553_);
lean_dec_ref(v_a_553_);
lean_dec(v_a_552_);
lean_dec(v_a_551_);
return v_res_555_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState(lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState___redArg(v_a_556_, v_a_557_, v_a_565_);
return v___x_568_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_556_ = stack[0].m_obj;
lean_object* v_a_557_ = stack[1].m_obj;
lean_object* v_a_558_ = stack[2].m_obj;
lean_object* v_a_559_ = stack[3].m_obj;
lean_object* v_a_560_ = stack[4].m_obj;
lean_object* v_a_561_ = stack[5].m_obj;
lean_object* v_a_562_ = stack[6].m_obj;
lean_object* v_a_563_ = stack[7].m_obj;
lean_object* v_a_564_ = stack[8].m_obj;
lean_object* v_a_565_ = stack[9].m_obj;
lean_object* v_a_566_ = stack[10].m_obj;
lean_object* v_res_569_;
v_res_569_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState(v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_);
stack->m_obj
 = v_res_569_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState___boxed(lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState(v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
lean_dec(v_a_572_);
lean_dec(v_a_571_);
lean_dec(v_a_570_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg___lam__0(lean_object* v_a_583_, lean_object* v_f_584_, lean_object* v_s_585_){
_start:
{
lean_object* v_rings_586_; lean_object* v_exprToRingId_587_; lean_object* v_semirings_588_; lean_object* v_exprToSemiringId_589_; lean_object* v_ncRings_590_; lean_object* v_exprToNCRingId_591_; lean_object* v_ncSemirings_592_; lean_object* v_exprToNCSemiringId_593_; lean_object* v_steps_594_; uint8_t v_reportedMaxDegreeIssue_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_616_; 
v_rings_586_ = lean_ctor_get(v_s_585_, 0);
v_exprToRingId_587_ = lean_ctor_get(v_s_585_, 1);
v_semirings_588_ = lean_ctor_get(v_s_585_, 2);
v_exprToSemiringId_589_ = lean_ctor_get(v_s_585_, 3);
v_ncRings_590_ = lean_ctor_get(v_s_585_, 4);
v_exprToNCRingId_591_ = lean_ctor_get(v_s_585_, 5);
v_ncSemirings_592_ = lean_ctor_get(v_s_585_, 6);
v_exprToNCSemiringId_593_ = lean_ctor_get(v_s_585_, 7);
v_steps_594_ = lean_ctor_get(v_s_585_, 8);
v_reportedMaxDegreeIssue_595_ = lean_ctor_get_uint8(v_s_585_, sizeof(void*)*9);
v_isSharedCheck_616_ = !lean_is_exclusive(v_s_585_);
if (v_isSharedCheck_616_ == 0)
{
v___x_597_ = v_s_585_;
v_isShared_598_ = v_isSharedCheck_616_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_steps_594_);
lean_inc(v_exprToNCSemiringId_593_);
lean_inc(v_ncSemirings_592_);
lean_inc(v_exprToNCRingId_591_);
lean_inc(v_ncRings_590_);
lean_inc(v_exprToSemiringId_589_);
lean_inc(v_semirings_588_);
lean_inc(v_exprToRingId_587_);
lean_inc(v_rings_586_);
lean_dec(v_s_585_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_616_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_599_ = lean_unsigned_to_nat(1u);
v___x_600_ = lean_nat_add(v_a_583_, v___x_599_);
v___x_601_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default;
v___x_602_ = l_Array_rightpad___redArg(v___x_600_, v___x_601_, v_semirings_588_);
lean_dec(v___x_600_);
v___x_603_ = lean_array_get_size(v___x_602_);
v___x_604_ = lean_nat_dec_lt(v_a_583_, v___x_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_606_; 
lean_dec_ref(v_f_584_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 2, v___x_602_);
v___x_606_ = v___x_597_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_rings_586_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_exprToRingId_587_);
lean_ctor_set(v_reuseFailAlloc_607_, 2, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_607_, 3, v_exprToSemiringId_589_);
lean_ctor_set(v_reuseFailAlloc_607_, 4, v_ncRings_590_);
lean_ctor_set(v_reuseFailAlloc_607_, 5, v_exprToNCRingId_591_);
lean_ctor_set(v_reuseFailAlloc_607_, 6, v_ncSemirings_592_);
lean_ctor_set(v_reuseFailAlloc_607_, 7, v_exprToNCSemiringId_593_);
lean_ctor_set(v_reuseFailAlloc_607_, 8, v_steps_594_);
lean_ctor_set_uint8(v_reuseFailAlloc_607_, sizeof(void*)*9, v_reportedMaxDegreeIssue_595_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
else
{
lean_object* v_v_608_; lean_object* v___x_609_; lean_object* v_xs_x27_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_614_; 
v_v_608_ = lean_array_fget(v___x_602_, v_a_583_);
v___x_609_ = lean_box(0);
v_xs_x27_610_ = lean_array_fset(v___x_602_, v_a_583_, v___x_609_);
v___x_611_ = lean_apply_1(v_f_584_, v_v_608_);
v___x_612_ = lean_array_fset(v_xs_x27_610_, v_a_583_, v___x_611_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 2, v___x_612_);
v___x_614_ = v___x_597_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_rings_586_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_exprToRingId_587_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_615_, 3, v_exprToSemiringId_589_);
lean_ctor_set(v_reuseFailAlloc_615_, 4, v_ncRings_590_);
lean_ctor_set(v_reuseFailAlloc_615_, 5, v_exprToNCRingId_591_);
lean_ctor_set(v_reuseFailAlloc_615_, 6, v_ncSemirings_592_);
lean_ctor_set(v_reuseFailAlloc_615_, 7, v_exprToNCSemiringId_593_);
lean_ctor_set(v_reuseFailAlloc_615_, 8, v_steps_594_);
lean_ctor_set_uint8(v_reuseFailAlloc_615_, sizeof(void*)*9, v_reportedMaxDegreeIssue_595_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg___lam__0___boxed(lean_object* v_a_617_, lean_object* v_f_618_, lean_object* v_s_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg___lam__0(v_a_617_, v_f_618_, v_s_619_);
lean_dec(v_a_617_);
return v_res_620_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg(lean_object* v_f_621_, lean_object* v_a_622_, lean_object* v_a_623_){
_start:
{
lean_object* v___f_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
lean_inc(v_a_622_);
v___f_625_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_625_, 0, v_a_622_);
lean_closure_set(v___f_625_, 1, v_f_621_);
v___x_626_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_627_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_626_, v___f_625_, v_a_623_);
return v___x_627_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_621_ = stack[0].m_obj;
lean_object* v_a_622_ = stack[1].m_obj;
lean_object* v_a_623_ = stack[2].m_obj;
lean_object* v_res_628_;
v_res_628_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg(v_f_621_, v_a_622_, v_a_623_);
stack->m_obj
 = v_res_628_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg___boxed(lean_object* v_f_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg(v_f_629_, v_a_630_, v_a_631_);
lean_dec(v_a_631_);
lean_dec(v_a_630_);
return v_res_633_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState(lean_object* v_f_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg(v_f_634_, v_a_635_, v_a_636_);
return v___x_647_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_634_ = stack[0].m_obj;
lean_object* v_a_635_ = stack[1].m_obj;
lean_object* v_a_636_ = stack[2].m_obj;
lean_object* v_a_637_ = stack[3].m_obj;
lean_object* v_a_638_ = stack[4].m_obj;
lean_object* v_a_639_ = stack[5].m_obj;
lean_object* v_a_640_ = stack[6].m_obj;
lean_object* v_a_641_ = stack[7].m_obj;
lean_object* v_a_642_ = stack[8].m_obj;
lean_object* v_a_643_ = stack[9].m_obj;
lean_object* v_a_644_ = stack[10].m_obj;
lean_object* v_a_645_ = stack[11].m_obj;
lean_object* v_res_648_;
v_res_648_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState(v_f_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
stack->m_obj
 = v_res_648_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___boxed(lean_object* v_f_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState(v_f_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_);
lean_dec(v_a_660_);
lean_dec_ref(v_a_659_);
lean_dec(v_a_658_);
lean_dec_ref(v_a_657_);
lean_dec(v_a_656_);
lean_dec_ref(v_a_655_);
lean_dec(v_a_654_);
lean_dec_ref(v_a_653_);
lean_dec(v_a_652_);
lean_dec(v_a_651_);
lean_dec(v_a_650_);
return v_res_662_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM___closed__1(void){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_664_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM___closed__0));
v___x_665_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState___boxed), 12, 0);
v___x_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
lean_ctor_set(v___x_666_, 1, v___x_664_);
return v___x_666_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM(void){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM___closed__1);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_668_, lean_object* v_vals_669_, lean_object* v_i_670_, lean_object* v_k_671_){
_start:
{
lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_672_ = lean_array_get_size(v_keys_668_);
v___x_673_ = lean_nat_dec_lt(v_i_670_, v___x_672_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; 
lean_dec(v_i_670_);
v___x_674_ = lean_box(0);
return v___x_674_;
}
else
{
lean_object* v_k_x27_675_; size_t v___x_676_; size_t v___x_677_; uint8_t v___x_678_; 
v_k_x27_675_ = lean_array_fget_borrowed(v_keys_668_, v_i_670_);
v___x_676_ = lean_ptr_addr(v_k_671_);
v___x_677_ = lean_ptr_addr(v_k_x27_675_);
v___x_678_ = lean_usize_dec_eq(v___x_676_, v___x_677_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = lean_unsigned_to_nat(1u);
v___x_680_ = lean_nat_add(v_i_670_, v___x_679_);
lean_dec(v_i_670_);
v_i_670_ = v___x_680_;
goto _start;
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_array_fget_borrowed(v_vals_669_, v_i_670_);
lean_dec(v_i_670_);
lean_inc(v___x_682_);
v___x_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
return v___x_683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_684_, lean_object* v_vals_685_, lean_object* v_i_686_, lean_object* v_k_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_684_, v_vals_685_, v_i_686_, v_k_687_);
lean_dec_ref(v_k_687_);
lean_dec_ref(v_vals_685_);
lean_dec_ref(v_keys_684_);
return v_res_688_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(lean_object* v_x_689_, size_t v_x_690_, lean_object* v_x_691_){
_start:
{
if (lean_obj_tag(v_x_689_) == 0)
{
lean_object* v_es_692_; lean_object* v___x_693_; size_t v___x_694_; size_t v___x_695_; lean_object* v_j_696_; lean_object* v___x_697_; 
v_es_692_ = lean_ctor_get(v_x_689_, 0);
v___x_693_ = lean_box(2);
v___x_694_ = ((size_t)31ULL);
v___x_695_ = lean_usize_land(v_x_690_, v___x_694_);
v_j_696_ = lean_usize_to_nat(v___x_695_);
v___x_697_ = lean_array_get_borrowed(v___x_693_, v_es_692_, v_j_696_);
lean_dec(v_j_696_);
switch(lean_obj_tag(v___x_697_))
{
case 0:
{
lean_object* v_key_698_; lean_object* v_val_699_; size_t v___x_700_; size_t v___x_701_; uint8_t v___x_702_; 
v_key_698_ = lean_ctor_get(v___x_697_, 0);
v_val_699_ = lean_ctor_get(v___x_697_, 1);
v___x_700_ = lean_ptr_addr(v_x_691_);
v___x_701_ = lean_ptr_addr(v_key_698_);
v___x_702_ = lean_usize_dec_eq(v___x_700_, v___x_701_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; 
v___x_703_ = lean_box(0);
return v___x_703_;
}
else
{
lean_object* v___x_704_; 
lean_inc(v_val_699_);
v___x_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_704_, 0, v_val_699_);
return v___x_704_;
}
}
case 1:
{
lean_object* v_node_705_; size_t v___x_706_; size_t v___x_707_; 
v_node_705_ = lean_ctor_get(v___x_697_, 0);
v___x_706_ = ((size_t)5ULL);
v___x_707_ = lean_usize_shift_right(v_x_690_, v___x_706_);
v_x_689_ = v_node_705_;
v_x_690_ = v___x_707_;
goto _start;
}
default: 
{
lean_object* v___x_709_; 
v___x_709_ = lean_box(0);
return v___x_709_;
}
}
}
else
{
lean_object* v_ks_710_; lean_object* v_vs_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v_ks_710_ = lean_ctor_get(v_x_689_, 0);
v_vs_711_ = lean_ctor_get(v_x_689_, 1);
v___x_712_ = lean_unsigned_to_nat(0u);
v___x_713_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_710_, v_vs_711_, v___x_712_, v_x_691_);
return v___x_713_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_689_ = stack[0].m_obj;
size_t v_x_690_ = stack[1].m_num;
lean_object* v_x_691_ = stack[2].m_obj;
lean_object* v_res_714_;
v_res_714_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_689_, v_x_690_, v_x_691_);
stack->m_obj
 = v_res_714_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_715_, lean_object* v_x_716_, lean_object* v_x_717_){
_start:
{
size_t v_x_916__boxed_718_; lean_object* v_res_719_; 
v_x_916__boxed_718_ = lean_unbox_usize(v_x_716_);
lean_dec(v_x_716_);
v_res_719_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_715_, v_x_916__boxed_718_, v_x_717_);
lean_dec_ref(v_x_717_);
lean_dec_ref(v_x_715_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(lean_object* v_x_720_, lean_object* v_x_721_){
_start:
{
size_t v___x_722_; size_t v___x_723_; size_t v___x_724_; uint64_t v___x_725_; size_t v___x_726_; lean_object* v___x_727_; 
v___x_722_ = lean_ptr_addr(v_x_721_);
v___x_723_ = ((size_t)3ULL);
v___x_724_ = lean_usize_shift_right(v___x_722_, v___x_723_);
v___x_725_ = lean_usize_to_uint64(v___x_724_);
v___x_726_ = lean_uint64_to_usize(v___x_725_);
v___x_727_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_720_, v___x_726_, v_x_721_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg___boxed(lean_object* v_x_728_, lean_object* v_x_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_x_728_, v_x_729_);
lean_dec_ref(v_x_729_);
lean_dec_ref(v_x_728_);
return v_res_730_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(lean_object* v_e_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_732_, v_a_733_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_745_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_745_ == 0)
{
v___x_738_ = v___x_735_;
v_isShared_739_ = v_isSharedCheck_745_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_745_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v_exprToSemiringId_740_; lean_object* v___x_741_; lean_object* v___x_743_; 
v_exprToSemiringId_740_ = lean_ctor_get(v_a_736_, 3);
lean_inc_ref(v_exprToSemiringId_740_);
lean_dec(v_a_736_);
v___x_741_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_exprToSemiringId_740_, v_e_731_);
lean_dec_ref(v_exprToSemiringId_740_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_741_);
v___x_743_ = v___x_738_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_741_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
v_a_746_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_735_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_735_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_731_ = stack[0].m_obj;
lean_object* v_a_732_ = stack[1].m_obj;
lean_object* v_a_733_ = stack[2].m_obj;
lean_object* v_res_754_;
v_res_754_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_731_, v_a_732_, v_a_733_);
stack->m_obj
 = v_res_754_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg___boxed(lean_object* v_e_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_755_, v_a_756_, v_a_757_);
lean_dec_ref(v_a_757_);
lean_dec(v_a_756_);
lean_dec_ref(v_e_755_);
return v_res_759_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f(lean_object* v_e_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_760_, v_a_761_, v_a_769_);
return v___x_772_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_760_ = stack[0].m_obj;
lean_object* v_a_761_ = stack[1].m_obj;
lean_object* v_a_762_ = stack[2].m_obj;
lean_object* v_a_763_ = stack[3].m_obj;
lean_object* v_a_764_ = stack[4].m_obj;
lean_object* v_a_765_ = stack[5].m_obj;
lean_object* v_a_766_ = stack[6].m_obj;
lean_object* v_a_767_ = stack[7].m_obj;
lean_object* v_a_768_ = stack[8].m_obj;
lean_object* v_a_769_ = stack[9].m_obj;
lean_object* v_a_770_ = stack[10].m_obj;
lean_object* v_res_773_;
v_res_773_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f(v_e_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_);
stack->m_obj
 = v_res_773_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___boxed(lean_object* v_e_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f(v_e_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
lean_dec(v_a_782_);
lean_dec_ref(v_a_781_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec(v_a_776_);
lean_dec(v_a_775_);
lean_dec_ref(v_e_774_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0(lean_object* v_00_u03b2_787_, lean_object* v_x_788_, lean_object* v_x_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_x_788_, v_x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___boxed(lean_object* v_00_u03b2_791_, lean_object* v_x_792_, lean_object* v_x_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0(v_00_u03b2_791_, v_x_792_, v_x_793_);
lean_dec_ref(v_x_793_);
lean_dec_ref(v_x_792_);
return v_res_794_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_795_, lean_object* v_x_796_, size_t v_x_797_, lean_object* v_x_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_796_, v_x_797_, v_x_798_);
return v___x_799_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_796_ = stack[1].m_obj;
size_t v_x_797_ = stack[2].m_num;
lean_object* v_x_798_ = stack[3].m_obj;
lean_object* v_res_800_;
v_res_800_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0(lean_box(0), v_x_796_, v_x_797_, v_x_798_);
stack->m_obj
 = v_res_800_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_801_, lean_object* v_x_802_, lean_object* v_x_803_, lean_object* v_x_804_){
_start:
{
size_t v_x_1102__boxed_805_; lean_object* v_res_806_; 
v_x_1102__boxed_805_ = lean_unbox_usize(v_x_803_);
lean_dec(v_x_803_);
v_res_806_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0(v_00_u03b2_801_, v_x_802_, v_x_1102__boxed_805_, v_x_804_);
lean_dec_ref(v_x_804_);
lean_dec_ref(v_x_802_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_807_, lean_object* v_keys_808_, lean_object* v_vals_809_, lean_object* v_heq_810_, lean_object* v_i_811_, lean_object* v_k_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_808_, v_vals_809_, v_i_811_, v_k_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_814_, lean_object* v_keys_815_, lean_object* v_vals_816_, lean_object* v_heq_817_, lean_object* v_i_818_, lean_object* v_k_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_814_, v_keys_815_, v_vals_816_, v_heq_817_, v_i_818_, v_k_819_);
lean_dec_ref(v_k_819_);
lean_dec_ref(v_vals_816_);
lean_dec_ref(v_keys_815_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_821_, lean_object* v_x_822_, lean_object* v_x_823_, lean_object* v_x_824_){
_start:
{
lean_object* v_ks_825_; lean_object* v_vs_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_852_; 
v_ks_825_ = lean_ctor_get(v_x_821_, 0);
v_vs_826_ = lean_ctor_get(v_x_821_, 1);
v_isSharedCheck_852_ = !lean_is_exclusive(v_x_821_);
if (v_isSharedCheck_852_ == 0)
{
v___x_828_ = v_x_821_;
v_isShared_829_ = v_isSharedCheck_852_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_vs_826_);
lean_inc(v_ks_825_);
lean_dec(v_x_821_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_852_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_830_ = lean_array_get_size(v_ks_825_);
v___x_831_ = lean_nat_dec_lt(v_x_822_, v___x_830_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_835_; 
lean_dec(v_x_822_);
v___x_832_ = lean_array_push(v_ks_825_, v_x_823_);
v___x_833_ = lean_array_push(v_vs_826_, v_x_824_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 1, v___x_833_);
lean_ctor_set(v___x_828_, 0, v___x_832_);
v___x_835_ = v___x_828_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_832_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
else
{
lean_object* v_k_x27_837_; size_t v___x_838_; size_t v___x_839_; uint8_t v___x_840_; 
v_k_x27_837_ = lean_array_fget_borrowed(v_ks_825_, v_x_822_);
v___x_838_ = lean_ptr_addr(v_x_823_);
v___x_839_ = lean_ptr_addr(v_k_x27_837_);
v___x_840_ = lean_usize_dec_eq(v___x_838_, v___x_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_842_; 
if (v_isShared_829_ == 0)
{
v___x_842_ = v___x_828_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_ks_825_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_vs_826_);
v___x_842_ = v_reuseFailAlloc_846_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = lean_unsigned_to_nat(1u);
v___x_844_ = lean_nat_add(v_x_822_, v___x_843_);
lean_dec(v_x_822_);
v_x_821_ = v___x_842_;
v_x_822_ = v___x_844_;
goto _start;
}
}
else
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_850_; 
v___x_847_ = lean_array_fset(v_ks_825_, v_x_822_, v_x_823_);
v___x_848_ = lean_array_fset(v_vs_826_, v_x_822_, v_x_824_);
lean_dec(v_x_822_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 1, v___x_848_);
lean_ctor_set(v___x_828_, 0, v___x_847_);
v___x_850_ = v___x_828_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v___x_848_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_853_, lean_object* v_k_854_, lean_object* v_v_855_){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = lean_unsigned_to_nat(0u);
v___x_857_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_853_, v___x_856_, v_k_854_, v_v_855_);
return v___x_857_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_858_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(lean_object* v_x_859_, size_t v_x_860_, size_t v_x_861_, lean_object* v_x_862_, lean_object* v_x_863_){
_start:
{
if (lean_obj_tag(v_x_859_) == 0)
{
lean_object* v_es_864_; size_t v___x_865_; size_t v___x_866_; lean_object* v_j_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v_es_864_ = lean_ctor_get(v_x_859_, 0);
v___x_865_ = ((size_t)31ULL);
v___x_866_ = lean_usize_land(v_x_860_, v___x_865_);
v_j_867_ = lean_usize_to_nat(v___x_866_);
v___x_868_ = lean_array_get_size(v_es_864_);
v___x_869_ = lean_nat_dec_lt(v_j_867_, v___x_868_);
if (v___x_869_ == 0)
{
lean_dec(v_j_867_);
lean_dec(v_x_863_);
lean_dec_ref(v_x_862_);
return v_x_859_;
}
else
{
lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_910_; 
lean_inc_ref(v_es_864_);
v_isSharedCheck_910_ = !lean_is_exclusive(v_x_859_);
if (v_isSharedCheck_910_ == 0)
{
lean_object* v_unused_911_; 
v_unused_911_ = lean_ctor_get(v_x_859_, 0);
lean_dec(v_unused_911_);
v___x_871_ = v_x_859_;
v_isShared_872_ = v_isSharedCheck_910_;
goto v_resetjp_870_;
}
else
{
lean_dec(v_x_859_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_910_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v_v_873_; lean_object* v___x_874_; lean_object* v_xs_x27_875_; lean_object* v___y_877_; 
v_v_873_ = lean_array_fget(v_es_864_, v_j_867_);
v___x_874_ = lean_box(0);
v_xs_x27_875_ = lean_array_fset(v_es_864_, v_j_867_, v___x_874_);
switch(lean_obj_tag(v_v_873_))
{
case 0:
{
lean_object* v_key_882_; lean_object* v_val_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_895_; 
v_key_882_ = lean_ctor_get(v_v_873_, 0);
v_val_883_ = lean_ctor_get(v_v_873_, 1);
v_isSharedCheck_895_ = !lean_is_exclusive(v_v_873_);
if (v_isSharedCheck_895_ == 0)
{
v___x_885_ = v_v_873_;
v_isShared_886_ = v_isSharedCheck_895_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_val_883_);
lean_inc(v_key_882_);
lean_dec(v_v_873_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_895_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
size_t v___x_887_; size_t v___x_888_; uint8_t v___x_889_; 
v___x_887_ = lean_ptr_addr(v_x_862_);
v___x_888_ = lean_ptr_addr(v_key_882_);
v___x_889_ = lean_usize_dec_eq(v___x_887_, v___x_888_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; lean_object* v___x_891_; 
lean_del_object(v___x_885_);
v___x_890_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_882_, v_val_883_, v_x_862_, v_x_863_);
v___x_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
v___y_877_ = v___x_891_;
goto v___jp_876_;
}
else
{
lean_object* v___x_893_; 
lean_dec(v_val_883_);
lean_dec(v_key_882_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 1, v_x_863_);
lean_ctor_set(v___x_885_, 0, v_x_862_);
v___x_893_ = v___x_885_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_x_862_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_x_863_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
v___y_877_ = v___x_893_;
goto v___jp_876_;
}
}
}
}
case 1:
{
lean_object* v_node_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_908_; 
v_node_896_ = lean_ctor_get(v_v_873_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v_v_873_);
if (v_isSharedCheck_908_ == 0)
{
v___x_898_ = v_v_873_;
v_isShared_899_ = v_isSharedCheck_908_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_node_896_);
lean_dec(v_v_873_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_908_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
size_t v___x_900_; size_t v___x_901_; size_t v___x_902_; size_t v___x_903_; lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_900_ = ((size_t)5ULL);
v___x_901_ = lean_usize_shift_right(v_x_860_, v___x_900_);
v___x_902_ = ((size_t)1ULL);
v___x_903_ = lean_usize_add(v_x_861_, v___x_902_);
v___x_904_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_node_896_, v___x_901_, v___x_903_, v_x_862_, v_x_863_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v___x_904_);
v___x_906_ = v___x_898_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_904_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
v___y_877_ = v___x_906_;
goto v___jp_876_;
}
}
}
default: 
{
lean_object* v___x_909_; 
v___x_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_909_, 0, v_x_862_);
lean_ctor_set(v___x_909_, 1, v_x_863_);
v___y_877_ = v___x_909_;
goto v___jp_876_;
}
}
v___jp_876_:
{
lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_878_ = lean_array_fset(v_xs_x27_875_, v_j_867_, v___y_877_);
lean_dec(v_j_867_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_878_);
v___x_880_ = v___x_871_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
else
{
lean_object* v_ks_912_; lean_object* v_vs_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_931_; 
v_ks_912_ = lean_ctor_get(v_x_859_, 0);
v_vs_913_ = lean_ctor_get(v_x_859_, 1);
v_isSharedCheck_931_ = !lean_is_exclusive(v_x_859_);
if (v_isSharedCheck_931_ == 0)
{
v___x_915_ = v_x_859_;
v_isShared_916_ = v_isSharedCheck_931_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_vs_913_);
lean_inc(v_ks_912_);
lean_dec(v_x_859_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_931_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_ks_912_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_vs_913_);
v___x_918_ = v_reuseFailAlloc_930_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
lean_object* v_newNode_919_; size_t v___x_920_; uint8_t v___x_921_; 
v_newNode_919_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(v___x_918_, v_x_862_, v_x_863_);
v___x_920_ = ((size_t)7ULL);
v___x_921_ = lean_usize_dec_le(v___x_920_, v_x_861_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_922_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_919_);
v___x_923_ = lean_unsigned_to_nat(4u);
v___x_924_ = lean_nat_dec_lt(v___x_922_, v___x_923_);
lean_dec(v___x_922_);
if (v___x_924_ == 0)
{
lean_object* v_ks_925_; lean_object* v_vs_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v_ks_925_ = lean_ctor_get(v_newNode_919_, 0);
lean_inc_ref(v_ks_925_);
v_vs_926_ = lean_ctor_get(v_newNode_919_, 1);
lean_inc_ref(v_vs_926_);
lean_dec_ref(v_newNode_919_);
v___x_927_ = lean_unsigned_to_nat(0u);
v___x_928_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0);
v___x_929_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_x_861_, v_ks_925_, v_vs_926_, v___x_927_, v___x_928_);
lean_dec_ref(v_vs_926_);
lean_dec_ref(v_ks_925_);
return v___x_929_;
}
else
{
return v_newNode_919_;
}
}
else
{
return v_newNode_919_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_859_ = stack[0].m_obj;
size_t v_x_860_ = stack[1].m_num;
size_t v_x_861_ = stack[2].m_num;
lean_object* v_x_862_ = stack[3].m_obj;
lean_object* v_x_863_ = stack[4].m_obj;
lean_object* v_res_932_;
v_res_932_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_859_, v_x_860_, v_x_861_, v_x_862_, v_x_863_);
stack->m_obj
 = v_res_932_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(size_t v_depth_933_, lean_object* v_keys_934_, lean_object* v_vals_935_, lean_object* v_i_936_, lean_object* v_entries_937_){
_start:
{
lean_object* v___x_938_; uint8_t v___x_939_; 
v___x_938_ = lean_array_get_size(v_keys_934_);
v___x_939_ = lean_nat_dec_lt(v_i_936_, v___x_938_);
if (v___x_939_ == 0)
{
lean_dec(v_i_936_);
return v_entries_937_;
}
else
{
lean_object* v_k_940_; lean_object* v_v_941_; size_t v___x_942_; size_t v___x_943_; size_t v___x_944_; uint64_t v___x_945_; size_t v_h_946_; size_t v___x_947_; lean_object* v___x_948_; size_t v___x_949_; size_t v___x_950_; size_t v___x_951_; size_t v_h_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v_k_940_ = lean_array_fget_borrowed(v_keys_934_, v_i_936_);
v_v_941_ = lean_array_fget_borrowed(v_vals_935_, v_i_936_);
v___x_942_ = lean_ptr_addr(v_k_940_);
v___x_943_ = ((size_t)3ULL);
v___x_944_ = lean_usize_shift_right(v___x_942_, v___x_943_);
v___x_945_ = lean_usize_to_uint64(v___x_944_);
v_h_946_ = lean_uint64_to_usize(v___x_945_);
v___x_947_ = ((size_t)5ULL);
v___x_948_ = lean_unsigned_to_nat(1u);
v___x_949_ = ((size_t)1ULL);
v___x_950_ = lean_usize_sub(v_depth_933_, v___x_949_);
v___x_951_ = lean_usize_mul(v___x_947_, v___x_950_);
v_h_952_ = lean_usize_shift_right(v_h_946_, v___x_951_);
v___x_953_ = lean_nat_add(v_i_936_, v___x_948_);
lean_dec(v_i_936_);
lean_inc(v_v_941_);
lean_inc(v_k_940_);
v___x_954_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_entries_937_, v_h_952_, v_depth_933_, v_k_940_, v_v_941_);
v_i_936_ = v___x_953_;
v_entries_937_ = v___x_954_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_933_ = stack[0].m_num;
lean_object* v_keys_934_ = stack[1].m_obj;
lean_object* v_vals_935_ = stack[2].m_obj;
lean_object* v_i_936_ = stack[3].m_obj;
lean_object* v_entries_937_ = stack[4].m_obj;
lean_object* v_res_956_;
v_res_956_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_933_, v_keys_934_, v_vals_935_, v_i_936_, v_entries_937_);
stack->m_obj
 = v_res_956_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_957_, lean_object* v_keys_958_, lean_object* v_vals_959_, lean_object* v_i_960_, lean_object* v_entries_961_){
_start:
{
size_t v_depth_boxed_962_; lean_object* v_res_963_; 
v_depth_boxed_962_ = lean_unbox_usize(v_depth_957_);
lean_dec(v_depth_957_);
v_res_963_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_962_, v_keys_958_, v_vals_959_, v_i_960_, v_entries_961_);
lean_dec_ref(v_vals_959_);
lean_dec_ref(v_keys_958_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___boxed(lean_object* v_x_964_, lean_object* v_x_965_, lean_object* v_x_966_, lean_object* v_x_967_, lean_object* v_x_968_){
_start:
{
size_t v_x_6498__boxed_969_; size_t v_x_6499__boxed_970_; lean_object* v_res_971_; 
v_x_6498__boxed_969_ = lean_unbox_usize(v_x_965_);
lean_dec(v_x_965_);
v_x_6499__boxed_970_ = lean_unbox_usize(v_x_966_);
lean_dec(v_x_966_);
v_res_971_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_964_, v_x_6498__boxed_969_, v_x_6499__boxed_970_, v_x_967_, v_x_968_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(lean_object* v_x_972_, lean_object* v_x_973_, lean_object* v_x_974_){
_start:
{
size_t v___x_975_; size_t v___x_976_; size_t v___x_977_; uint64_t v___x_978_; size_t v___x_979_; size_t v___x_980_; lean_object* v___x_981_; 
v___x_975_ = lean_ptr_addr(v_x_973_);
v___x_976_ = ((size_t)3ULL);
v___x_977_ = lean_usize_shift_right(v___x_975_, v___x_976_);
v___x_978_ = lean_usize_to_uint64(v___x_977_);
v___x_979_ = lean_uint64_to_usize(v___x_978_);
v___x_980_ = ((size_t)1ULL);
v___x_981_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_972_, v___x_979_, v___x_980_, v_x_973_, v_x_974_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0(lean_object* v_e_982_, lean_object* v_a_983_, lean_object* v_s_984_){
_start:
{
lean_object* v_rings_985_; lean_object* v_exprToRingId_986_; lean_object* v_semirings_987_; lean_object* v_exprToSemiringId_988_; lean_object* v_ncRings_989_; lean_object* v_exprToNCRingId_990_; lean_object* v_ncSemirings_991_; lean_object* v_exprToNCSemiringId_992_; lean_object* v_steps_993_; uint8_t v_reportedMaxDegreeIssue_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1002_; 
v_rings_985_ = lean_ctor_get(v_s_984_, 0);
v_exprToRingId_986_ = lean_ctor_get(v_s_984_, 1);
v_semirings_987_ = lean_ctor_get(v_s_984_, 2);
v_exprToSemiringId_988_ = lean_ctor_get(v_s_984_, 3);
v_ncRings_989_ = lean_ctor_get(v_s_984_, 4);
v_exprToNCRingId_990_ = lean_ctor_get(v_s_984_, 5);
v_ncSemirings_991_ = lean_ctor_get(v_s_984_, 6);
v_exprToNCSemiringId_992_ = lean_ctor_get(v_s_984_, 7);
v_steps_993_ = lean_ctor_get(v_s_984_, 8);
v_reportedMaxDegreeIssue_994_ = lean_ctor_get_uint8(v_s_984_, sizeof(void*)*9);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_s_984_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_996_ = v_s_984_;
v_isShared_997_ = v_isSharedCheck_1002_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_steps_993_);
lean_inc(v_exprToNCSemiringId_992_);
lean_inc(v_ncSemirings_991_);
lean_inc(v_exprToNCRingId_990_);
lean_inc(v_ncRings_989_);
lean_inc(v_exprToSemiringId_988_);
lean_inc(v_semirings_987_);
lean_inc(v_exprToRingId_986_);
lean_inc(v_rings_985_);
lean_dec(v_s_984_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1002_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_998_; lean_object* v___x_1000_; 
lean_inc(v_a_983_);
v___x_998_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_exprToSemiringId_988_, v_e_982_, v_a_983_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 3, v___x_998_);
v___x_1000_ = v___x_996_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_rings_985_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_exprToRingId_986_);
lean_ctor_set(v_reuseFailAlloc_1001_, 2, v_semirings_987_);
lean_ctor_set(v_reuseFailAlloc_1001_, 3, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1001_, 4, v_ncRings_989_);
lean_ctor_set(v_reuseFailAlloc_1001_, 5, v_exprToNCRingId_990_);
lean_ctor_set(v_reuseFailAlloc_1001_, 6, v_ncSemirings_991_);
lean_ctor_set(v_reuseFailAlloc_1001_, 7, v_exprToNCSemiringId_992_);
lean_ctor_set(v_reuseFailAlloc_1001_, 8, v_steps_993_);
lean_ctor_set_uint8(v_reuseFailAlloc_1001_, sizeof(void*)*9, v_reportedMaxDegreeIssue_994_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0___boxed(lean_object* v_e_1003_, lean_object* v_a_1004_, lean_object* v_s_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0(v_e_1003_, v_a_1004_, v_s_1005_);
lean_dec(v_a_1004_);
return v_res_1006_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__0));
v___x_1009_ = l_Lean_stringToMessageData(v___x_1008_);
return v___x_1009_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(lean_object* v_e_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v___f_1023_; lean_object* v___x_1024_; 
lean_inc(v_a_1011_);
lean_inc_ref(v_e_1010_);
v___f_1023_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1023_, 0, v_e_1010_);
lean_closure_set(v___f_1023_, 1, v_a_1011_);
v___x_1024_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_1010_, v_a_1012_, v_a_1017_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_a_1025_);
lean_dec_ref_known(v___x_1024_, 1);
if (lean_obj_tag(v_a_1025_) == 1)
{
lean_object* v_val_1026_; uint8_t v___x_1027_; 
lean_dec_ref(v___f_1023_);
v_val_1026_ = lean_ctor_get(v_a_1025_, 0);
lean_inc(v_val_1026_);
lean_dec_ref_known(v_a_1025_, 1);
v___x_1027_ = lean_nat_dec_eq(v_val_1026_, v_a_1011_);
lean_dec(v_val_1026_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1028_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1);
v___x_1029_ = l_Lean_indentExpr(v_e_1010_);
v___x_1030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1013_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; uint8_t v_verbose_1033_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1031_, 1);
v_verbose_1033_ = lean_ctor_get_uint8(v_a_1032_, 0);
lean_dec(v_a_1032_);
if (v_verbose_1033_ == 0)
{
lean_dec_ref_known(v___x_1030_, 2);
goto v___jp_1020_;
}
else
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Lean_Meta_Sym_reportIssue(v___x_1030_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_dec_ref_known(v___x_1034_, 1);
goto v___jp_1020_;
}
else
{
return v___x_1034_;
}
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_dec_ref_known(v___x_1030_, 2);
v_a_1035_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_1031_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1031_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
else
{
lean_dec_ref(v_e_1010_);
goto v___jp_1020_;
}
}
else
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
lean_dec(v_a_1025_);
lean_dec_ref(v_e_1010_);
v___x_1043_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1044_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1043_, v___f_1023_, v_a_1012_);
return v___x_1044_;
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_dec_ref(v___f_1023_);
lean_dec_ref(v_e_1010_);
v_a_1045_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1024_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1024_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
v___jp_1020_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = lean_box(0);
v___x_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
return v___x_1022_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1010_ = stack[0].m_obj;
lean_object* v_a_1011_ = stack[1].m_obj;
lean_object* v_a_1012_ = stack[2].m_obj;
lean_object* v_a_1013_ = stack[3].m_obj;
lean_object* v_a_1014_ = stack[4].m_obj;
lean_object* v_a_1015_ = stack[5].m_obj;
lean_object* v_a_1016_ = stack[6].m_obj;
lean_object* v_a_1017_ = stack[7].m_obj;
lean_object* v_a_1018_ = stack[8].m_obj;
lean_object* v_res_1053_;
v_res_1053_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
stack->m_obj
 = v_res_1053_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___boxed(lean_object* v_e_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
lean_dec(v_a_1056_);
lean_dec(v_a_1055_);
return v_res_1064_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(lean_object* v_e_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1065_, v_a_1066_, v_a_1067_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
return v___x_1078_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1065_ = stack[0].m_obj;
lean_object* v_a_1066_ = stack[1].m_obj;
lean_object* v_a_1067_ = stack[2].m_obj;
lean_object* v_a_1068_ = stack[3].m_obj;
lean_object* v_a_1069_ = stack[4].m_obj;
lean_object* v_a_1070_ = stack[5].m_obj;
lean_object* v_a_1071_ = stack[6].m_obj;
lean_object* v_a_1072_ = stack[7].m_obj;
lean_object* v_a_1073_ = stack[8].m_obj;
lean_object* v_a_1074_ = stack[9].m_obj;
lean_object* v_a_1075_ = stack[10].m_obj;
lean_object* v_a_1076_ = stack[11].m_obj;
lean_object* v_res_1079_;
v_res_1079_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(v_e_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
stack->m_obj
 = v_res_1079_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___boxed(lean_object* v_e_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(v_e_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
lean_dec(v_a_1089_);
lean_dec_ref(v_a_1088_);
lean_dec(v_a_1087_);
lean_dec_ref(v_a_1086_);
lean_dec(v_a_1085_);
lean_dec_ref(v_a_1084_);
lean_dec(v_a_1083_);
lean_dec(v_a_1082_);
lean_dec(v_a_1081_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0(lean_object* v_00_u03b2_1094_, lean_object* v_x_1095_, lean_object* v_x_1096_, lean_object* v_x_1097_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_x_1095_, v_x_1096_, v_x_1097_);
return v___x_1098_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(lean_object* v_00_u03b2_1099_, lean_object* v_x_1100_, size_t v_x_1101_, size_t v_x_1102_, lean_object* v_x_1103_, lean_object* v_x_1104_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_1100_, v_x_1101_, v_x_1102_, v_x_1103_, v_x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1100_ = stack[1].m_obj;
size_t v_x_1101_ = stack[2].m_num;
size_t v_x_1102_ = stack[3].m_num;
lean_object* v_x_1103_ = stack[4].m_obj;
lean_object* v_x_1104_ = stack[5].m_obj;
lean_object* v_res_1106_;
v_res_1106_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(lean_box(0), v_x_1100_, v_x_1101_, v_x_1102_, v_x_1103_, v_x_1104_);
stack->m_obj
 = v_res_1106_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1107_, lean_object* v_x_1108_, lean_object* v_x_1109_, lean_object* v_x_1110_, lean_object* v_x_1111_, lean_object* v_x_1112_){
_start:
{
size_t v_x_6935__boxed_1113_; size_t v_x_6936__boxed_1114_; lean_object* v_res_1115_; 
v_x_6935__boxed_1113_ = lean_unbox_usize(v_x_1109_);
lean_dec(v_x_1109_);
v_x_6936__boxed_1114_ = lean_unbox_usize(v_x_1110_);
lean_dec(v_x_1110_);
v_res_1115_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(v_00_u03b2_1107_, v_x_1108_, v_x_6935__boxed_1113_, v_x_6936__boxed_1114_, v_x_1111_, v_x_1112_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1116_, lean_object* v_n_1117_, lean_object* v_k_1118_, lean_object* v_v_1119_){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(v_n_1117_, v_k_1118_, v_v_1119_);
return v___x_1120_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1121_, size_t v_depth_1122_, lean_object* v_keys_1123_, lean_object* v_vals_1124_, lean_object* v_heq_1125_, lean_object* v_i_1126_, lean_object* v_entries_1127_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_1122_, v_keys_1123_, v_vals_1124_, v_i_1126_, v_entries_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1122_ = stack[1].m_num;
lean_object* v_keys_1123_ = stack[2].m_obj;
lean_object* v_vals_1124_ = stack[3].m_obj;
lean_object* v_i_1126_ = stack[5].m_obj;
lean_object* v_entries_1127_ = stack[6].m_obj;
lean_object* v_res_1129_;
v_res_1129_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(lean_box(0), v_depth_1122_, v_keys_1123_, v_vals_1124_, lean_box(0), v_i_1126_, v_entries_1127_);
stack->m_obj
 = v_res_1129_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1130_, lean_object* v_depth_1131_, lean_object* v_keys_1132_, lean_object* v_vals_1133_, lean_object* v_heq_1134_, lean_object* v_i_1135_, lean_object* v_entries_1136_){
_start:
{
size_t v_depth_boxed_1137_; lean_object* v_res_1138_; 
v_depth_boxed_1137_ = lean_unbox_usize(v_depth_1131_);
lean_dec(v_depth_1131_);
v_res_1138_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(v_00_u03b2_1130_, v_depth_boxed_1137_, v_keys_1132_, v_vals_1133_, v_heq_1134_, v_i_1135_, v_entries_1136_);
lean_dec_ref(v_vals_1133_);
lean_dec_ref(v_keys_1132_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1139_, lean_object* v_x_1140_, lean_object* v_x_1141_, lean_object* v_x_1142_, lean_object* v_x_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1140_, v_x_1141_, v_x_1142_, v_x_1143_);
return v___x_1144_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0(lean_object* v_e_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1145_, v___y_1146_, v___y_1147_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
return v___x_1158_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1145_ = stack[0].m_obj;
lean_object* v___y_1146_ = stack[1].m_obj;
lean_object* v___y_1147_ = stack[2].m_obj;
lean_object* v___y_1148_ = stack[3].m_obj;
lean_object* v___y_1149_ = stack[4].m_obj;
lean_object* v___y_1150_ = stack[5].m_obj;
lean_object* v___y_1151_ = stack[6].m_obj;
lean_object* v___y_1152_ = stack[7].m_obj;
lean_object* v___y_1153_ = stack[8].m_obj;
lean_object* v___y_1154_ = stack[9].m_obj;
lean_object* v___y_1155_ = stack[10].m_obj;
lean_object* v___y_1156_ = stack[11].m_obj;
lean_object* v_res_1159_;
v_res_1159_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0(v_e_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
stack->m_obj
 = v_res_1159_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0___boxed(lean_object* v_e_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0(v_e_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec(v___y_1161_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0(lean_object* v_e_1176_, lean_object* v___f_1177_, lean_object* v___f_1178_, lean_object* v_size_1179_, lean_object* v_s_1180_){
_start:
{
lean_object* v_denote_1181_; lean_object* v_vars_1182_; lean_object* v_varMap_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1192_; 
v_denote_1181_ = lean_ctor_get(v_s_1180_, 0);
v_vars_1182_ = lean_ctor_get(v_s_1180_, 1);
v_varMap_1183_ = lean_ctor_get(v_s_1180_, 2);
v_isSharedCheck_1192_ = !lean_is_exclusive(v_s_1180_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1185_ = v_s_1180_;
v_isShared_1186_ = v_isSharedCheck_1192_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_varMap_1183_);
lean_inc(v_vars_1182_);
lean_inc(v_denote_1181_);
lean_dec(v_s_1180_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1192_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; 
lean_inc_ref(v_e_1176_);
v___x_1187_ = l_Lean_PersistentArray_push___redArg(v_vars_1182_, v_e_1176_);
v___x_1188_ = l_Lean_PersistentHashMap_insert___redArg(v___f_1177_, v___f_1178_, v_varMap_1183_, v_e_1176_, v_size_1179_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 2, v___x_1188_);
lean_ctor_set(v___x_1185_, 1, v___x_1187_);
v___x_1190_ = v___x_1185_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_denote_1181_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v___x_1187_);
lean_ctor_set(v_reuseFailAlloc_1191_, 2, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__1(lean_object* v_toPure_1193_, lean_object* v_size_1194_, lean_object* v_____r_1195_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = lean_apply_2(v_toPure_1193_, lean_box(0), v_size_1194_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2(lean_object* v_e_1197_, lean_object* v_inst_1198_, lean_object* v_toBind_1199_, lean_object* v___f_1200_, lean_object* v_____r_1201_){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1202_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1203_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SolverExtension_markTerm___boxed), 14, 3);
lean_closure_set(v___x_1203_, 0, lean_box(0));
lean_closure_set(v___x_1203_, 1, v___x_1202_);
lean_closure_set(v___x_1203_, 2, v_e_1197_);
v___x_1204_ = lean_apply_2(v_inst_1198_, lean_box(0), v___x_1203_);
v___x_1205_ = lean_apply_4(v_toBind_1199_, lean_box(0), lean_box(0), v___x_1204_, v___f_1200_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3(lean_object* v_inst_1206_, lean_object* v_e_1207_, lean_object* v_toBind_1208_, lean_object* v___f_1209_, lean_object* v_____r_1210_){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = lean_apply_1(v_inst_1206_, v_e_1207_);
v___x_1212_ = lean_apply_4(v_toBind_1208_, lean_box(0), lean_box(0), v___x_1211_, v___f_1209_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4(lean_object* v___f_1213_, lean_object* v___f_1214_, lean_object* v_e_1215_, lean_object* v_toPure_1216_, lean_object* v_inst_1217_, lean_object* v_toBind_1218_, lean_object* v_inst_1219_, lean_object* v_modifySemiringState_1220_, lean_object* v_s_1221_){
_start:
{
lean_object* v_vars_1222_; lean_object* v_varMap_1223_; lean_object* v___x_1224_; 
v_vars_1222_ = lean_ctor_get(v_s_1221_, 1);
lean_inc_ref(v_vars_1222_);
v_varMap_1223_ = lean_ctor_get(v_s_1221_, 2);
lean_inc_ref(v_varMap_1223_);
lean_dec_ref(v_s_1221_);
lean_inc_ref(v_e_1215_);
lean_inc_ref(v___f_1214_);
lean_inc_ref(v___f_1213_);
v___x_1224_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_1213_, v___f_1214_, v_varMap_1223_, v_e_1215_);
lean_dec_ref(v_varMap_1223_);
if (lean_obj_tag(v___x_1224_) == 1)
{
lean_object* v_val_1225_; lean_object* v___x_1226_; 
lean_dec_ref(v_vars_1222_);
lean_dec(v_modifySemiringState_1220_);
lean_dec(v_inst_1219_);
lean_dec(v_toBind_1218_);
lean_dec(v_inst_1217_);
lean_dec_ref(v_e_1215_);
lean_dec_ref(v___f_1214_);
lean_dec_ref(v___f_1213_);
v_val_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_val_1225_);
lean_dec_ref_known(v___x_1224_, 1);
v___x_1226_ = lean_apply_2(v_toPure_1216_, lean_box(0), v_val_1225_);
return v___x_1226_;
}
else
{
lean_object* v_size_1227_; lean_object* v___f_1228_; lean_object* v___f_1229_; lean_object* v___f_1230_; lean_object* v___f_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
lean_dec(v___x_1224_);
v_size_1227_ = lean_ctor_get(v_vars_1222_, 2);
lean_inc_n(v_size_1227_, 2);
lean_dec_ref(v_vars_1222_);
lean_inc_ref_n(v_e_1215_, 2);
v___f_1228_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1228_, 0, v_e_1215_);
lean_closure_set(v___f_1228_, 1, v___f_1213_);
lean_closure_set(v___f_1228_, 2, v___f_1214_);
lean_closure_set(v___f_1228_, 3, v_size_1227_);
v___f_1229_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1229_, 0, v_toPure_1216_);
lean_closure_set(v___f_1229_, 1, v_size_1227_);
lean_inc_n(v_toBind_1218_, 2);
v___f_1230_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1230_, 0, v_e_1215_);
lean_closure_set(v___f_1230_, 1, v_inst_1217_);
lean_closure_set(v___f_1230_, 2, v_toBind_1218_);
lean_closure_set(v___f_1230_, 3, v___f_1229_);
v___f_1231_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1231_, 0, v_inst_1219_);
lean_closure_set(v___f_1231_, 1, v_e_1215_);
lean_closure_set(v___f_1231_, 2, v_toBind_1218_);
lean_closure_set(v___f_1231_, 3, v___f_1230_);
v___x_1232_ = lean_apply_1(v_modifySemiringState_1220_, v___f_1228_);
v___x_1233_ = lean_apply_4(v_toBind_1218_, lean_box(0), lean_box(0), v___x_1232_, v___f_1231_);
return v___x_1233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(lean_object* v_inst_1236_, lean_object* v_inst_1237_, lean_object* v_inst_1238_, lean_object* v_inst_1239_, lean_object* v_e_1240_){
_start:
{
lean_object* v_toApplicative_1241_; lean_object* v_toBind_1242_; lean_object* v_getSemiringState_1243_; lean_object* v_modifySemiringState_1244_; lean_object* v_toPure_1245_; lean_object* v___f_1246_; lean_object* v___f_1247_; lean_object* v___f_1248_; lean_object* v___x_1249_; 
v_toApplicative_1241_ = lean_ctor_get(v_inst_1237_, 0);
lean_inc_ref(v_toApplicative_1241_);
v_toBind_1242_ = lean_ctor_get(v_inst_1237_, 1);
lean_inc_n(v_toBind_1242_, 2);
lean_dec_ref(v_inst_1237_);
v_getSemiringState_1243_ = lean_ctor_get(v_inst_1238_, 0);
lean_inc(v_getSemiringState_1243_);
v_modifySemiringState_1244_ = lean_ctor_get(v_inst_1238_, 1);
lean_inc(v_modifySemiringState_1244_);
lean_dec_ref(v_inst_1238_);
v_toPure_1245_ = lean_ctor_get(v_toApplicative_1241_, 1);
lean_inc(v_toPure_1245_);
lean_dec_ref(v_toApplicative_1241_);
v___f_1246_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0));
v___f_1247_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1));
v___f_1248_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4), 9, 8);
lean_closure_set(v___f_1248_, 0, v___f_1246_);
lean_closure_set(v___f_1248_, 1, v___f_1247_);
lean_closure_set(v___f_1248_, 2, v_e_1240_);
lean_closure_set(v___f_1248_, 3, v_toPure_1245_);
lean_closure_set(v___f_1248_, 4, v_inst_1236_);
lean_closure_set(v___f_1248_, 5, v_toBind_1242_);
lean_closure_set(v___f_1248_, 6, v_inst_1239_);
lean_closure_set(v___f_1248_, 7, v_modifySemiringState_1244_);
v___x_1249_ = lean_apply_4(v_toBind_1242_, lean_box(0), lean_box(0), v_getSemiringState_1243_, v___f_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore(lean_object* v_m_1250_, lean_object* v_inst_1251_, lean_object* v_inst_1252_, lean_object* v_inst_1253_, lean_object* v_inst_1254_, lean_object* v_e_1255_){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(v_inst_1251_, v_inst_1252_, v_inst_1253_, v_inst_1254_, v_e_1255_);
return v___x_1256_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0___closed__0));
v___x_1259_ = l_Lean_stringToMessageData(v___x_1258_);
return v___x_1259_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0(lean_object* v___x_1260_, lean_object* v___x_1261_, lean_object* v___f_1262_, lean_object* v___x_1263_, lean_object* v___f_1264_, lean_object* v_e_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_1265_, v___y_1267_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; uint8_t v___x_1280_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref_known(v___x_1278_, 1);
v___x_1280_ = lean_unbox(v_a_1279_);
lean_dec(v_a_1279_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1449__overap_1284_; lean_object* v___x_1285_; 
v___x_1281_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0___closed__1);
lean_inc_ref(v_e_1265_);
v___x_1282_ = l_Lean_indentExpr(v_e_1265_);
v___x_1283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1281_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
lean_inc_ref(v___x_1260_);
v___x_1449__overap_1284_ = l_Lean_throwError___redArg(v___x_1260_, v___x_1261_, v___x_1283_);
lean_inc(v___y_1276_);
lean_inc_ref(v___y_1275_);
lean_inc(v___y_1274_);
lean_inc_ref(v___y_1273_);
lean_inc(v___y_1272_);
lean_inc_ref(v___y_1271_);
lean_inc(v___y_1270_);
lean_inc_ref(v___y_1269_);
lean_inc(v___y_1268_);
lean_inc(v___y_1267_);
lean_inc(v___y_1266_);
v___x_1285_ = lean_apply_12(v___x_1449__overap_1284_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, lean_box(0));
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v___x_1452__overap_1286_; lean_object* v___x_1287_; 
lean_dec_ref_known(v___x_1285_, 1);
v___x_1452__overap_1286_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(v___f_1262_, v___x_1260_, v___x_1263_, v___f_1264_, v_e_1265_);
lean_inc(v___y_1276_);
lean_inc_ref(v___y_1275_);
lean_inc(v___y_1274_);
lean_inc_ref(v___y_1273_);
lean_inc(v___y_1272_);
lean_inc_ref(v___y_1271_);
lean_inc(v___y_1270_);
lean_inc_ref(v___y_1269_);
lean_inc(v___y_1268_);
lean_inc(v___y_1267_);
lean_inc(v___y_1266_);
v___x_1287_ = lean_apply_12(v___x_1452__overap_1286_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, lean_box(0));
return v___x_1287_;
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec_ref(v_e_1265_);
lean_dec_ref(v___f_1264_);
lean_dec_ref(v___x_1263_);
lean_dec(v___f_1262_);
lean_dec_ref(v___x_1260_);
v_a_1288_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1285_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1285_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
else
{
lean_object* v___x_1456__overap_1296_; lean_object* v___x_1297_; 
lean_dec_ref(v___x_1261_);
v___x_1456__overap_1296_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(v___f_1262_, v___x_1260_, v___x_1263_, v___f_1264_, v_e_1265_);
lean_inc(v___y_1276_);
lean_inc_ref(v___y_1275_);
lean_inc(v___y_1274_);
lean_inc_ref(v___y_1273_);
lean_inc(v___y_1272_);
lean_inc_ref(v___y_1271_);
lean_inc(v___y_1270_);
lean_inc_ref(v___y_1269_);
lean_inc(v___y_1268_);
lean_inc(v___y_1267_);
lean_inc(v___y_1266_);
v___x_1297_ = lean_apply_12(v___x_1456__overap_1296_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, lean_box(0));
return v___x_1297_;
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec_ref(v_e_1265_);
lean_dec_ref(v___f_1264_);
lean_dec_ref(v___x_1263_);
lean_dec(v___f_1262_);
lean_dec_ref(v___x_1261_);
lean_dec_ref(v___x_1260_);
v_a_1298_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1278_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1278_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1260_ = stack[0].m_obj;
lean_object* v___x_1261_ = stack[1].m_obj;
lean_object* v___f_1262_ = stack[2].m_obj;
lean_object* v___x_1263_ = stack[3].m_obj;
lean_object* v___f_1264_ = stack[4].m_obj;
lean_object* v_e_1265_ = stack[5].m_obj;
lean_object* v___y_1266_ = stack[6].m_obj;
lean_object* v___y_1267_ = stack[7].m_obj;
lean_object* v___y_1268_ = stack[8].m_obj;
lean_object* v___y_1269_ = stack[9].m_obj;
lean_object* v___y_1270_ = stack[10].m_obj;
lean_object* v___y_1271_ = stack[11].m_obj;
lean_object* v___y_1272_ = stack[12].m_obj;
lean_object* v___y_1273_ = stack[13].m_obj;
lean_object* v___y_1274_ = stack[14].m_obj;
lean_object* v___y_1275_ = stack[15].m_obj;
lean_object* v___y_1276_ = stack[16].m_obj;
lean_object* v_res_1306_;
v_res_1306_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0(v___x_1260_, v___x_1261_, v___f_1262_, v___x_1263_, v___f_1264_, v_e_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
stack->m_obj
 = v_res_1306_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0___boxed(lean_object** _args){
lean_object* v___x_1307_ = _args[0];
lean_object* v___x_1308_ = _args[1];
lean_object* v___f_1309_ = _args[2];
lean_object* v___x_1310_ = _args[3];
lean_object* v___f_1311_ = _args[4];
lean_object* v_e_1312_ = _args[5];
lean_object* v___y_1313_ = _args[6];
lean_object* v___y_1314_ = _args[7];
lean_object* v___y_1315_ = _args[8];
lean_object* v___y_1316_ = _args[9];
lean_object* v___y_1317_ = _args[10];
lean_object* v___y_1318_ = _args[11];
lean_object* v___y_1319_ = _args[12];
lean_object* v___y_1320_ = _args[13];
lean_object* v___y_1321_ = _args[14];
lean_object* v___y_1322_ = _args[15];
lean_object* v___y_1323_ = _args[16];
lean_object* v___y_1324_ = _args[17];
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0(v___x_1307_, v___x_1308_, v___f_1309_, v___x_1310_, v___f_1311_, v_e_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec(v___y_1313_);
return v_res_1325_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__0(void){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l_instMonadEIO___redArg();
return v___x_1326_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__1(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__0);
v___x_1328_ = l_StateRefT_x27_instMonad___redArg(v___x_1327_);
return v___x_1328_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__7(void){
_start:
{
lean_object* v___x_1334_; lean_object* v___f_1335_; 
v___x_1334_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_1335_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1335_, 0, v___x_1334_);
return v___f_1335_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__8(void){
_start:
{
lean_object* v___x_1336_; lean_object* v___f_1337_; 
v___x_1336_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_1337_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1337_, 0, v___x_1336_);
return v___f_1337_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__9(void){
_start:
{
lean_object* v___f_1338_; lean_object* v___f_1339_; lean_object* v___x_1340_; 
v___f_1338_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__8, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__8_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__8);
v___f_1339_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__7, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__7_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__7);
v___x_1340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___f_1339_);
lean_ctor_set(v___x_1340_, 1, v___f_1338_);
return v___x_1340_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__10(void){
_start:
{
lean_object* v___x_1341_; lean_object* v___f_1342_; 
v___x_1341_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__9, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__9_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__9);
v___f_1342_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1342_, 0, v___x_1341_);
return v___f_1342_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__11(void){
_start:
{
lean_object* v___x_1343_; lean_object* v___f_1344_; 
v___x_1343_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__9, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__9_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__9);
v___f_1344_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1344_, 0, v___x_1343_);
return v___f_1344_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__12(void){
_start:
{
lean_object* v___f_1345_; lean_object* v___f_1346_; lean_object* v___x_1347_; 
v___f_1345_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__11, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__11_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__11);
v___f_1346_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__10, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__10_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__10);
v___x_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___f_1346_);
lean_ctor_set(v___x_1347_, 1, v___f_1345_);
return v___x_1347_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__13(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___f_1349_; 
v___x_1348_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__12);
v___f_1349_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1349_, 0, v___x_1348_);
return v___f_1349_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__14(void){
_start:
{
lean_object* v___x_1350_; lean_object* v___f_1351_; 
v___x_1350_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__12);
v___f_1351_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1351_, 0, v___x_1350_);
return v___f_1351_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__15(void){
_start:
{
lean_object* v___f_1352_; lean_object* v___f_1353_; lean_object* v___x_1354_; 
v___f_1352_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__14, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__14_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__14);
v___f_1353_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__13, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__13_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__13);
v___x_1354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___f_1353_);
lean_ctor_set(v___x_1354_, 1, v___f_1352_);
return v___x_1354_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__16(void){
_start:
{
lean_object* v___x_1355_; lean_object* v___f_1356_; 
v___x_1355_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__15, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__15_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__15);
v___f_1356_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1356_, 0, v___x_1355_);
return v___f_1356_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__17(void){
_start:
{
lean_object* v___x_1357_; lean_object* v___f_1358_; 
v___x_1357_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__15, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__15_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__15);
v___f_1358_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1358_, 0, v___x_1357_);
return v___f_1358_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__18(void){
_start:
{
lean_object* v___f_1359_; lean_object* v___f_1360_; lean_object* v___x_1361_; 
v___f_1359_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__17, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__17_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__17);
v___f_1360_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__16, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__16_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__16);
v___x_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___f_1360_);
lean_ctor_set(v___x_1361_, 1, v___f_1359_);
return v___x_1361_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__19(void){
_start:
{
lean_object* v___x_1362_; lean_object* v___f_1363_; 
v___x_1362_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__18, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__18_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__18);
v___f_1363_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1363_, 0, v___x_1362_);
return v___f_1363_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__20(void){
_start:
{
lean_object* v___x_1364_; lean_object* v___f_1365_; 
v___x_1364_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__18, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__18_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__18);
v___f_1365_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1365_, 0, v___x_1364_);
return v___f_1365_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__21(void){
_start:
{
lean_object* v___f_1366_; lean_object* v___f_1367_; lean_object* v___x_1368_; 
v___f_1366_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__20, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__20_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__20);
v___f_1367_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__19, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__19_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__19);
v___x_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___f_1367_);
lean_ctor_set(v___x_1368_, 1, v___f_1366_);
return v___x_1368_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__22(void){
_start:
{
lean_object* v___x_1369_; lean_object* v___f_1370_; 
v___x_1369_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__21, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__21_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__21);
v___f_1370_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1370_, 0, v___x_1369_);
return v___f_1370_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__23(void){
_start:
{
lean_object* v___x_1371_; lean_object* v___f_1372_; 
v___x_1371_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__21, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__21_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__21);
v___f_1372_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1372_, 0, v___x_1371_);
return v___f_1372_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__24(void){
_start:
{
lean_object* v___f_1373_; lean_object* v___f_1374_; lean_object* v___x_1375_; 
v___f_1373_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__23, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__23_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__23);
v___f_1374_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__22, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__22_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__22);
v___x_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___f_1374_);
lean_ctor_set(v___x_1375_, 1, v___f_1373_);
return v___x_1375_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__25(void){
_start:
{
lean_object* v___x_1376_; lean_object* v___f_1377_; 
v___x_1376_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__24, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__24_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__24);
v___f_1377_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1377_, 0, v___x_1376_);
return v___f_1377_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__26(void){
_start:
{
lean_object* v___x_1378_; lean_object* v___f_1379_; 
v___x_1378_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__24, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__24_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__24);
v___f_1379_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1379_, 0, v___x_1378_);
return v___f_1379_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__27(void){
_start:
{
lean_object* v___f_1380_; lean_object* v___f_1381_; lean_object* v___x_1382_; 
v___f_1380_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__26, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__26_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__26);
v___f_1381_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__25, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__25_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__25);
v___x_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___f_1381_);
lean_ctor_set(v___x_1382_, 1, v___f_1380_);
return v___x_1382_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__28(void){
_start:
{
lean_object* v___x_1383_; lean_object* v___f_1384_; 
v___x_1383_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__27, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__27_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__27);
v___f_1384_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1384_, 0, v___x_1383_);
return v___f_1384_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__29(void){
_start:
{
lean_object* v___x_1385_; lean_object* v___f_1386_; 
v___x_1385_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__27, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__27_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__27);
v___f_1386_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1386_, 0, v___x_1385_);
return v___f_1386_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__30(void){
_start:
{
lean_object* v___f_1387_; lean_object* v___f_1388_; lean_object* v___x_1389_; 
v___f_1387_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__29, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__29_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__29);
v___f_1388_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__28, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__28_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__28);
v___x_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1389_, 0, v___f_1388_);
lean_ctor_set(v___x_1389_, 1, v___f_1387_);
return v___x_1389_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__31(void){
_start:
{
lean_object* v___x_1390_; lean_object* v___f_1391_; 
v___x_1390_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__30, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__30_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__30);
v___f_1391_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1391_, 0, v___x_1390_);
return v___f_1391_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__32(void){
_start:
{
lean_object* v___x_1392_; lean_object* v___f_1393_; 
v___x_1392_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__30, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__30_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__30);
v___f_1393_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1393_, 0, v___x_1392_);
return v___f_1393_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__33(void){
_start:
{
lean_object* v___f_1394_; lean_object* v___f_1395_; lean_object* v___x_1396_; 
v___f_1394_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__32, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__32_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__32);
v___f_1395_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__31, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__31_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__31);
v___x_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___f_1395_);
lean_ctor_set(v___x_1396_, 1, v___f_1394_);
return v___x_1396_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__37(void){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1400_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1401_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__36));
v___x_1402_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__35));
v___x_1403_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1402_, v___x_1401_, v___x_1400_);
return v___x_1403_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__38(void){
_start:
{
lean_object* v___x_1404_; lean_object* v___f_1405_; lean_object* v___f_1406_; lean_object* v___x_1407_; 
v___x_1404_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__37, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__37_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__37);
v___f_1405_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6));
v___f_1406_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__34));
v___x_1407_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1406_, v___f_1405_, v___x_1404_);
return v___x_1407_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__39(void){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1408_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__38, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__38_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__38);
v___x_1409_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__36));
v___x_1410_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__35));
v___x_1411_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1410_, v___x_1409_, v___x_1408_);
return v___x_1411_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__40(void){
_start:
{
lean_object* v___x_1412_; lean_object* v___f_1413_; lean_object* v___f_1414_; lean_object* v___x_1415_; 
v___x_1412_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__39, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__39_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__39);
v___f_1413_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6));
v___f_1414_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__34));
v___x_1415_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1414_, v___f_1413_, v___x_1412_);
return v___x_1415_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__41(void){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1416_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__40, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__40_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__40);
v___x_1417_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__36));
v___x_1418_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__35));
v___x_1419_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1418_, v___x_1417_, v___x_1416_);
return v___x_1419_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__42(void){
_start:
{
lean_object* v___x_1420_; lean_object* v___f_1421_; lean_object* v___f_1422_; lean_object* v___x_1423_; 
v___x_1420_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__41, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__41_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__41);
v___f_1421_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6));
v___f_1422_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__34));
v___x_1423_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1422_, v___f_1421_, v___x_1420_);
return v___x_1423_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__43(void){
_start:
{
lean_object* v___x_1424_; lean_object* v___f_1425_; lean_object* v___f_1426_; lean_object* v___x_1427_; 
v___x_1424_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__42, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__42_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__42);
v___f_1425_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6));
v___f_1426_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__34));
v___x_1427_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1426_, v___f_1425_, v___x_1424_);
return v___x_1427_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__44(void){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1428_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__43, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__43_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__43);
v___x_1429_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__36));
v___x_1430_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__35));
v___x_1431_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1430_, v___x_1429_, v___x_1428_);
return v___x_1431_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__45(void){
_start:
{
lean_object* v___x_1432_; lean_object* v___f_1433_; lean_object* v___f_1434_; lean_object* v___x_1435_; 
v___x_1432_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__44, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__44_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__44);
v___f_1433_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6));
v___f_1434_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__34));
v___x_1435_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1434_, v___f_1433_, v___x_1432_);
return v___x_1435_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__48(void){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___f_1442_; 
v___x_1440_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__36));
v___x_1441_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_1442_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1442_, 0, v___x_1441_);
lean_closure_set(v___f_1442_, 1, v___x_1440_);
return v___f_1442_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__49(void){
_start:
{
lean_object* v___f_1443_; lean_object* v___f_1444_; lean_object* v___f_1445_; 
v___f_1443_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6));
v___f_1444_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__48, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__48_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__48);
v___f_1445_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1445_, 0, v___f_1444_);
lean_closure_set(v___f_1445_, 1, v___f_1443_);
return v___f_1445_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__50(void){
_start:
{
lean_object* v___x_1446_; lean_object* v___f_1447_; lean_object* v___f_1448_; 
v___x_1446_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__36));
v___f_1447_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__49, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__49_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__49);
v___f_1448_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1448_, 0, v___f_1447_);
lean_closure_set(v___f_1448_, 1, v___x_1446_);
return v___f_1448_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__51(void){
_start:
{
lean_object* v___f_1449_; lean_object* v___f_1450_; lean_object* v___f_1451_; 
v___f_1449_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6));
v___f_1450_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__50, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__50_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__50);
v___f_1451_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1451_, 0, v___f_1450_);
lean_closure_set(v___f_1451_, 1, v___f_1449_);
return v___f_1451_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__52(void){
_start:
{
lean_object* v___f_1452_; lean_object* v___f_1453_; lean_object* v___f_1454_; 
v___f_1452_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6));
v___f_1453_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__51, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__51_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__51);
v___f_1454_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1454_, 0, v___f_1453_);
lean_closure_set(v___f_1454_, 1, v___f_1452_);
return v___f_1454_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__53(void){
_start:
{
lean_object* v___x_1455_; lean_object* v___f_1456_; lean_object* v___f_1457_; 
v___x_1455_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__36));
v___f_1456_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__52, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__52_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__52);
v___f_1457_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1457_, 0, v___f_1456_);
lean_closure_set(v___f_1457_, 1, v___x_1455_);
return v___f_1457_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__54(void){
_start:
{
lean_object* v___f_1458_; lean_object* v___f_1459_; lean_object* v___f_1460_; 
v___f_1458_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__6));
v___f_1459_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__53, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__53_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__53);
v___f_1460_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1460_, 0, v___f_1459_);
lean_closure_set(v___f_1460_, 1, v___f_1458_);
return v___f_1460_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM(void){
_start:
{
lean_object* v___x_1461_; lean_object* v_toApplicative_1462_; lean_object* v_toFunctor_1463_; lean_object* v_toSeq_1464_; lean_object* v_toSeqLeft_1465_; lean_object* v_toSeqRight_1466_; lean_object* v___f_1467_; lean_object* v___f_1468_; lean_object* v___f_1469_; lean_object* v___f_1470_; lean_object* v___x_1471_; lean_object* v___f_1472_; lean_object* v___f_1473_; lean_object* v___f_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v_toApplicative_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1522_; 
v___x_1461_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__1);
v_toApplicative_1462_ = lean_ctor_get(v___x_1461_, 0);
v_toFunctor_1463_ = lean_ctor_get(v_toApplicative_1462_, 0);
v_toSeq_1464_ = lean_ctor_get(v_toApplicative_1462_, 2);
v_toSeqLeft_1465_ = lean_ctor_get(v_toApplicative_1462_, 3);
v_toSeqRight_1466_ = lean_ctor_get(v_toApplicative_1462_, 4);
v___f_1467_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__2));
v___f_1468_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__3));
lean_inc_ref_n(v_toFunctor_1463_, 2);
v___f_1469_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1469_, 0, v_toFunctor_1463_);
v___f_1470_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1470_, 0, v_toFunctor_1463_);
v___x_1471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___f_1469_);
lean_ctor_set(v___x_1471_, 1, v___f_1470_);
lean_inc(v_toSeqRight_1466_);
v___f_1472_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1472_, 0, v_toSeqRight_1466_);
lean_inc(v_toSeqLeft_1465_);
v___f_1473_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1473_, 0, v_toSeqLeft_1465_);
lean_inc(v_toSeq_1464_);
v___f_1474_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1474_, 0, v_toSeq_1464_);
v___x_1475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1471_);
lean_ctor_set(v___x_1475_, 1, v___f_1467_);
lean_ctor_set(v___x_1475_, 2, v___f_1474_);
lean_ctor_set(v___x_1475_, 3, v___f_1473_);
lean_ctor_set(v___x_1475_, 4, v___f_1472_);
v___x_1476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1475_);
lean_ctor_set(v___x_1476_, 1, v___f_1468_);
v___x_1477_ = l_StateRefT_x27_instMonad___redArg(v___x_1476_);
v_toApplicative_1478_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1522_ == 0)
{
lean_object* v_unused_1523_; 
v_unused_1523_ = lean_ctor_get(v___x_1477_, 1);
lean_dec(v_unused_1523_);
v___x_1480_ = v___x_1477_;
v_isShared_1481_ = v_isSharedCheck_1522_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_toApplicative_1478_);
lean_dec(v___x_1477_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1522_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v_toFunctor_1482_; lean_object* v_toSeq_1483_; lean_object* v_toSeqLeft_1484_; lean_object* v_toSeqRight_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1520_; 
v_toFunctor_1482_ = lean_ctor_get(v_toApplicative_1478_, 0);
v_toSeq_1483_ = lean_ctor_get(v_toApplicative_1478_, 2);
v_toSeqLeft_1484_ = lean_ctor_get(v_toApplicative_1478_, 3);
v_toSeqRight_1485_ = lean_ctor_get(v_toApplicative_1478_, 4);
v_isSharedCheck_1520_ = !lean_is_exclusive(v_toApplicative_1478_);
if (v_isSharedCheck_1520_ == 0)
{
lean_object* v_unused_1521_; 
v_unused_1521_ = lean_ctor_get(v_toApplicative_1478_, 1);
lean_dec(v_unused_1521_);
v___x_1487_ = v_toApplicative_1478_;
v_isShared_1488_ = v_isSharedCheck_1520_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_toSeqRight_1485_);
lean_inc(v_toSeqLeft_1484_);
lean_inc(v_toSeq_1483_);
lean_inc(v_toFunctor_1482_);
lean_dec(v_toApplicative_1478_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1520_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___f_1489_; lean_object* v___f_1490_; lean_object* v___f_1491_; lean_object* v___f_1492_; lean_object* v___x_1493_; lean_object* v___f_1494_; lean_object* v___f_1495_; lean_object* v___f_1496_; lean_object* v___x_1498_; 
v___f_1489_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__4));
v___f_1490_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__5));
lean_inc_ref(v_toFunctor_1482_);
v___f_1491_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1491_, 0, v_toFunctor_1482_);
v___f_1492_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1492_, 0, v_toFunctor_1482_);
v___x_1493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___f_1491_);
lean_ctor_set(v___x_1493_, 1, v___f_1492_);
v___f_1494_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1494_, 0, v_toSeqRight_1485_);
v___f_1495_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1495_, 0, v_toSeqLeft_1484_);
v___f_1496_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1496_, 0, v_toSeq_1483_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 4, v___f_1494_);
lean_ctor_set(v___x_1487_, 3, v___f_1495_);
lean_ctor_set(v___x_1487_, 2, v___f_1496_);
lean_ctor_set(v___x_1487_, 1, v___f_1489_);
lean_ctor_set(v___x_1487_, 0, v___x_1493_);
v___x_1498_ = v___x_1487_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1493_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v___f_1489_);
lean_ctor_set(v_reuseFailAlloc_1519_, 2, v___f_1496_);
lean_ctor_set(v_reuseFailAlloc_1519_, 3, v___f_1495_);
lean_ctor_set(v_reuseFailAlloc_1519_, 4, v___f_1494_);
v___x_1498_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1500_; 
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 1, v___f_1490_);
lean_ctor_set(v___x_1480_, 0, v___x_1498_);
v___x_1500_ = v___x_1480_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v___f_1490_);
v___x_1500_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v_toMonadRef_1511_; lean_object* v___f_1512_; lean_object* v___f_1513_; lean_object* v___f_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___f_1517_; 
v___x_1501_ = l_StateRefT_x27_instMonad___redArg(v___x_1500_);
v___x_1502_ = l_ReaderT_instMonad___redArg(v___x_1501_);
v___x_1503_ = l_StateRefT_x27_instMonad___redArg(v___x_1502_);
v___x_1504_ = l_ReaderT_instMonad___redArg(v___x_1503_);
v___x_1505_ = l_ReaderT_instMonad___redArg(v___x_1504_);
v___x_1506_ = l_StateRefT_x27_instMonad___redArg(v___x_1505_);
v___x_1507_ = l_ReaderT_instMonad___redArg(v___x_1506_);
v___x_1508_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateSemiringM;
v___x_1509_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__33, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__33_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__33);
v___x_1510_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__45, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__45_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__45);
v_toMonadRef_1511_ = lean_ctor_get(v___x_1510_, 0);
v___f_1512_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__47));
v___f_1513_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___closed__0));
v___f_1514_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__54, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__54_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___closed__54);
lean_inc_ref(v___x_1507_);
v___x_1515_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1514_, v___x_1507_);
lean_inc_ref(v_toMonadRef_1511_);
v___x_1516_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1509_);
lean_ctor_set(v___x_1516_, 1, v_toMonadRef_1511_);
lean_ctor_set(v___x_1516_, 2, v___x_1515_);
v___f_1517_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarSemiringM___lam__0___boxed), 18, 5);
lean_closure_set(v___f_1517_, 0, v___x_1507_);
lean_closure_set(v___f_1517_, 1, v___x_1516_);
lean_closure_set(v___f_1517_, 2, v___f_1512_);
lean_closure_set(v___f_1517_, 3, v___x_1508_);
lean_closure_set(v___f_1517_, 4, v___f_1513_);
return v___f_1517_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__1(lean_object* v_a_1524_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_nat_to_int(v_a_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0(lean_object* v___y_1526_, lean_object* v_a_1527_, lean_object* v_s_1528_){
_start:
{
lean_object* v_exp_1529_; lean_object* v_rings_1530_; lean_object* v_semirings_1531_; lean_object* v_ncRings_1532_; lean_object* v_ncSemirings_1533_; lean_object* v_typeClassify_1534_; lean_object* v_orders_1535_; lean_object* v_typeOrderClassify_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
v_exp_1529_ = lean_ctor_get(v_s_1528_, 0);
v_rings_1530_ = lean_ctor_get(v_s_1528_, 1);
v_semirings_1531_ = lean_ctor_get(v_s_1528_, 2);
v_ncRings_1532_ = lean_ctor_get(v_s_1528_, 3);
v_ncSemirings_1533_ = lean_ctor_get(v_s_1528_, 4);
v_typeClassify_1534_ = lean_ctor_get(v_s_1528_, 5);
v_orders_1535_ = lean_ctor_get(v_s_1528_, 6);
v_typeOrderClassify_1536_ = lean_ctor_get(v_s_1528_, 7);
v___x_1537_ = lean_array_get_size(v_semirings_1531_);
v___x_1538_ = lean_nat_dec_lt(v___y_1526_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_dec_ref(v_a_1527_);
return v_s_1528_;
}
else
{
lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1562_; 
lean_inc_ref(v_typeOrderClassify_1536_);
lean_inc_ref(v_orders_1535_);
lean_inc_ref(v_typeClassify_1534_);
lean_inc_ref(v_ncSemirings_1533_);
lean_inc_ref(v_ncRings_1532_);
lean_inc_ref(v_semirings_1531_);
lean_inc_ref(v_rings_1530_);
lean_inc(v_exp_1529_);
v_isSharedCheck_1562_ = !lean_is_exclusive(v_s_1528_);
if (v_isSharedCheck_1562_ == 0)
{
lean_object* v_unused_1563_; lean_object* v_unused_1564_; lean_object* v_unused_1565_; lean_object* v_unused_1566_; lean_object* v_unused_1567_; lean_object* v_unused_1568_; lean_object* v_unused_1569_; lean_object* v_unused_1570_; 
v_unused_1563_ = lean_ctor_get(v_s_1528_, 7);
lean_dec(v_unused_1563_);
v_unused_1564_ = lean_ctor_get(v_s_1528_, 6);
lean_dec(v_unused_1564_);
v_unused_1565_ = lean_ctor_get(v_s_1528_, 5);
lean_dec(v_unused_1565_);
v_unused_1566_ = lean_ctor_get(v_s_1528_, 4);
lean_dec(v_unused_1566_);
v_unused_1567_ = lean_ctor_get(v_s_1528_, 3);
lean_dec(v_unused_1567_);
v_unused_1568_ = lean_ctor_get(v_s_1528_, 2);
lean_dec(v_unused_1568_);
v_unused_1569_ = lean_ctor_get(v_s_1528_, 1);
lean_dec(v_unused_1569_);
v_unused_1570_ = lean_ctor_get(v_s_1528_, 0);
lean_dec(v_unused_1570_);
v___x_1540_ = v_s_1528_;
v_isShared_1541_ = v_isSharedCheck_1562_;
goto v_resetjp_1539_;
}
else
{
lean_dec(v_s_1528_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1562_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v_v_1542_; lean_object* v_toSemiring_1543_; lean_object* v_ringId_1544_; lean_object* v_commSemiringInst_1545_; lean_object* v_addRightCancelInst_x3f_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1560_; 
v_v_1542_ = lean_array_fget(v_semirings_1531_, v___y_1526_);
v_toSemiring_1543_ = lean_ctor_get(v_v_1542_, 0);
v_ringId_1544_ = lean_ctor_get(v_v_1542_, 1);
v_commSemiringInst_1545_ = lean_ctor_get(v_v_1542_, 2);
v_addRightCancelInst_x3f_1546_ = lean_ctor_get(v_v_1542_, 3);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_v_1542_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; 
v_unused_1561_ = lean_ctor_get(v_v_1542_, 4);
lean_dec(v_unused_1561_);
v___x_1548_ = v_v_1542_;
v_isShared_1549_ = v_isSharedCheck_1560_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_addRightCancelInst_x3f_1546_);
lean_inc(v_commSemiringInst_1545_);
lean_inc(v_ringId_1544_);
lean_inc(v_toSemiring_1543_);
lean_dec(v_v_1542_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1560_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1550_; lean_object* v_xs_x27_1551_; lean_object* v___x_1552_; lean_object* v___x_1554_; 
v___x_1550_ = lean_box(0);
v_xs_x27_1551_ = lean_array_fset(v_semirings_1531_, v___y_1526_, v___x_1550_);
v___x_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1552_, 0, v_a_1527_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 4, v___x_1552_);
v___x_1554_ = v___x_1548_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_toSemiring_1543_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_ringId_1544_);
lean_ctor_set(v_reuseFailAlloc_1559_, 2, v_commSemiringInst_1545_);
lean_ctor_set(v_reuseFailAlloc_1559_, 3, v_addRightCancelInst_x3f_1546_);
lean_ctor_set(v_reuseFailAlloc_1559_, 4, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_object* v___x_1555_; lean_object* v___x_1557_; 
v___x_1555_ = lean_array_fset(v_xs_x27_1551_, v___y_1526_, v___x_1554_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 2, v___x_1555_);
v___x_1557_ = v___x_1540_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_exp_1529_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_rings_1530_);
lean_ctor_set(v_reuseFailAlloc_1558_, 2, v___x_1555_);
lean_ctor_set(v_reuseFailAlloc_1558_, 3, v_ncRings_1532_);
lean_ctor_set(v_reuseFailAlloc_1558_, 4, v_ncSemirings_1533_);
lean_ctor_set(v_reuseFailAlloc_1558_, 5, v_typeClassify_1534_);
lean_ctor_set(v_reuseFailAlloc_1558_, 6, v_orders_1535_);
lean_ctor_set(v_reuseFailAlloc_1558_, 7, v_typeOrderClassify_1536_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0___boxed(lean_object* v___y_1571_, lean_object* v_a_1572_, lean_object* v_s_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0(v___y_1571_, v_a_1572_, v_s_1573_);
lean_dec(v___y_1571_);
return v_res_1574_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v___y_1599_; lean_object* v___x_1620_; 
v___x_1620_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1642_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1623_ = v___x_1620_;
v_isShared_1624_ = v_isSharedCheck_1642_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1620_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1642_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v_toQFn_x3f_1625_; 
v_toQFn_x3f_1625_ = lean_ctor_get(v_a_1621_, 4);
if (lean_obj_tag(v_toQFn_x3f_1625_) == 1)
{
lean_object* v_val_1626_; lean_object* v___x_1628_; 
lean_inc_ref(v_toQFn_x3f_1625_);
lean_dec(v_a_1621_);
v_val_1626_ = lean_ctor_get(v_toQFn_x3f_1625_, 0);
lean_inc(v_val_1626_);
lean_dec_ref_known(v_toQFn_x3f_1625_, 1);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 0, v_val_1626_);
v___x_1628_ = v___x_1623_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_val_1626_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
else
{
lean_object* v_toSemiring_1630_; lean_object* v_type_1631_; lean_object* v_u_1632_; lean_object* v_semiringInst_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
lean_del_object(v___x_1623_);
v_toSemiring_1630_ = lean_ctor_get(v_a_1621_, 0);
lean_inc_ref(v_toSemiring_1630_);
lean_dec(v_a_1621_);
v_type_1631_ = lean_ctor_get(v_toSemiring_1630_, 1);
lean_inc_ref(v_type_1631_);
v_u_1632_ = lean_ctor_get(v_toSemiring_1630_, 2);
lean_inc(v_u_1632_);
v_semiringInst_1633_ = lean_ctor_get(v_toSemiring_1630_, 3);
lean_inc_ref(v_semiringInst_1633_);
lean_dec_ref(v_toSemiring_1630_);
v___x_1634_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___closed__5));
v___x_1635_ = lean_box(0);
v___x_1636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1636_, 0, v_u_1632_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = l_Lean_mkConst(v___x_1634_, v___x_1636_);
v___x_1638_ = l_Lean_mkAppB(v___x_1637_, v_type_1631_, v_semiringInst_1633_);
v___x_1639_ = l_Lean_Meta_Sym_canon(v___x_1638_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1641_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
lean_dec_ref_known(v___x_1639_, 1);
v___x_1641_ = l_Lean_Meta_Sym_shareCommon(v_a_1640_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
v___y_1599_ = v___x_1641_;
goto v___jp_1598_;
}
else
{
v___y_1599_ = v___x_1639_;
goto v___jp_1598_;
}
}
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
v_a_1643_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1620_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1620_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
v___jp_1598_:
{
if (lean_obj_tag(v___y_1599_) == 0)
{
lean_object* v_a_1600_; lean_object* v___f_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v_a_1600_ = lean_ctor_get(v___y_1599_, 0);
lean_inc_n(v_a_1600_, 2);
lean_dec_ref_known(v___y_1599_, 1);
lean_inc(v___y_1586_);
v___f_1601_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1601_, 0, v___y_1586_);
lean_closure_set(v___f_1601_, 1, v_a_1600_);
v___x_1602_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_1603_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_1602_, v___f_1601_, v___y_1592_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1610_ == 0)
{
lean_object* v_unused_1611_; 
v_unused_1611_ = lean_ctor_get(v___x_1603_, 0);
lean_dec(v_unused_1611_);
v___x_1605_ = v___x_1603_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_dec(v___x_1603_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 0, v_a_1600_);
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1600_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
lean_dec(v_a_1600_);
v_a_1612_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1603_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1603_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
else
{
return v___y_1599_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1586_ = stack[0].m_obj;
lean_object* v___y_1587_ = stack[1].m_obj;
lean_object* v___y_1588_ = stack[2].m_obj;
lean_object* v___y_1589_ = stack[3].m_obj;
lean_object* v___y_1590_ = stack[4].m_obj;
lean_object* v___y_1591_ = stack[5].m_obj;
lean_object* v___y_1592_ = stack[6].m_obj;
lean_object* v___y_1593_ = stack[7].m_obj;
lean_object* v___y_1594_ = stack[8].m_obj;
lean_object* v___y_1595_ = stack[9].m_obj;
lean_object* v___y_1596_ = stack[10].m_obj;
lean_object* v_res_1651_;
v_res_1651_ = l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
stack->m_obj
 = v_res_1651_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___boxed(lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec(v___y_1653_);
lean_dec(v___y_1652_);
return v_res_1664_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6___closed__0(void){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
return v___x_1665_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6(lean_object* v_msg_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v___x_1679_; lean_object* v___f_1680_; lean_object* v___x_41156__overap_1681_; lean_object* v___x_1682_; 
v___x_1679_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6___closed__0);
v___f_1680_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1680_, 0, v___x_1679_);
v___x_41156__overap_1681_ = lean_panic_fn_borrowed(v___f_1680_, v_msg_1666_);
lean_dec_ref(v___f_1680_);
lean_inc(v___y_1677_);
lean_inc_ref(v___y_1676_);
lean_inc(v___y_1675_);
lean_inc_ref(v___y_1674_);
lean_inc(v___y_1673_);
lean_inc_ref(v___y_1672_);
lean_inc(v___y_1671_);
lean_inc_ref(v___y_1670_);
lean_inc(v___y_1669_);
lean_inc(v___y_1668_);
lean_inc(v___y_1667_);
v___x_1682_ = lean_apply_12(v___x_41156__overap_1681_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, lean_box(0));
return v___x_1682_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1666_ = stack[0].m_obj;
lean_object* v___y_1667_ = stack[1].m_obj;
lean_object* v___y_1668_ = stack[2].m_obj;
lean_object* v___y_1669_ = stack[3].m_obj;
lean_object* v___y_1670_ = stack[4].m_obj;
lean_object* v___y_1671_ = stack[5].m_obj;
lean_object* v___y_1672_ = stack[6].m_obj;
lean_object* v___y_1673_ = stack[7].m_obj;
lean_object* v___y_1674_ = stack[8].m_obj;
lean_object* v___y_1675_ = stack[9].m_obj;
lean_object* v___y_1676_ = stack[10].m_obj;
lean_object* v___y_1677_ = stack[11].m_obj;
lean_object* v_res_1683_;
v_res_1683_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6(v_msg_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
stack->m_obj
 = v_res_1683_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6___boxed(lean_object* v_msg_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6(v_msg_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec(v___y_1685_);
return v_res_1697_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1699_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg___closed__0));
v___x_1700_ = l_Lean_stringToMessageData(v___x_1699_);
return v___x_1700_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg(lean_object* v_type_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v___x_1708_; 
lean_inc_ref(v_type_1701_);
v___x_1708_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1721_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1711_ = v___x_1708_;
v_isShared_1712_ = v_isSharedCheck_1721_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1708_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1721_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
if (lean_obj_tag(v_a_1709_) == 1)
{
lean_object* v_val_1713_; lean_object* v___x_1715_; 
lean_dec_ref(v_type_1701_);
v_val_1713_ = lean_ctor_get(v_a_1709_, 0);
lean_inc(v_val_1713_);
lean_dec_ref_known(v_a_1709_, 1);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 0, v_val_1713_);
v___x_1715_ = v___x_1711_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_val_1713_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
else
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
lean_del_object(v___x_1711_);
lean_dec(v_a_1709_);
v___x_1717_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg___closed__1, &l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg___closed__1_once, _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg___closed__1);
v___x_1718_ = l_Lean_indentExpr(v_type_1701_);
v___x_1719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1717_);
lean_ctor_set(v___x_1719_, 1, v___x_1718_);
v___x_1720_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v___x_1719_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
return v___x_1720_;
}
}
}
else
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
lean_dec_ref(v_type_1701_);
v_a_1722_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1708_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1708_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1701_ = stack[0].m_obj;
lean_object* v___y_1702_ = stack[1].m_obj;
lean_object* v___y_1703_ = stack[2].m_obj;
lean_object* v___y_1704_ = stack[3].m_obj;
lean_object* v___y_1705_ = stack[4].m_obj;
lean_object* v___y_1706_ = stack[5].m_obj;
lean_object* v_res_1730_;
v_res_1730_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg(v_type_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
stack->m_obj
 = v_res_1730_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_type_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg(v_type_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
return v_res_1738_;
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__4(lean_object* v_type_1739_, lean_object* v_u_1740_, lean_object* v_instDeclName_1741_, lean_object* v_declName_1742_, lean_object* v_expectedInst_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1756_ = lean_box(0);
v___x_1757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1757_, 0, v_u_1740_);
lean_ctor_set(v___x_1757_, 1, v___x_1756_);
lean_inc_ref(v___x_1757_);
v___x_1758_ = l_Lean_mkConst(v_instDeclName_1741_, v___x_1757_);
lean_inc_ref(v_type_1739_);
v___x_1759_ = l_Lean_Expr_app___override(v___x_1758_, v_type_1739_);
v___x_1760_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg(v___x_1759_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; lean_object* v___x_1762_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc_n(v_a_1761_, 2);
lean_dec_ref_known(v___x_1760_, 1);
lean_inc(v_declName_1742_);
v___x_1762_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v_declName_1742_, v_a_1761_, v_expectedInst_1743_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
lean_dec_ref_known(v___x_1762_, 1);
v___x_1763_ = l_Lean_mkConst(v_declName_1742_, v___x_1757_);
v___x_1764_ = l_Lean_mkAppB(v___x_1763_, v_type_1739_, v_a_1761_);
v___x_1765_ = l_Lean_Meta_Sym_canon(v___x_1764_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1767_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1766_);
lean_dec_ref_known(v___x_1765_, 1);
v___x_1767_ = l_Lean_Meta_Sym_shareCommon(v_a_1766_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
return v___x_1767_;
}
else
{
return v___x_1765_;
}
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
lean_dec(v_a_1761_);
lean_dec_ref_known(v___x_1757_, 2);
lean_dec(v_declName_1742_);
lean_dec_ref(v_type_1739_);
v_a_1768_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1762_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1762_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1757_, 2);
lean_dec_ref(v_expectedInst_1743_);
lean_dec(v_declName_1742_);
lean_dec_ref(v_type_1739_);
return v___x_1760_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1739_ = stack[0].m_obj;
lean_object* v_u_1740_ = stack[1].m_obj;
lean_object* v_instDeclName_1741_ = stack[2].m_obj;
lean_object* v_declName_1742_ = stack[3].m_obj;
lean_object* v_expectedInst_1743_ = stack[4].m_obj;
lean_object* v___y_1744_ = stack[5].m_obj;
lean_object* v___y_1745_ = stack[6].m_obj;
lean_object* v___y_1746_ = stack[7].m_obj;
lean_object* v___y_1747_ = stack[8].m_obj;
lean_object* v___y_1748_ = stack[9].m_obj;
lean_object* v___y_1749_ = stack[10].m_obj;
lean_object* v___y_1750_ = stack[11].m_obj;
lean_object* v___y_1751_ = stack[12].m_obj;
lean_object* v___y_1752_ = stack[13].m_obj;
lean_object* v___y_1753_ = stack[14].m_obj;
lean_object* v___y_1754_ = stack[15].m_obj;
lean_object* v_res_1776_;
v_res_1776_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__4(v_type_1739_, v_u_1740_, v_instDeclName_1741_, v_declName_1742_, v_expectedInst_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
stack->m_obj
 = v_res_1776_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__4___boxed(lean_object** _args){
lean_object* v_type_1777_ = _args[0];
lean_object* v_u_1778_ = _args[1];
lean_object* v_instDeclName_1779_ = _args[2];
lean_object* v_declName_1780_ = _args[3];
lean_object* v_expectedInst_1781_ = _args[4];
lean_object* v___y_1782_ = _args[5];
lean_object* v___y_1783_ = _args[6];
lean_object* v___y_1784_ = _args[7];
lean_object* v___y_1785_ = _args[8];
lean_object* v___y_1786_ = _args[9];
lean_object* v___y_1787_ = _args[10];
lean_object* v___y_1788_ = _args[11];
lean_object* v___y_1789_ = _args[12];
lean_object* v___y_1790_ = _args[13];
lean_object* v___y_1791_ = _args[14];
lean_object* v___y_1792_ = _args[15];
lean_object* v___y_1793_ = _args[16];
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__4(v_type_1777_, v_u_1778_, v_instDeclName_1779_, v_declName_1780_, v_expectedInst_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec(v___y_1782_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___lam__0(lean_object* v_a_1795_, lean_object* v_s_1796_){
_start:
{
lean_object* v_toRing_1797_; lean_object* v_invFn_x3f_1798_; lean_object* v_divFn_x3f_1799_; lean_object* v_semiringId_x3f_1800_; lean_object* v_commSemiringInst_1801_; lean_object* v_commRingInst_1802_; lean_object* v_noZeroDivInst_x3f_1803_; lean_object* v_fieldInst_x3f_1804_; lean_object* v_powIdentityInst_x3f_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1836_; 
v_toRing_1797_ = lean_ctor_get(v_s_1796_, 0);
v_invFn_x3f_1798_ = lean_ctor_get(v_s_1796_, 1);
v_divFn_x3f_1799_ = lean_ctor_get(v_s_1796_, 2);
v_semiringId_x3f_1800_ = lean_ctor_get(v_s_1796_, 3);
v_commSemiringInst_1801_ = lean_ctor_get(v_s_1796_, 4);
v_commRingInst_1802_ = lean_ctor_get(v_s_1796_, 5);
v_noZeroDivInst_x3f_1803_ = lean_ctor_get(v_s_1796_, 6);
v_fieldInst_x3f_1804_ = lean_ctor_get(v_s_1796_, 7);
v_powIdentityInst_x3f_1805_ = lean_ctor_get(v_s_1796_, 8);
v_isSharedCheck_1836_ = !lean_is_exclusive(v_s_1796_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1807_ = v_s_1796_;
v_isShared_1808_ = v_isSharedCheck_1836_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_powIdentityInst_x3f_1805_);
lean_inc(v_fieldInst_x3f_1804_);
lean_inc(v_noZeroDivInst_x3f_1803_);
lean_inc(v_commRingInst_1802_);
lean_inc(v_commSemiringInst_1801_);
lean_inc(v_semiringId_x3f_1800_);
lean_inc(v_divFn_x3f_1799_);
lean_inc(v_invFn_x3f_1798_);
lean_inc(v_toRing_1797_);
lean_dec(v_s_1796_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1836_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v_id_1809_; lean_object* v_type_1810_; lean_object* v_u_1811_; lean_object* v_ringInst_1812_; lean_object* v_semiringInst_1813_; lean_object* v_charInst_x3f_1814_; lean_object* v_addFn_x3f_1815_; lean_object* v_mulFn_x3f_1816_; lean_object* v_subFn_x3f_1817_; lean_object* v_powFn_x3f_1818_; lean_object* v_intCastFn_x3f_1819_; lean_object* v_natCastFn_x3f_1820_; lean_object* v_natSMulFn_x3f_1821_; lean_object* v_intSMulFn_x3f_1822_; lean_object* v_one_x3f_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1834_; 
v_id_1809_ = lean_ctor_get(v_toRing_1797_, 0);
v_type_1810_ = lean_ctor_get(v_toRing_1797_, 1);
v_u_1811_ = lean_ctor_get(v_toRing_1797_, 2);
v_ringInst_1812_ = lean_ctor_get(v_toRing_1797_, 3);
v_semiringInst_1813_ = lean_ctor_get(v_toRing_1797_, 4);
v_charInst_x3f_1814_ = lean_ctor_get(v_toRing_1797_, 5);
v_addFn_x3f_1815_ = lean_ctor_get(v_toRing_1797_, 6);
v_mulFn_x3f_1816_ = lean_ctor_get(v_toRing_1797_, 7);
v_subFn_x3f_1817_ = lean_ctor_get(v_toRing_1797_, 8);
v_powFn_x3f_1818_ = lean_ctor_get(v_toRing_1797_, 10);
v_intCastFn_x3f_1819_ = lean_ctor_get(v_toRing_1797_, 11);
v_natCastFn_x3f_1820_ = lean_ctor_get(v_toRing_1797_, 12);
v_natSMulFn_x3f_1821_ = lean_ctor_get(v_toRing_1797_, 13);
v_intSMulFn_x3f_1822_ = lean_ctor_get(v_toRing_1797_, 14);
v_one_x3f_1823_ = lean_ctor_get(v_toRing_1797_, 15);
v_isSharedCheck_1834_ = !lean_is_exclusive(v_toRing_1797_);
if (v_isSharedCheck_1834_ == 0)
{
lean_object* v_unused_1835_; 
v_unused_1835_ = lean_ctor_get(v_toRing_1797_, 9);
lean_dec(v_unused_1835_);
v___x_1825_ = v_toRing_1797_;
v_isShared_1826_ = v_isSharedCheck_1834_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_one_x3f_1823_);
lean_inc(v_intSMulFn_x3f_1822_);
lean_inc(v_natSMulFn_x3f_1821_);
lean_inc(v_natCastFn_x3f_1820_);
lean_inc(v_intCastFn_x3f_1819_);
lean_inc(v_powFn_x3f_1818_);
lean_inc(v_subFn_x3f_1817_);
lean_inc(v_mulFn_x3f_1816_);
lean_inc(v_addFn_x3f_1815_);
lean_inc(v_charInst_x3f_1814_);
lean_inc(v_semiringInst_1813_);
lean_inc(v_ringInst_1812_);
lean_inc(v_u_1811_);
lean_inc(v_type_1810_);
lean_inc(v_id_1809_);
lean_dec(v_toRing_1797_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1834_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1827_; lean_object* v___x_1829_; 
v___x_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1827_, 0, v_a_1795_);
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 9, v___x_1827_);
v___x_1829_ = v___x_1825_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_id_1809_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v_type_1810_);
lean_ctor_set(v_reuseFailAlloc_1833_, 2, v_u_1811_);
lean_ctor_set(v_reuseFailAlloc_1833_, 3, v_ringInst_1812_);
lean_ctor_set(v_reuseFailAlloc_1833_, 4, v_semiringInst_1813_);
lean_ctor_set(v_reuseFailAlloc_1833_, 5, v_charInst_x3f_1814_);
lean_ctor_set(v_reuseFailAlloc_1833_, 6, v_addFn_x3f_1815_);
lean_ctor_set(v_reuseFailAlloc_1833_, 7, v_mulFn_x3f_1816_);
lean_ctor_set(v_reuseFailAlloc_1833_, 8, v_subFn_x3f_1817_);
lean_ctor_set(v_reuseFailAlloc_1833_, 9, v___x_1827_);
lean_ctor_set(v_reuseFailAlloc_1833_, 10, v_powFn_x3f_1818_);
lean_ctor_set(v_reuseFailAlloc_1833_, 11, v_intCastFn_x3f_1819_);
lean_ctor_set(v_reuseFailAlloc_1833_, 12, v_natCastFn_x3f_1820_);
lean_ctor_set(v_reuseFailAlloc_1833_, 13, v_natSMulFn_x3f_1821_);
lean_ctor_set(v_reuseFailAlloc_1833_, 14, v_intSMulFn_x3f_1822_);
lean_ctor_set(v_reuseFailAlloc_1833_, 15, v_one_x3f_1823_);
v___x_1829_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
lean_object* v___x_1831_; 
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v___x_1829_);
v___x_1831_ = v___x_1807_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v_invFn_x3f_1798_);
lean_ctor_set(v_reuseFailAlloc_1832_, 2, v_divFn_x3f_1799_);
lean_ctor_set(v_reuseFailAlloc_1832_, 3, v_semiringId_x3f_1800_);
lean_ctor_set(v_reuseFailAlloc_1832_, 4, v_commSemiringInst_1801_);
lean_ctor_set(v_reuseFailAlloc_1832_, 5, v_commRingInst_1802_);
lean_ctor_set(v_reuseFailAlloc_1832_, 6, v_noZeroDivInst_x3f_1803_);
lean_ctor_set(v_reuseFailAlloc_1832_, 7, v_fieldInst_x3f_1804_);
lean_ctor_set(v_reuseFailAlloc_1832_, 8, v_powIdentityInst_x3f_1805_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
}
}
lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1903_; 
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1865_ = v___x_1862_;
v_isShared_1866_ = v_isSharedCheck_1903_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1862_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1903_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v_toRing_1867_; lean_object* v_negFn_x3f_1868_; 
v_toRing_1867_ = lean_ctor_get(v_a_1863_, 0);
lean_inc_ref(v_toRing_1867_);
lean_dec(v_a_1863_);
v_negFn_x3f_1868_ = lean_ctor_get(v_toRing_1867_, 9);
if (lean_obj_tag(v_negFn_x3f_1868_) == 1)
{
lean_object* v_val_1869_; lean_object* v___x_1871_; 
lean_inc_ref(v_negFn_x3f_1868_);
lean_dec_ref(v_toRing_1867_);
v_val_1869_ = lean_ctor_get(v_negFn_x3f_1868_, 0);
lean_inc(v_val_1869_);
lean_dec_ref_known(v_negFn_x3f_1868_, 1);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v_val_1869_);
v___x_1871_ = v___x_1865_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_val_1869_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
else
{
lean_object* v_type_1873_; lean_object* v_u_1874_; lean_object* v_ringInst_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v_expectedInst_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
lean_del_object(v___x_1865_);
v_type_1873_ = lean_ctor_get(v_toRing_1867_, 1);
lean_inc_ref_n(v_type_1873_, 2);
v_u_1874_ = lean_ctor_get(v_toRing_1867_, 2);
lean_inc_n(v_u_1874_, 2);
v_ringInst_1875_ = lean_ctor_get(v_toRing_1867_, 3);
lean_inc_ref(v_ringInst_1875_);
lean_dec_ref(v_toRing_1867_);
v___x_1876_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1));
v___x_1877_ = lean_box(0);
v___x_1878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1878_, 0, v_u_1874_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
v___x_1879_ = l_Lean_mkConst(v___x_1876_, v___x_1878_);
v_expectedInst_1880_ = l_Lean_mkAppB(v___x_1879_, v_type_1873_, v_ringInst_1875_);
v___x_1881_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__3));
v___x_1882_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5));
v___x_1883_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__4(v_type_1873_, v_u_1874_, v___x_1881_, v___x_1882_, v_expectedInst_1880_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v___f_1885_; lean_object* v___x_1886_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc_n(v_a_1884_, 2);
lean_dec_ref_known(v___x_1883_, 1);
v___f_1885_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_1885_, 0, v_a_1884_);
v___x_1886_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_1885_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1893_ == 0)
{
lean_object* v_unused_1894_; 
v_unused_1894_ = lean_ctor_get(v___x_1886_, 0);
lean_dec(v_unused_1894_);
v___x_1888_ = v___x_1886_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_dec(v___x_1886_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v_a_1884_);
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1884_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
lean_dec(v_a_1884_);
v_a_1895_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1886_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1886_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
else
{
return v___x_1883_;
}
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
v_a_1904_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1862_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1862_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1850_ = stack[0].m_obj;
lean_object* v___y_1851_ = stack[1].m_obj;
lean_object* v___y_1852_ = stack[2].m_obj;
lean_object* v___y_1853_ = stack[3].m_obj;
lean_object* v___y_1854_ = stack[4].m_obj;
lean_object* v___y_1855_ = stack[5].m_obj;
lean_object* v___y_1856_ = stack[6].m_obj;
lean_object* v___y_1857_ = stack[7].m_obj;
lean_object* v___y_1858_ = stack[8].m_obj;
lean_object* v___y_1859_ = stack[9].m_obj;
lean_object* v___y_1860_ = stack[10].m_obj;
lean_object* v_res_1912_;
v_res_1912_ = l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
stack->m_obj
 = v_res_1912_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___boxed(lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec(v___y_1914_);
lean_dec(v___y_1913_);
return v_res_1925_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = lean_unsigned_to_nat(0u);
v___x_1934_ = lean_nat_to_int(v___x_1933_);
return v___x_1934_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(lean_object* v_k_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_2015_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_1957_ = v___x_1954_;
v_isShared_1958_ = v_isSharedCheck_2015_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_2015_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v_toRing_1959_; lean_object* v_type_1960_; lean_object* v_u_1961_; lean_object* v_semiringInst_1962_; lean_object* v___x_1963_; lean_object* v_n_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v_ofNatInst_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v_toRing_1959_ = lean_ctor_get(v_a_1955_, 0);
lean_inc_ref(v_toRing_1959_);
lean_dec(v_a_1955_);
v_type_1960_ = lean_ctor_get(v_toRing_1959_, 1);
lean_inc_ref_n(v_type_1960_, 2);
v_u_1961_ = lean_ctor_get(v_toRing_1959_, 2);
lean_inc(v_u_1961_);
v_semiringInst_1962_ = lean_ctor_get(v_toRing_1959_, 4);
lean_inc_ref(v_semiringInst_1962_);
lean_dec_ref(v_toRing_1959_);
v___x_1963_ = lean_nat_abs(v_k_1941_);
v_n_1964_ = l_Lean_mkRawNatLit(v___x_1963_);
v___x_1965_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__1));
v___x_1966_ = lean_box(0);
v___x_1967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1967_, 0, v_u_1961_);
lean_ctor_set(v___x_1967_, 1, v___x_1966_);
lean_inc_ref(v___x_1967_);
v___x_1999_ = l_Lean_mkConst(v___x_1965_, v___x_1967_);
lean_inc_ref(v_n_1964_);
v___x_2000_ = l_Lean_mkAppB(v___x_1999_, v_type_1960_, v_n_1964_);
v___x_2001_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2000_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2002_);
lean_dec_ref_known(v___x_2001_, 1);
if (lean_obj_tag(v_a_2002_) == 1)
{
lean_object* v_val_2003_; 
lean_dec_ref(v_semiringInst_1962_);
v_val_2003_ = lean_ctor_get(v_a_2002_, 0);
lean_inc(v_val_2003_);
lean_dec_ref_known(v_a_2002_, 1);
v_ofNatInst_1969_ = v_val_2003_;
v___y_1970_ = v___y_1942_;
v___y_1971_ = v___y_1943_;
v___y_1972_ = v___y_1944_;
v___y_1973_ = v___y_1945_;
v___y_1974_ = v___y_1946_;
v___y_1975_ = v___y_1947_;
v___y_1976_ = v___y_1948_;
v___y_1977_ = v___y_1949_;
v___y_1978_ = v___y_1950_;
v___y_1979_ = v___y_1951_;
v___y_1980_ = v___y_1952_;
goto v___jp_1968_;
}
else
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
lean_dec(v_a_2002_);
v___x_2004_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__6));
lean_inc_ref(v___x_1967_);
v___x_2005_ = l_Lean_mkConst(v___x_2004_, v___x_1967_);
lean_inc_ref(v_n_1964_);
lean_inc_ref(v_type_1960_);
v___x_2006_ = l_Lean_mkApp3(v___x_2005_, v_type_1960_, v_semiringInst_1962_, v_n_1964_);
v_ofNatInst_1969_ = v___x_2006_;
v___y_1970_ = v___y_1942_;
v___y_1971_ = v___y_1943_;
v___y_1972_ = v___y_1944_;
v___y_1973_ = v___y_1945_;
v___y_1974_ = v___y_1946_;
v___y_1975_ = v___y_1947_;
v___y_1976_ = v___y_1948_;
v___y_1977_ = v___y_1949_;
v___y_1978_ = v___y_1950_;
v___y_1979_ = v___y_1951_;
v___y_1980_ = v___y_1952_;
goto v___jp_1968_;
}
}
else
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
lean_dec_ref_known(v___x_1967_, 2);
lean_dec_ref(v_n_1964_);
lean_dec_ref(v_semiringInst_1962_);
lean_dec_ref(v_type_1960_);
lean_del_object(v___x_1957_);
v_a_2007_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2009_ = v___x_2001_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_2001_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2007_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
v___jp_1968_:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v_e_1983_; lean_object* v___x_1984_; uint8_t v___x_1985_; 
v___x_1981_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3));
v___x_1982_ = l_Lean_mkConst(v___x_1981_, v___x_1967_);
v_e_1983_ = l_Lean_mkApp3(v___x_1982_, v_type_1960_, v_n_1964_, v_ofNatInst_1969_);
v___x_1984_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4, &l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4_once, _init_l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4);
v___x_1985_ = lean_int_dec_lt(v_k_1941_, v___x_1984_);
if (v___x_1985_ == 0)
{
lean_object* v___x_1987_; 
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v_e_1983_);
v___x_1987_ = v___x_1957_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_e_1983_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
else
{
lean_object* v___x_1989_; 
lean_del_object(v___x_1957_);
v___x_1989_ = l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1998_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1992_ = v___x_1989_;
v_isShared_1993_ = v_isSharedCheck_1998_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1989_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1998_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1994_; lean_object* v___x_1996_; 
v___x_1994_ = l_Lean_Expr_app___override(v_a_1990_, v_e_1983_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_1994_);
v___x_1996_ = v___x_1992_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1994_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
else
{
lean_dec_ref(v_e_1983_);
return v___x_1989_;
}
}
}
}
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
v_a_2016_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_1954_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_1954_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1941_ = stack[0].m_obj;
lean_object* v___y_1942_ = stack[1].m_obj;
lean_object* v___y_1943_ = stack[2].m_obj;
lean_object* v___y_1944_ = stack[3].m_obj;
lean_object* v___y_1945_ = stack[4].m_obj;
lean_object* v___y_1946_ = stack[5].m_obj;
lean_object* v___y_1947_ = stack[6].m_obj;
lean_object* v___y_1948_ = stack[7].m_obj;
lean_object* v___y_1949_ = stack[8].m_obj;
lean_object* v___y_1950_ = stack[9].m_obj;
lean_object* v___y_1951_ = stack[10].m_obj;
lean_object* v___y_1952_ = stack[11].m_obj;
lean_object* v_res_2024_;
v_res_2024_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v_k_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
stack->m_obj
 = v_res_2024_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___boxed(lean_object* v_k_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v_k_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec(v_k_2025_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___lam__0(lean_object* v_a_2039_, lean_object* v_s_2040_){
_start:
{
lean_object* v_toRing_2041_; lean_object* v_invFn_x3f_2042_; lean_object* v_divFn_x3f_2043_; lean_object* v_semiringId_x3f_2044_; lean_object* v_commSemiringInst_2045_; lean_object* v_commRingInst_2046_; lean_object* v_noZeroDivInst_x3f_2047_; lean_object* v_fieldInst_x3f_2048_; lean_object* v_powIdentityInst_x3f_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2080_; 
v_toRing_2041_ = lean_ctor_get(v_s_2040_, 0);
v_invFn_x3f_2042_ = lean_ctor_get(v_s_2040_, 1);
v_divFn_x3f_2043_ = lean_ctor_get(v_s_2040_, 2);
v_semiringId_x3f_2044_ = lean_ctor_get(v_s_2040_, 3);
v_commSemiringInst_2045_ = lean_ctor_get(v_s_2040_, 4);
v_commRingInst_2046_ = lean_ctor_get(v_s_2040_, 5);
v_noZeroDivInst_x3f_2047_ = lean_ctor_get(v_s_2040_, 6);
v_fieldInst_x3f_2048_ = lean_ctor_get(v_s_2040_, 7);
v_powIdentityInst_x3f_2049_ = lean_ctor_get(v_s_2040_, 8);
v_isSharedCheck_2080_ = !lean_is_exclusive(v_s_2040_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2051_ = v_s_2040_;
v_isShared_2052_ = v_isSharedCheck_2080_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_powIdentityInst_x3f_2049_);
lean_inc(v_fieldInst_x3f_2048_);
lean_inc(v_noZeroDivInst_x3f_2047_);
lean_inc(v_commRingInst_2046_);
lean_inc(v_commSemiringInst_2045_);
lean_inc(v_semiringId_x3f_2044_);
lean_inc(v_divFn_x3f_2043_);
lean_inc(v_invFn_x3f_2042_);
lean_inc(v_toRing_2041_);
lean_dec(v_s_2040_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2080_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v_id_2053_; lean_object* v_type_2054_; lean_object* v_u_2055_; lean_object* v_ringInst_2056_; lean_object* v_semiringInst_2057_; lean_object* v_charInst_x3f_2058_; lean_object* v_addFn_x3f_2059_; lean_object* v_mulFn_x3f_2060_; lean_object* v_subFn_x3f_2061_; lean_object* v_negFn_x3f_2062_; lean_object* v_intCastFn_x3f_2063_; lean_object* v_natCastFn_x3f_2064_; lean_object* v_natSMulFn_x3f_2065_; lean_object* v_intSMulFn_x3f_2066_; lean_object* v_one_x3f_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2078_; 
v_id_2053_ = lean_ctor_get(v_toRing_2041_, 0);
v_type_2054_ = lean_ctor_get(v_toRing_2041_, 1);
v_u_2055_ = lean_ctor_get(v_toRing_2041_, 2);
v_ringInst_2056_ = lean_ctor_get(v_toRing_2041_, 3);
v_semiringInst_2057_ = lean_ctor_get(v_toRing_2041_, 4);
v_charInst_x3f_2058_ = lean_ctor_get(v_toRing_2041_, 5);
v_addFn_x3f_2059_ = lean_ctor_get(v_toRing_2041_, 6);
v_mulFn_x3f_2060_ = lean_ctor_get(v_toRing_2041_, 7);
v_subFn_x3f_2061_ = lean_ctor_get(v_toRing_2041_, 8);
v_negFn_x3f_2062_ = lean_ctor_get(v_toRing_2041_, 9);
v_intCastFn_x3f_2063_ = lean_ctor_get(v_toRing_2041_, 11);
v_natCastFn_x3f_2064_ = lean_ctor_get(v_toRing_2041_, 12);
v_natSMulFn_x3f_2065_ = lean_ctor_get(v_toRing_2041_, 13);
v_intSMulFn_x3f_2066_ = lean_ctor_get(v_toRing_2041_, 14);
v_one_x3f_2067_ = lean_ctor_get(v_toRing_2041_, 15);
v_isSharedCheck_2078_ = !lean_is_exclusive(v_toRing_2041_);
if (v_isSharedCheck_2078_ == 0)
{
lean_object* v_unused_2079_; 
v_unused_2079_ = lean_ctor_get(v_toRing_2041_, 10);
lean_dec(v_unused_2079_);
v___x_2069_ = v_toRing_2041_;
v_isShared_2070_ = v_isSharedCheck_2078_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_one_x3f_2067_);
lean_inc(v_intSMulFn_x3f_2066_);
lean_inc(v_natSMulFn_x3f_2065_);
lean_inc(v_natCastFn_x3f_2064_);
lean_inc(v_intCastFn_x3f_2063_);
lean_inc(v_negFn_x3f_2062_);
lean_inc(v_subFn_x3f_2061_);
lean_inc(v_mulFn_x3f_2060_);
lean_inc(v_addFn_x3f_2059_);
lean_inc(v_charInst_x3f_2058_);
lean_inc(v_semiringInst_2057_);
lean_inc(v_ringInst_2056_);
lean_inc(v_u_2055_);
lean_inc(v_type_2054_);
lean_inc(v_id_2053_);
lean_dec(v_toRing_2041_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2078_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2071_; lean_object* v___x_2073_; 
v___x_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2071_, 0, v_a_2039_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 10, v___x_2071_);
v___x_2073_ = v___x_2069_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_id_2053_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_type_2054_);
lean_ctor_set(v_reuseFailAlloc_2077_, 2, v_u_2055_);
lean_ctor_set(v_reuseFailAlloc_2077_, 3, v_ringInst_2056_);
lean_ctor_set(v_reuseFailAlloc_2077_, 4, v_semiringInst_2057_);
lean_ctor_set(v_reuseFailAlloc_2077_, 5, v_charInst_x3f_2058_);
lean_ctor_set(v_reuseFailAlloc_2077_, 6, v_addFn_x3f_2059_);
lean_ctor_set(v_reuseFailAlloc_2077_, 7, v_mulFn_x3f_2060_);
lean_ctor_set(v_reuseFailAlloc_2077_, 8, v_subFn_x3f_2061_);
lean_ctor_set(v_reuseFailAlloc_2077_, 9, v_negFn_x3f_2062_);
lean_ctor_set(v_reuseFailAlloc_2077_, 10, v___x_2071_);
lean_ctor_set(v_reuseFailAlloc_2077_, 11, v_intCastFn_x3f_2063_);
lean_ctor_set(v_reuseFailAlloc_2077_, 12, v_natCastFn_x3f_2064_);
lean_ctor_set(v_reuseFailAlloc_2077_, 13, v_natSMulFn_x3f_2065_);
lean_ctor_set(v_reuseFailAlloc_2077_, 14, v_intSMulFn_x3f_2066_);
lean_ctor_set(v_reuseFailAlloc_2077_, 15, v_one_x3f_2067_);
v___x_2073_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
lean_object* v___x_2075_; 
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 0, v___x_2073_);
v___x_2075_ = v___x_2051_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2073_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v_invFn_x3f_2042_);
lean_ctor_set(v_reuseFailAlloc_2076_, 2, v_divFn_x3f_2043_);
lean_ctor_set(v_reuseFailAlloc_2076_, 3, v_semiringId_x3f_2044_);
lean_ctor_set(v_reuseFailAlloc_2076_, 4, v_commSemiringInst_2045_);
lean_ctor_set(v_reuseFailAlloc_2076_, 5, v_commRingInst_2046_);
lean_ctor_set(v_reuseFailAlloc_2076_, 6, v_noZeroDivInst_x3f_2047_);
lean_ctor_set(v_reuseFailAlloc_2076_, 7, v_fieldInst_x3f_2048_);
lean_ctor_set(v_reuseFailAlloc_2076_, 8, v_powIdentityInst_x3f_2049_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__2(void){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = lean_unsigned_to_nat(0u);
v___x_2085_ = l_Lean_Level_ofNat(v___x_2084_);
return v___x_2085_;
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7(lean_object* v_u_2096_, lean_object* v_type_2097_, lean_object* v_semiringInst_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2111_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__1));
v___x_2112_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__2, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__2);
v___x_2113_ = lean_box(0);
lean_inc(v_u_2096_);
v___x_2114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2114_, 0, v_u_2096_);
lean_ctor_set(v___x_2114_, 1, v___x_2113_);
lean_inc_ref(v___x_2114_);
v___x_2115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2112_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
v___x_2116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2116_, 0, v_u_2096_);
lean_ctor_set(v___x_2116_, 1, v___x_2115_);
lean_inc_ref(v___x_2116_);
v___x_2117_ = l_Lean_mkConst(v___x_2111_, v___x_2116_);
v___x_2118_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2097_, 2);
v___x_2119_ = l_Lean_mkApp3(v___x_2117_, v_type_2097_, v___x_2118_, v_type_2097_);
v___x_2120_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg(v___x_2119_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v_inst_x27_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc_n(v_a_2121_, 2);
lean_dec_ref_known(v___x_2120_, 1);
v___x_2122_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__4));
v___x_2123_ = l_Lean_mkConst(v___x_2122_, v___x_2114_);
lean_inc_ref(v_type_2097_);
v_inst_x27_2124_ = l_Lean_mkAppB(v___x_2123_, v_type_2097_, v_semiringInst_2098_);
v___x_2125_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___closed__6));
v___x_2126_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v___x_2125_, v_a_2121_, v_inst_x27_2124_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
lean_dec_ref_known(v___x_2126_, 1);
v___x_2127_ = l_Lean_mkConst(v___x_2125_, v___x_2116_);
lean_inc_ref(v_type_2097_);
v___x_2128_ = l_Lean_mkApp4(v___x_2127_, v_type_2097_, v___x_2118_, v_type_2097_, v_a_2121_);
v___x_2129_ = l_Lean_Meta_Sym_canon(v___x_2128_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2131_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref_known(v___x_2129_, 1);
v___x_2131_ = l_Lean_Meta_Sym_shareCommon(v_a_2130_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
return v___x_2131_;
}
else
{
return v___x_2129_;
}
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
lean_dec(v_a_2121_);
lean_dec_ref_known(v___x_2116_, 2);
lean_dec_ref(v_type_2097_);
v_a_2132_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2126_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2126_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2132_);
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
lean_dec_ref_known(v___x_2116_, 2);
lean_dec_ref_known(v___x_2114_, 2);
lean_dec_ref(v_semiringInst_2098_);
lean_dec_ref(v_type_2097_);
return v___x_2120_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_2096_ = stack[0].m_obj;
lean_object* v_type_2097_ = stack[1].m_obj;
lean_object* v_semiringInst_2098_ = stack[2].m_obj;
lean_object* v___y_2099_ = stack[3].m_obj;
lean_object* v___y_2100_ = stack[4].m_obj;
lean_object* v___y_2101_ = stack[5].m_obj;
lean_object* v___y_2102_ = stack[6].m_obj;
lean_object* v___y_2103_ = stack[7].m_obj;
lean_object* v___y_2104_ = stack[8].m_obj;
lean_object* v___y_2105_ = stack[9].m_obj;
lean_object* v___y_2106_ = stack[10].m_obj;
lean_object* v___y_2107_ = stack[11].m_obj;
lean_object* v___y_2108_ = stack[12].m_obj;
lean_object* v___y_2109_ = stack[13].m_obj;
lean_object* v_res_2140_;
v_res_2140_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7(v_u_2096_, v_type_2097_, v_semiringInst_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
stack->m_obj
 = v_res_2140_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7___boxed(lean_object* v_u_2141_, lean_object* v_type_2142_, lean_object* v_semiringInst_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7(v_u_2141_, v_type_2142_, v_semiringInst_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec(v___y_2145_);
lean_dec(v___y_2144_);
return v_res_2156_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2203_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2172_ = v___x_2169_;
v_isShared_2173_ = v_isSharedCheck_2203_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2169_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2203_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v_toRing_2174_; lean_object* v_powFn_x3f_2175_; 
v_toRing_2174_ = lean_ctor_get(v_a_2170_, 0);
lean_inc_ref(v_toRing_2174_);
lean_dec(v_a_2170_);
v_powFn_x3f_2175_ = lean_ctor_get(v_toRing_2174_, 10);
if (lean_obj_tag(v_powFn_x3f_2175_) == 1)
{
lean_object* v_val_2176_; lean_object* v___x_2178_; 
lean_inc_ref(v_powFn_x3f_2175_);
lean_dec_ref(v_toRing_2174_);
v_val_2176_ = lean_ctor_get(v_powFn_x3f_2175_, 0);
lean_inc(v_val_2176_);
lean_dec_ref_known(v_powFn_x3f_2175_, 1);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 0, v_val_2176_);
v___x_2178_ = v___x_2172_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_val_2176_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
else
{
lean_object* v_type_2180_; lean_object* v_u_2181_; lean_object* v_semiringInst_2182_; lean_object* v___x_2183_; 
lean_del_object(v___x_2172_);
v_type_2180_ = lean_ctor_get(v_toRing_2174_, 1);
lean_inc_ref(v_type_2180_);
v_u_2181_ = lean_ctor_get(v_toRing_2174_, 2);
lean_inc(v_u_2181_);
v_semiringInst_2182_ = lean_ctor_get(v_toRing_2174_, 4);
lean_inc_ref(v_semiringInst_2182_);
lean_dec_ref(v_toRing_2174_);
v___x_2183_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___at___00Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_spec__7(v_u_2181_, v_type_2180_, v_semiringInst_2182_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v___f_2185_; lean_object* v___x_2186_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc_n(v_a_2184_, 2);
lean_dec_ref_known(v___x_2183_, 1);
v___f_2185_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___lam__0), 2, 1);
lean_closure_set(v___f_2185_, 0, v_a_2184_);
v___x_2186_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2185_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2193_ == 0)
{
lean_object* v_unused_2194_; 
v_unused_2194_ = lean_ctor_get(v___x_2186_, 0);
lean_dec(v_unused_2194_);
v___x_2188_ = v___x_2186_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_dec(v___x_2186_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 0, v_a_2184_);
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2184_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
else
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2202_; 
lean_dec(v_a_2184_);
v_a_2195_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2197_ = v___x_2186_;
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2186_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2200_; 
if (v_isShared_2198_ == 0)
{
v___x_2200_ = v___x_2197_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_a_2195_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
else
{
return v___x_2183_;
}
}
}
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
v_a_2204_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2169_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2169_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2157_ = stack[0].m_obj;
lean_object* v___y_2158_ = stack[1].m_obj;
lean_object* v___y_2159_ = stack[2].m_obj;
lean_object* v___y_2160_ = stack[3].m_obj;
lean_object* v___y_2161_ = stack[4].m_obj;
lean_object* v___y_2162_ = stack[5].m_obj;
lean_object* v___y_2163_ = stack[6].m_obj;
lean_object* v___y_2164_ = stack[7].m_obj;
lean_object* v___y_2165_ = stack[8].m_obj;
lean_object* v___y_2166_ = stack[9].m_obj;
lean_object* v___y_2167_ = stack[10].m_obj;
lean_object* v_res_2212_;
v_res_2212_ = l_Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
stack->m_obj
 = v_res_2212_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___boxed(lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec(v___y_2214_);
lean_dec(v___y_2213_);
return v_res_2225_;
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4(lean_object* v_type_2226_, lean_object* v_u_2227_, lean_object* v_instDeclName_2228_, lean_object* v_declName_2229_, lean_object* v_expectedInst_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2243_ = lean_box(0);
lean_inc_n(v_u_2227_, 2);
v___x_2244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2244_, 0, v_u_2227_);
lean_ctor_set(v___x_2244_, 1, v___x_2243_);
v___x_2245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2245_, 0, v_u_2227_);
lean_ctor_set(v___x_2245_, 1, v___x_2244_);
v___x_2246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2246_, 0, v_u_2227_);
lean_ctor_set(v___x_2246_, 1, v___x_2245_);
lean_inc_ref(v___x_2246_);
v___x_2247_ = l_Lean_mkConst(v_instDeclName_2228_, v___x_2246_);
lean_inc_ref_n(v_type_2226_, 3);
v___x_2248_ = l_Lean_mkApp3(v___x_2247_, v_type_2226_, v_type_2226_, v_type_2226_);
v___x_2249_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg(v___x_2248_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_a_2250_; lean_object* v___x_2251_; 
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
lean_inc_n(v_a_2250_, 2);
lean_dec_ref_known(v___x_2249_, 1);
lean_inc(v_declName_2229_);
v___x_2251_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v_declName_2229_, v_a_2250_, v_expectedInst_2230_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
lean_dec_ref_known(v___x_2251_, 1);
v___x_2252_ = l_Lean_mkConst(v_declName_2229_, v___x_2246_);
lean_inc_ref_n(v_type_2226_, 2);
v___x_2253_ = l_Lean_mkApp4(v___x_2252_, v_type_2226_, v_type_2226_, v_type_2226_, v_a_2250_);
v___x_2254_ = l_Lean_Meta_Sym_canon(v___x_2253_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; lean_object* v___x_2256_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
lean_inc(v_a_2255_);
lean_dec_ref_known(v___x_2254_, 1);
v___x_2256_ = l_Lean_Meta_Sym_shareCommon(v_a_2255_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
return v___x_2256_;
}
else
{
return v___x_2254_;
}
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
lean_dec(v_a_2250_);
lean_dec_ref_known(v___x_2246_, 2);
lean_dec(v_declName_2229_);
lean_dec_ref(v_type_2226_);
v_a_2257_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2251_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2251_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
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
else
{
lean_dec_ref_known(v___x_2246_, 2);
lean_dec_ref(v_expectedInst_2230_);
lean_dec(v_declName_2229_);
lean_dec_ref(v_type_2226_);
return v___x_2249_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2226_ = stack[0].m_obj;
lean_object* v_u_2227_ = stack[1].m_obj;
lean_object* v_instDeclName_2228_ = stack[2].m_obj;
lean_object* v_declName_2229_ = stack[3].m_obj;
lean_object* v_expectedInst_2230_ = stack[4].m_obj;
lean_object* v___y_2231_ = stack[5].m_obj;
lean_object* v___y_2232_ = stack[6].m_obj;
lean_object* v___y_2233_ = stack[7].m_obj;
lean_object* v___y_2234_ = stack[8].m_obj;
lean_object* v___y_2235_ = stack[9].m_obj;
lean_object* v___y_2236_ = stack[10].m_obj;
lean_object* v___y_2237_ = stack[11].m_obj;
lean_object* v___y_2238_ = stack[12].m_obj;
lean_object* v___y_2239_ = stack[13].m_obj;
lean_object* v___y_2240_ = stack[14].m_obj;
lean_object* v___y_2241_ = stack[15].m_obj;
lean_object* v_res_2265_;
v_res_2265_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4(v_type_2226_, v_u_2227_, v_instDeclName_2228_, v_declName_2229_, v_expectedInst_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
stack->m_obj
 = v_res_2265_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4___boxed(lean_object** _args){
lean_object* v_type_2266_ = _args[0];
lean_object* v_u_2267_ = _args[1];
lean_object* v_instDeclName_2268_ = _args[2];
lean_object* v_declName_2269_ = _args[3];
lean_object* v_expectedInst_2270_ = _args[4];
lean_object* v___y_2271_ = _args[5];
lean_object* v___y_2272_ = _args[6];
lean_object* v___y_2273_ = _args[7];
lean_object* v___y_2274_ = _args[8];
lean_object* v___y_2275_ = _args[9];
lean_object* v___y_2276_ = _args[10];
lean_object* v___y_2277_ = _args[11];
lean_object* v___y_2278_ = _args[12];
lean_object* v___y_2279_ = _args[13];
lean_object* v___y_2280_ = _args[14];
lean_object* v___y_2281_ = _args[15];
lean_object* v___y_2282_ = _args[16];
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4(v_type_2266_, v_u_2267_, v_instDeclName_2268_, v_declName_2269_, v_expectedInst_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec(v___y_2271_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0(lean_object* v_a_2284_, lean_object* v_s_2285_){
_start:
{
lean_object* v_toRing_2286_; lean_object* v_invFn_x3f_2287_; lean_object* v_divFn_x3f_2288_; lean_object* v_semiringId_x3f_2289_; lean_object* v_commSemiringInst_2290_; lean_object* v_commRingInst_2291_; lean_object* v_noZeroDivInst_x3f_2292_; lean_object* v_fieldInst_x3f_2293_; lean_object* v_powIdentityInst_x3f_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2325_; 
v_toRing_2286_ = lean_ctor_get(v_s_2285_, 0);
v_invFn_x3f_2287_ = lean_ctor_get(v_s_2285_, 1);
v_divFn_x3f_2288_ = lean_ctor_get(v_s_2285_, 2);
v_semiringId_x3f_2289_ = lean_ctor_get(v_s_2285_, 3);
v_commSemiringInst_2290_ = lean_ctor_get(v_s_2285_, 4);
v_commRingInst_2291_ = lean_ctor_get(v_s_2285_, 5);
v_noZeroDivInst_x3f_2292_ = lean_ctor_get(v_s_2285_, 6);
v_fieldInst_x3f_2293_ = lean_ctor_get(v_s_2285_, 7);
v_powIdentityInst_x3f_2294_ = lean_ctor_get(v_s_2285_, 8);
v_isSharedCheck_2325_ = !lean_is_exclusive(v_s_2285_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2296_ = v_s_2285_;
v_isShared_2297_ = v_isSharedCheck_2325_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_powIdentityInst_x3f_2294_);
lean_inc(v_fieldInst_x3f_2293_);
lean_inc(v_noZeroDivInst_x3f_2292_);
lean_inc(v_commRingInst_2291_);
lean_inc(v_commSemiringInst_2290_);
lean_inc(v_semiringId_x3f_2289_);
lean_inc(v_divFn_x3f_2288_);
lean_inc(v_invFn_x3f_2287_);
lean_inc(v_toRing_2286_);
lean_dec(v_s_2285_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2325_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v_id_2298_; lean_object* v_type_2299_; lean_object* v_u_2300_; lean_object* v_ringInst_2301_; lean_object* v_semiringInst_2302_; lean_object* v_charInst_x3f_2303_; lean_object* v_mulFn_x3f_2304_; lean_object* v_subFn_x3f_2305_; lean_object* v_negFn_x3f_2306_; lean_object* v_powFn_x3f_2307_; lean_object* v_intCastFn_x3f_2308_; lean_object* v_natCastFn_x3f_2309_; lean_object* v_natSMulFn_x3f_2310_; lean_object* v_intSMulFn_x3f_2311_; lean_object* v_one_x3f_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2323_; 
v_id_2298_ = lean_ctor_get(v_toRing_2286_, 0);
v_type_2299_ = lean_ctor_get(v_toRing_2286_, 1);
v_u_2300_ = lean_ctor_get(v_toRing_2286_, 2);
v_ringInst_2301_ = lean_ctor_get(v_toRing_2286_, 3);
v_semiringInst_2302_ = lean_ctor_get(v_toRing_2286_, 4);
v_charInst_x3f_2303_ = lean_ctor_get(v_toRing_2286_, 5);
v_mulFn_x3f_2304_ = lean_ctor_get(v_toRing_2286_, 7);
v_subFn_x3f_2305_ = lean_ctor_get(v_toRing_2286_, 8);
v_negFn_x3f_2306_ = lean_ctor_get(v_toRing_2286_, 9);
v_powFn_x3f_2307_ = lean_ctor_get(v_toRing_2286_, 10);
v_intCastFn_x3f_2308_ = lean_ctor_get(v_toRing_2286_, 11);
v_natCastFn_x3f_2309_ = lean_ctor_get(v_toRing_2286_, 12);
v_natSMulFn_x3f_2310_ = lean_ctor_get(v_toRing_2286_, 13);
v_intSMulFn_x3f_2311_ = lean_ctor_get(v_toRing_2286_, 14);
v_one_x3f_2312_ = lean_ctor_get(v_toRing_2286_, 15);
v_isSharedCheck_2323_ = !lean_is_exclusive(v_toRing_2286_);
if (v_isSharedCheck_2323_ == 0)
{
lean_object* v_unused_2324_; 
v_unused_2324_ = lean_ctor_get(v_toRing_2286_, 6);
lean_dec(v_unused_2324_);
v___x_2314_ = v_toRing_2286_;
v_isShared_2315_ = v_isSharedCheck_2323_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_one_x3f_2312_);
lean_inc(v_intSMulFn_x3f_2311_);
lean_inc(v_natSMulFn_x3f_2310_);
lean_inc(v_natCastFn_x3f_2309_);
lean_inc(v_intCastFn_x3f_2308_);
lean_inc(v_powFn_x3f_2307_);
lean_inc(v_negFn_x3f_2306_);
lean_inc(v_subFn_x3f_2305_);
lean_inc(v_mulFn_x3f_2304_);
lean_inc(v_charInst_x3f_2303_);
lean_inc(v_semiringInst_2302_);
lean_inc(v_ringInst_2301_);
lean_inc(v_u_2300_);
lean_inc(v_type_2299_);
lean_inc(v_id_2298_);
lean_dec(v_toRing_2286_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2323_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2316_; lean_object* v___x_2318_; 
v___x_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2316_, 0, v_a_2284_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 6, v___x_2316_);
v___x_2318_ = v___x_2314_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_id_2298_);
lean_ctor_set(v_reuseFailAlloc_2322_, 1, v_type_2299_);
lean_ctor_set(v_reuseFailAlloc_2322_, 2, v_u_2300_);
lean_ctor_set(v_reuseFailAlloc_2322_, 3, v_ringInst_2301_);
lean_ctor_set(v_reuseFailAlloc_2322_, 4, v_semiringInst_2302_);
lean_ctor_set(v_reuseFailAlloc_2322_, 5, v_charInst_x3f_2303_);
lean_ctor_set(v_reuseFailAlloc_2322_, 6, v___x_2316_);
lean_ctor_set(v_reuseFailAlloc_2322_, 7, v_mulFn_x3f_2304_);
lean_ctor_set(v_reuseFailAlloc_2322_, 8, v_subFn_x3f_2305_);
lean_ctor_set(v_reuseFailAlloc_2322_, 9, v_negFn_x3f_2306_);
lean_ctor_set(v_reuseFailAlloc_2322_, 10, v_powFn_x3f_2307_);
lean_ctor_set(v_reuseFailAlloc_2322_, 11, v_intCastFn_x3f_2308_);
lean_ctor_set(v_reuseFailAlloc_2322_, 12, v_natCastFn_x3f_2309_);
lean_ctor_set(v_reuseFailAlloc_2322_, 13, v_natSMulFn_x3f_2310_);
lean_ctor_set(v_reuseFailAlloc_2322_, 14, v_intSMulFn_x3f_2311_);
lean_ctor_set(v_reuseFailAlloc_2322_, 15, v_one_x3f_2312_);
v___x_2318_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
lean_object* v___x_2320_; 
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v___x_2318_);
v___x_2320_ = v___x_2296_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v___x_2318_);
lean_ctor_set(v_reuseFailAlloc_2321_, 1, v_invFn_x3f_2287_);
lean_ctor_set(v_reuseFailAlloc_2321_, 2, v_divFn_x3f_2288_);
lean_ctor_set(v_reuseFailAlloc_2321_, 3, v_semiringId_x3f_2289_);
lean_ctor_set(v_reuseFailAlloc_2321_, 4, v_commSemiringInst_2290_);
lean_ctor_set(v_reuseFailAlloc_2321_, 5, v_commRingInst_2291_);
lean_ctor_set(v_reuseFailAlloc_2321_, 6, v_noZeroDivInst_x3f_2292_);
lean_ctor_set(v_reuseFailAlloc_2321_, 7, v_fieldInst_x3f_2293_);
lean_ctor_set(v_reuseFailAlloc_2321_, 8, v_powIdentityInst_x3f_2294_);
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
lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v___x_2354_; 
v___x_2354_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2398_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2357_ = v___x_2354_;
v_isShared_2358_ = v_isSharedCheck_2398_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2354_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2398_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v_toRing_2359_; lean_object* v_addFn_x3f_2360_; 
v_toRing_2359_ = lean_ctor_get(v_a_2355_, 0);
lean_inc_ref(v_toRing_2359_);
lean_dec(v_a_2355_);
v_addFn_x3f_2360_ = lean_ctor_get(v_toRing_2359_, 6);
if (lean_obj_tag(v_addFn_x3f_2360_) == 1)
{
lean_object* v_val_2361_; lean_object* v___x_2363_; 
lean_inc_ref(v_addFn_x3f_2360_);
lean_dec_ref(v_toRing_2359_);
v_val_2361_ = lean_ctor_get(v_addFn_x3f_2360_, 0);
lean_inc(v_val_2361_);
lean_dec_ref_known(v_addFn_x3f_2360_, 1);
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 0, v_val_2361_);
v___x_2363_ = v___x_2357_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_val_2361_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
else
{
lean_object* v_type_2365_; lean_object* v_u_2366_; lean_object* v_semiringInst_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v_expectedInst_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
lean_del_object(v___x_2357_);
v_type_2365_ = lean_ctor_get(v_toRing_2359_, 1);
lean_inc_ref_n(v_type_2365_, 3);
v_u_2366_ = lean_ctor_get(v_toRing_2359_, 2);
lean_inc_n(v_u_2366_, 2);
v_semiringInst_2367_ = lean_ctor_get(v_toRing_2359_, 4);
lean_inc_ref(v_semiringInst_2367_);
lean_dec_ref(v_toRing_2359_);
v___x_2368_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__1));
v___x_2369_ = lean_box(0);
v___x_2370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2370_, 0, v_u_2366_);
lean_ctor_set(v___x_2370_, 1, v___x_2369_);
lean_inc_ref(v___x_2370_);
v___x_2371_ = l_Lean_mkConst(v___x_2368_, v___x_2370_);
v___x_2372_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__3));
v___x_2373_ = l_Lean_mkConst(v___x_2372_, v___x_2370_);
v___x_2374_ = l_Lean_mkAppB(v___x_2373_, v_type_2365_, v_semiringInst_2367_);
v_expectedInst_2375_ = l_Lean_mkAppB(v___x_2371_, v_type_2365_, v___x_2374_);
v___x_2376_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__5));
v___x_2377_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___closed__7));
v___x_2378_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4(v_type_2365_, v_u_2366_, v___x_2376_, v___x_2377_, v_expectedInst_2375_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; lean_object* v___f_2380_; lean_object* v___x_2381_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc_n(v_a_2379_, 2);
lean_dec_ref_known(v___x_2378_, 1);
v___f_2380_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_2380_, 0, v_a_2379_);
v___x_2381_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2380_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2388_ == 0)
{
lean_object* v_unused_2389_; 
v_unused_2389_ = lean_ctor_get(v___x_2381_, 0);
lean_dec(v_unused_2389_);
v___x_2383_ = v___x_2381_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_dec(v___x_2381_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 0, v_a_2379_);
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2379_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
lean_dec(v_a_2379_);
v_a_2390_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2381_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2381_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2390_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
else
{
return v___x_2378_;
}
}
}
}
else
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
v_a_2399_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2354_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2354_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2402_ == 0)
{
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2399_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2342_ = stack[0].m_obj;
lean_object* v___y_2343_ = stack[1].m_obj;
lean_object* v___y_2344_ = stack[2].m_obj;
lean_object* v___y_2345_ = stack[3].m_obj;
lean_object* v___y_2346_ = stack[4].m_obj;
lean_object* v___y_2347_ = stack[5].m_obj;
lean_object* v___y_2348_ = stack[6].m_obj;
lean_object* v___y_2349_ = stack[7].m_obj;
lean_object* v___y_2350_ = stack[8].m_obj;
lean_object* v___y_2351_ = stack[9].m_obj;
lean_object* v___y_2352_ = stack[10].m_obj;
lean_object* v_res_2407_;
v_res_2407_ = l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
stack->m_obj
 = v_res_2407_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___boxed(lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec(v___y_2408_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___lam__0(lean_object* v_a_2421_, lean_object* v_s_2422_){
_start:
{
lean_object* v_toRing_2423_; lean_object* v_invFn_x3f_2424_; lean_object* v_divFn_x3f_2425_; lean_object* v_semiringId_x3f_2426_; lean_object* v_commSemiringInst_2427_; lean_object* v_commRingInst_2428_; lean_object* v_noZeroDivInst_x3f_2429_; lean_object* v_fieldInst_x3f_2430_; lean_object* v_powIdentityInst_x3f_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2462_; 
v_toRing_2423_ = lean_ctor_get(v_s_2422_, 0);
v_invFn_x3f_2424_ = lean_ctor_get(v_s_2422_, 1);
v_divFn_x3f_2425_ = lean_ctor_get(v_s_2422_, 2);
v_semiringId_x3f_2426_ = lean_ctor_get(v_s_2422_, 3);
v_commSemiringInst_2427_ = lean_ctor_get(v_s_2422_, 4);
v_commRingInst_2428_ = lean_ctor_get(v_s_2422_, 5);
v_noZeroDivInst_x3f_2429_ = lean_ctor_get(v_s_2422_, 6);
v_fieldInst_x3f_2430_ = lean_ctor_get(v_s_2422_, 7);
v_powIdentityInst_x3f_2431_ = lean_ctor_get(v_s_2422_, 8);
v_isSharedCheck_2462_ = !lean_is_exclusive(v_s_2422_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2433_ = v_s_2422_;
v_isShared_2434_ = v_isSharedCheck_2462_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_powIdentityInst_x3f_2431_);
lean_inc(v_fieldInst_x3f_2430_);
lean_inc(v_noZeroDivInst_x3f_2429_);
lean_inc(v_commRingInst_2428_);
lean_inc(v_commSemiringInst_2427_);
lean_inc(v_semiringId_x3f_2426_);
lean_inc(v_divFn_x3f_2425_);
lean_inc(v_invFn_x3f_2424_);
lean_inc(v_toRing_2423_);
lean_dec(v_s_2422_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2462_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v_id_2435_; lean_object* v_type_2436_; lean_object* v_u_2437_; lean_object* v_ringInst_2438_; lean_object* v_semiringInst_2439_; lean_object* v_charInst_x3f_2440_; lean_object* v_addFn_x3f_2441_; lean_object* v_subFn_x3f_2442_; lean_object* v_negFn_x3f_2443_; lean_object* v_powFn_x3f_2444_; lean_object* v_intCastFn_x3f_2445_; lean_object* v_natCastFn_x3f_2446_; lean_object* v_natSMulFn_x3f_2447_; lean_object* v_intSMulFn_x3f_2448_; lean_object* v_one_x3f_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2460_; 
v_id_2435_ = lean_ctor_get(v_toRing_2423_, 0);
v_type_2436_ = lean_ctor_get(v_toRing_2423_, 1);
v_u_2437_ = lean_ctor_get(v_toRing_2423_, 2);
v_ringInst_2438_ = lean_ctor_get(v_toRing_2423_, 3);
v_semiringInst_2439_ = lean_ctor_get(v_toRing_2423_, 4);
v_charInst_x3f_2440_ = lean_ctor_get(v_toRing_2423_, 5);
v_addFn_x3f_2441_ = lean_ctor_get(v_toRing_2423_, 6);
v_subFn_x3f_2442_ = lean_ctor_get(v_toRing_2423_, 8);
v_negFn_x3f_2443_ = lean_ctor_get(v_toRing_2423_, 9);
v_powFn_x3f_2444_ = lean_ctor_get(v_toRing_2423_, 10);
v_intCastFn_x3f_2445_ = lean_ctor_get(v_toRing_2423_, 11);
v_natCastFn_x3f_2446_ = lean_ctor_get(v_toRing_2423_, 12);
v_natSMulFn_x3f_2447_ = lean_ctor_get(v_toRing_2423_, 13);
v_intSMulFn_x3f_2448_ = lean_ctor_get(v_toRing_2423_, 14);
v_one_x3f_2449_ = lean_ctor_get(v_toRing_2423_, 15);
v_isSharedCheck_2460_ = !lean_is_exclusive(v_toRing_2423_);
if (v_isSharedCheck_2460_ == 0)
{
lean_object* v_unused_2461_; 
v_unused_2461_ = lean_ctor_get(v_toRing_2423_, 7);
lean_dec(v_unused_2461_);
v___x_2451_ = v_toRing_2423_;
v_isShared_2452_ = v_isSharedCheck_2460_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_one_x3f_2449_);
lean_inc(v_intSMulFn_x3f_2448_);
lean_inc(v_natSMulFn_x3f_2447_);
lean_inc(v_natCastFn_x3f_2446_);
lean_inc(v_intCastFn_x3f_2445_);
lean_inc(v_powFn_x3f_2444_);
lean_inc(v_negFn_x3f_2443_);
lean_inc(v_subFn_x3f_2442_);
lean_inc(v_addFn_x3f_2441_);
lean_inc(v_charInst_x3f_2440_);
lean_inc(v_semiringInst_2439_);
lean_inc(v_ringInst_2438_);
lean_inc(v_u_2437_);
lean_inc(v_type_2436_);
lean_inc(v_id_2435_);
lean_dec(v_toRing_2423_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2460_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2453_; lean_object* v___x_2455_; 
v___x_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2453_, 0, v_a_2421_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 7, v___x_2453_);
v___x_2455_ = v___x_2451_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_id_2435_);
lean_ctor_set(v_reuseFailAlloc_2459_, 1, v_type_2436_);
lean_ctor_set(v_reuseFailAlloc_2459_, 2, v_u_2437_);
lean_ctor_set(v_reuseFailAlloc_2459_, 3, v_ringInst_2438_);
lean_ctor_set(v_reuseFailAlloc_2459_, 4, v_semiringInst_2439_);
lean_ctor_set(v_reuseFailAlloc_2459_, 5, v_charInst_x3f_2440_);
lean_ctor_set(v_reuseFailAlloc_2459_, 6, v_addFn_x3f_2441_);
lean_ctor_set(v_reuseFailAlloc_2459_, 7, v___x_2453_);
lean_ctor_set(v_reuseFailAlloc_2459_, 8, v_subFn_x3f_2442_);
lean_ctor_set(v_reuseFailAlloc_2459_, 9, v_negFn_x3f_2443_);
lean_ctor_set(v_reuseFailAlloc_2459_, 10, v_powFn_x3f_2444_);
lean_ctor_set(v_reuseFailAlloc_2459_, 11, v_intCastFn_x3f_2445_);
lean_ctor_set(v_reuseFailAlloc_2459_, 12, v_natCastFn_x3f_2446_);
lean_ctor_set(v_reuseFailAlloc_2459_, 13, v_natSMulFn_x3f_2447_);
lean_ctor_set(v_reuseFailAlloc_2459_, 14, v_intSMulFn_x3f_2448_);
lean_ctor_set(v_reuseFailAlloc_2459_, 15, v_one_x3f_2449_);
v___x_2455_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
lean_object* v___x_2457_; 
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 0, v___x_2455_);
v___x_2457_ = v___x_2433_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2455_);
lean_ctor_set(v_reuseFailAlloc_2458_, 1, v_invFn_x3f_2424_);
lean_ctor_set(v_reuseFailAlloc_2458_, 2, v_divFn_x3f_2425_);
lean_ctor_set(v_reuseFailAlloc_2458_, 3, v_semiringId_x3f_2426_);
lean_ctor_set(v_reuseFailAlloc_2458_, 4, v_commSemiringInst_2427_);
lean_ctor_set(v_reuseFailAlloc_2458_, 5, v_commRingInst_2428_);
lean_ctor_set(v_reuseFailAlloc_2458_, 6, v_noZeroDivInst_x3f_2429_);
lean_ctor_set(v_reuseFailAlloc_2458_, 7, v_fieldInst_x3f_2430_);
lean_ctor_set(v_reuseFailAlloc_2458_, 8, v_powIdentityInst_x3f_2431_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
}
}
lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v___x_2491_; 
v___x_2491_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2535_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2494_ = v___x_2491_;
v_isShared_2495_ = v_isSharedCheck_2535_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2491_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2535_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v_toRing_2496_; lean_object* v_mulFn_x3f_2497_; 
v_toRing_2496_ = lean_ctor_get(v_a_2492_, 0);
lean_inc_ref(v_toRing_2496_);
lean_dec(v_a_2492_);
v_mulFn_x3f_2497_ = lean_ctor_get(v_toRing_2496_, 7);
if (lean_obj_tag(v_mulFn_x3f_2497_) == 1)
{
lean_object* v_val_2498_; lean_object* v___x_2500_; 
lean_inc_ref(v_mulFn_x3f_2497_);
lean_dec_ref(v_toRing_2496_);
v_val_2498_ = lean_ctor_get(v_mulFn_x3f_2497_, 0);
lean_inc(v_val_2498_);
lean_dec_ref_known(v_mulFn_x3f_2497_, 1);
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 0, v_val_2498_);
v___x_2500_ = v___x_2494_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_val_2498_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
else
{
lean_object* v_type_2502_; lean_object* v_u_2503_; lean_object* v_semiringInst_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v_expectedInst_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
lean_del_object(v___x_2494_);
v_type_2502_ = lean_ctor_get(v_toRing_2496_, 1);
lean_inc_ref_n(v_type_2502_, 3);
v_u_2503_ = lean_ctor_get(v_toRing_2496_, 2);
lean_inc_n(v_u_2503_, 2);
v_semiringInst_2504_ = lean_ctor_get(v_toRing_2496_, 4);
lean_inc_ref(v_semiringInst_2504_);
lean_dec_ref(v_toRing_2496_);
v___x_2505_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__1));
v___x_2506_ = lean_box(0);
v___x_2507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2507_, 0, v_u_2503_);
lean_ctor_set(v___x_2507_, 1, v___x_2506_);
lean_inc_ref(v___x_2507_);
v___x_2508_ = l_Lean_mkConst(v___x_2505_, v___x_2507_);
v___x_2509_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__3));
v___x_2510_ = l_Lean_mkConst(v___x_2509_, v___x_2507_);
v___x_2511_ = l_Lean_mkAppB(v___x_2510_, v_type_2502_, v_semiringInst_2504_);
v_expectedInst_2512_ = l_Lean_mkAppB(v___x_2508_, v_type_2502_, v___x_2511_);
v___x_2513_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__5));
v___x_2514_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___closed__7));
v___x_2515_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4(v_type_2502_, v_u_2503_, v___x_2513_, v___x_2514_, v_expectedInst_2512_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___f_2517_; lean_object* v___x_2518_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
lean_inc_n(v_a_2516_, 2);
lean_dec_ref_known(v___x_2515_, 1);
v___f_2517_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___lam__0), 2, 1);
lean_closure_set(v___f_2517_, 0, v_a_2516_);
v___x_2518_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2517_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2525_ == 0)
{
lean_object* v_unused_2526_; 
v_unused_2526_ = lean_ctor_get(v___x_2518_, 0);
lean_dec(v_unused_2526_);
v___x_2520_ = v___x_2518_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_dec(v___x_2518_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 0, v_a_2516_);
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2516_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
lean_dec(v_a_2516_);
v_a_2527_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___x_2518_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2518_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
else
{
return v___x_2515_;
}
}
}
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
v_a_2536_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2491_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2491_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2479_ = stack[0].m_obj;
lean_object* v___y_2480_ = stack[1].m_obj;
lean_object* v___y_2481_ = stack[2].m_obj;
lean_object* v___y_2482_ = stack[3].m_obj;
lean_object* v___y_2483_ = stack[4].m_obj;
lean_object* v___y_2484_ = stack[5].m_obj;
lean_object* v___y_2485_ = stack[6].m_obj;
lean_object* v___y_2486_ = stack[7].m_obj;
lean_object* v___y_2487_ = stack[8].m_obj;
lean_object* v___y_2488_ = stack[9].m_obj;
lean_object* v___y_2489_ = stack[10].m_obj;
lean_object* v_res_2544_;
v_res_2544_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
stack->m_obj
 = v_res_2544_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___boxed(lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec(v___y_2545_);
return v_res_2557_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3(void){
_start:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2561_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__2));
v___x_2562_ = lean_unsigned_to_nat(39u);
v___x_2563_ = lean_unsigned_to_nat(131u);
v___x_2564_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__1));
v___x_2565_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__0));
v___x_2566_ = l_mkPanicMessageWithDecl(v___x_2565_, v___x_2564_, v___x_2563_, v___x_2562_, v___x_2561_);
return v___x_2566_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(lean_object* v_gen_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_){
_start:
{
switch(lean_obj_tag(v_a_2568_))
{
case 0:
{
lean_object* v_k_2581_; lean_object* v___x_2582_; 
lean_dec(v_gen_2567_);
v_k_2581_ = lean_ctor_get(v_a_2568_, 0);
lean_inc(v_k_2581_);
lean_dec_ref_known(v_a_2568_, 1);
v___x_2582_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v_k_2581_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
lean_dec(v_k_2581_);
return v___x_2582_;
}
case 1:
{
lean_object* v_k_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
lean_dec(v_gen_2567_);
v_k_2583_ = lean_ctor_get(v_a_2568_, 0);
lean_inc(v_k_2583_);
lean_dec_ref_known(v_a_2568_, 1);
v___x_2584_ = lean_nat_to_int(v_k_2583_);
v___x_2585_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v___x_2584_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
lean_dec(v___x_2584_);
return v___x_2585_;
}
case 3:
{
lean_object* v_i_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v_i_2586_ = lean_ctor_get(v_a_2568_, 0);
lean_inc(v_i_2586_);
lean_dec_ref_known(v_a_2568_, 1);
v___x_2587_ = l_Lean_instInhabitedExpr;
v___x_2588_ = l_Lean_Meta_Sym_Arith_getToQFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2590_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2589_);
lean_dec_ref_known(v___x_2588_, 1);
v___x_2590_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getSemiringState___redArg(v_a_2569_, v_a_2570_, v_a_2578_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; lean_object* v___y_2593_; lean_object* v_vars_2615_; lean_object* v_size_2616_; uint8_t v___x_2617_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_a_2591_);
lean_dec_ref_known(v___x_2590_, 1);
v_vars_2615_ = lean_ctor_get(v_a_2591_, 1);
lean_inc_ref(v_vars_2615_);
lean_dec(v_a_2591_);
v_size_2616_ = lean_ctor_get(v_vars_2615_, 2);
v___x_2617_ = lean_nat_dec_lt(v_i_2586_, v_size_2616_);
if (v___x_2617_ == 0)
{
lean_object* v___x_2618_; 
lean_dec_ref(v_vars_2615_);
lean_dec(v_i_2586_);
v___x_2618_ = l_outOfBounds___redArg(v___x_2587_);
v___y_2593_ = v___x_2618_;
goto v___jp_2592_;
}
else
{
lean_object* v___x_2619_; 
v___x_2619_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2587_, v_vars_2615_, v_i_2586_);
lean_dec(v_i_2586_);
lean_dec_ref(v_vars_2615_);
v___y_2593_ = v___x_2619_;
goto v___jp_2592_;
}
v___jp_2592_:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2594_ = l_Lean_Expr_app___override(v_a_2589_, v___y_2593_);
v___x_2595_ = l_Lean_Meta_Sym_shareCommon(v___x_2594_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc_n(v_a_2596_, 2);
lean_dec_ref_known(v___x_2595_, 1);
v___x_2597_ = lean_box(0);
lean_inc(v_a_2579_);
lean_inc_ref(v_a_2578_);
lean_inc(v_a_2577_);
lean_inc_ref(v_a_2576_);
lean_inc(v_a_2575_);
lean_inc_ref(v_a_2574_);
lean_inc(v_a_2573_);
lean_inc_ref(v_a_2572_);
lean_inc(v_a_2571_);
lean_inc(v_a_2570_);
v___x_2598_ = lean_grind_internalize(v_a_2596_, v_gen_2567_, v___x_2597_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2605_ == 0)
{
lean_object* v_unused_2606_; 
v_unused_2606_ = lean_ctor_get(v___x_2598_, 0);
lean_dec(v_unused_2606_);
v___x_2600_ = v___x_2598_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_dec(v___x_2598_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 0, v_a_2596_);
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2596_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_dec(v_a_2596_);
v_a_2607_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2598_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2598_);
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
else
{
lean_dec(v_gen_2567_);
return v___x_2595_;
}
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_dec(v_a_2589_);
lean_dec(v_i_2586_);
lean_dec(v_gen_2567_);
v_a_2620_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2590_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2590_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
else
{
lean_dec(v_i_2586_);
lean_dec(v_gen_2567_);
return v___x_2588_;
}
}
case 5:
{
lean_object* v_a_2628_; lean_object* v_b_2629_; lean_object* v___x_2630_; 
v_a_2628_ = lean_ctor_get(v_a_2568_, 0);
lean_inc_ref(v_a_2628_);
v_b_2629_ = lean_ctor_get(v_a_2568_, 1);
lean_inc_ref(v_b_2629_);
lean_dec_ref_known(v_a_2568_, 2);
v___x_2630_ = l_Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; lean_object* v___x_2632_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_a_2631_);
lean_dec_ref_known(v___x_2630_, 1);
lean_inc(v_gen_2567_);
v___x_2632_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_gen_2567_, v_a_2628_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_a_2633_; lean_object* v___x_2634_; 
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_a_2633_);
lean_dec_ref_known(v___x_2632_, 1);
v___x_2634_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_gen_2567_, v_b_2629_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2643_; 
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2637_ = v___x_2634_;
v_isShared_2638_ = v_isSharedCheck_2643_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2634_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2643_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2639_; lean_object* v___x_2641_; 
v___x_2639_ = l_Lean_mkAppB(v_a_2631_, v_a_2633_, v_a_2635_);
if (v_isShared_2638_ == 0)
{
lean_ctor_set(v___x_2637_, 0, v___x_2639_);
v___x_2641_ = v___x_2637_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2639_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
else
{
lean_dec(v_a_2633_);
lean_dec(v_a_2631_);
return v___x_2634_;
}
}
else
{
lean_dec(v_a_2631_);
lean_dec_ref(v_b_2629_);
lean_dec(v_gen_2567_);
return v___x_2632_;
}
}
else
{
lean_dec_ref(v_b_2629_);
lean_dec_ref(v_a_2628_);
lean_dec(v_gen_2567_);
return v___x_2630_;
}
}
case 7:
{
lean_object* v_a_2644_; lean_object* v_b_2645_; lean_object* v___x_2646_; 
v_a_2644_ = lean_ctor_get(v_a_2568_, 0);
lean_inc_ref(v_a_2644_);
v_b_2645_ = lean_ctor_get(v_a_2568_, 1);
lean_inc_ref(v_b_2645_);
lean_dec_ref_known(v_a_2568_, 2);
v___x_2646_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v_a_2647_; lean_object* v___x_2648_; 
v_a_2647_ = lean_ctor_get(v___x_2646_, 0);
lean_inc(v_a_2647_);
lean_dec_ref_known(v___x_2646_, 1);
lean_inc(v_gen_2567_);
v___x_2648_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_gen_2567_, v_a_2644_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v___x_2650_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
lean_inc(v_a_2649_);
lean_dec_ref_known(v___x_2648_, 1);
v___x_2650_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_gen_2567_, v_b_2645_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2659_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2653_ = v___x_2650_;
v_isShared_2654_ = v_isSharedCheck_2659_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2650_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2659_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2655_; lean_object* v___x_2657_; 
v___x_2655_ = l_Lean_mkAppB(v_a_2647_, v_a_2649_, v_a_2651_);
if (v_isShared_2654_ == 0)
{
lean_ctor_set(v___x_2653_, 0, v___x_2655_);
v___x_2657_ = v___x_2653_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v___x_2655_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
else
{
lean_dec(v_a_2649_);
lean_dec(v_a_2647_);
return v___x_2650_;
}
}
else
{
lean_dec(v_a_2647_);
lean_dec_ref(v_b_2645_);
lean_dec(v_gen_2567_);
return v___x_2648_;
}
}
else
{
lean_dec_ref(v_b_2645_);
lean_dec_ref(v_a_2644_);
lean_dec(v_gen_2567_);
return v___x_2646_;
}
}
case 8:
{
lean_object* v_a_2660_; lean_object* v_k_2661_; lean_object* v___x_2662_; 
v_a_2660_ = lean_ctor_get(v_a_2568_, 0);
lean_inc_ref(v_a_2660_);
v_k_2661_ = lean_ctor_get(v_a_2568_, 1);
lean_inc(v_k_2661_);
lean_dec_ref_known(v_a_2568_, 2);
v___x_2662_ = l_Lean_Meta_Sym_Arith_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; lean_object* v___x_2664_; 
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_a_2663_);
lean_dec_ref_known(v___x_2662_, 1);
v___x_2664_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_gen_2567_, v_a_2660_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2674_; 
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2667_ = v___x_2664_;
v_isShared_2668_ = v_isSharedCheck_2674_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2664_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2674_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2672_; 
v___x_2669_ = l_Lean_mkNatLit(v_k_2661_);
v___x_2670_ = l_Lean_mkAppB(v_a_2663_, v_a_2665_, v___x_2669_);
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 0, v___x_2670_);
v___x_2672_ = v___x_2667_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2670_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
else
{
lean_dec(v_a_2663_);
lean_dec(v_k_2661_);
return v___x_2664_;
}
}
else
{
lean_dec(v_k_2661_);
lean_dec_ref(v_a_2660_);
lean_dec(v_gen_2567_);
return v___x_2662_;
}
}
default: 
{
lean_object* v___x_2675_; lean_object* v___x_2676_; 
lean_dec_ref(v_a_2568_);
lean_dec(v_gen_2567_);
v___x_2675_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3);
v___x_2676_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__6(v___x_2675_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
return v___x_2676_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_gen_2567_ = stack[0].m_obj;
lean_object* v_a_2568_ = stack[1].m_obj;
lean_object* v_a_2569_ = stack[2].m_obj;
lean_object* v_a_2570_ = stack[3].m_obj;
lean_object* v_a_2571_ = stack[4].m_obj;
lean_object* v_a_2572_ = stack[5].m_obj;
lean_object* v_a_2573_ = stack[6].m_obj;
lean_object* v_a_2574_ = stack[7].m_obj;
lean_object* v_a_2575_ = stack[8].m_obj;
lean_object* v_a_2576_ = stack[9].m_obj;
lean_object* v_a_2577_ = stack[10].m_obj;
lean_object* v_a_2578_ = stack[11].m_obj;
lean_object* v_a_2579_ = stack[12].m_obj;
lean_object* v_res_2677_;
v_res_2677_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_gen_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
stack->m_obj
 = v_res_2677_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___boxed(lean_object* v_gen_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_gen_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_);
lean_dec(v_a_2690_);
lean_dec_ref(v_a_2689_);
lean_dec(v_a_2688_);
lean_dec_ref(v_a_2687_);
lean_dec(v_a_2686_);
lean_dec_ref(v_a_2685_);
lean_dec(v_a_2684_);
lean_dec_ref(v_a_2683_);
lean_dec(v_a_2682_);
lean_dec(v_a_2681_);
lean_dec(v_a_2680_);
return v_res_2692_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7(lean_object* v_type_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
lean_object* v___x_2706_; 
v___x_2706_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___redArg(v_type_2693_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
return v___x_2706_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2693_ = stack[0].m_obj;
lean_object* v___y_2694_ = stack[1].m_obj;
lean_object* v___y_2695_ = stack[2].m_obj;
lean_object* v___y_2696_ = stack[3].m_obj;
lean_object* v___y_2697_ = stack[4].m_obj;
lean_object* v___y_2698_ = stack[5].m_obj;
lean_object* v___y_2699_ = stack[6].m_obj;
lean_object* v___y_2700_ = stack[7].m_obj;
lean_object* v___y_2701_ = stack[8].m_obj;
lean_object* v___y_2702_ = stack[9].m_obj;
lean_object* v___y_2703_ = stack[10].m_obj;
lean_object* v___y_2704_ = stack[11].m_obj;
lean_object* v_res_2707_;
v_res_2707_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7(v_type_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
stack->m_obj
 = v_res_2707_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7___boxed(lean_object* v_type_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3_spec__4_spec__7(v_type_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
return v_res_2721_;
}
}
lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(lean_object* v_e_2722_, lean_object* v_gen_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_){
_start:
{
lean_object* v___x_2736_; 
v___x_2736_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_gen_2723_, v_e_2722_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; lean_object* v___x_2738_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2737_);
lean_dec_ref_known(v___x_2736_, 1);
v___x_2738_ = l_Lean_Meta_Sym_shareCommon(v_a_2737_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_);
return v___x_2738_;
}
else
{
return v___x_2736_;
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_Expr_denoteAsRingExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2722_ = stack[0].m_obj;
lean_object* v_gen_2723_ = stack[1].m_obj;
lean_object* v_a_2724_ = stack[2].m_obj;
lean_object* v_a_2725_ = stack[3].m_obj;
lean_object* v_a_2726_ = stack[4].m_obj;
lean_object* v_a_2727_ = stack[5].m_obj;
lean_object* v_a_2728_ = stack[6].m_obj;
lean_object* v_a_2729_ = stack[7].m_obj;
lean_object* v_a_2730_ = stack[8].m_obj;
lean_object* v_a_2731_ = stack[9].m_obj;
lean_object* v_a_2732_ = stack[10].m_obj;
lean_object* v_a_2733_ = stack[11].m_obj;
lean_object* v_a_2734_ = stack[12].m_obj;
lean_object* v_res_2739_;
v_res_2739_ = l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(v_e_2722_, v_gen_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_);
stack->m_obj
 = v_res_2739_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr___boxed(lean_object* v_e_2740_, lean_object* v_gen_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(v_e_2740_, v_gen_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_);
lean_dec(v_a_2752_);
lean_dec_ref(v_a_2751_);
lean_dec(v_a_2750_);
lean_dec_ref(v_a_2749_);
lean_dec(v_a_2748_);
lean_dec_ref(v_a_2747_);
lean_dec(v_a_2746_);
lean_dec_ref(v_a_2745_);
lean_dec(v_a_2744_);
lean_dec(v_a_2743_);
lean_dec(v_a_2742_);
return v_res_2754_;
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
