// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.NonCommSemiringM
// Imports: public import Lean.Meta.Tactic.Grind.Arith.CommRing.SemiringM
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
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Sym_Arith_arithExt;
lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getNCSemiring(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default;
lean_object* l_Array_rightpad___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getArithState___redArg(lean_object*, lean_object*);
lean_object* l_instMonadLiftT___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__1___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___closed__1_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "`grind` internal error, invalid semiringId"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "expression in two different semirings"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "`grind` internal error, semiring term has not been internalized"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0___boxed(lean_object**);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__1;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__3_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__4_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__5_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__7;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__8;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__9;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__10;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__11;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__12;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__13;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__14;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__15;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__16;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__17;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__18;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__19;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__20;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__21;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__22;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__23;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__24;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__25;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__26;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__27;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__28;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__29;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__30;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__31;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__32;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__33;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__34 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__34_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__35 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__35_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__36 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__36_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__37;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__38;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__39;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__40;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__41;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__42;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__43;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__44;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__45;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__46 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__46_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__46_value),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6_value)} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__47 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__47_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__48;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__49;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__50;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__51;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__52;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__53;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__54;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run___redArg(lean_object* v_semiringId_1_, lean_object* v_x_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run___redArg___boxed(lean_object* v_semiringId_15_, lean_object* v_x_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run___redArg(v_semiringId_15_, v_x_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run(lean_object* v_00_u03b1_29_, lean_object* v_semiringId_30_, lean_object* v_x_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run___boxed(lean_object* v_00_u03b1_44_, lean_object* v_semiringId_45_, lean_object* v_x_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run(v_00_u03b1_44_, v_semiringId_45_, v_x_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__0(lean_object* v_e_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Meta_Sym_canon(v_e_59_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v_a_73_; lean_object* v___x_74_; 
v_a_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_a_73_);
lean_dec_ref_known(v___x_72_, 1);
v___x_74_ = l_Lean_Meta_Sym_shareCommon(v_a_73_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_);
return v___x_74_;
}
else
{
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__0___boxed(lean_object* v_e_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__0(v_e_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
lean_dec(v___y_78_);
lean_dec(v___y_77_);
lean_dec(v___y_76_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__1(lean_object* v_e_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_e_89_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__1___boxed(lean_object* v_e_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__1(v_e_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
lean_dec(v___y_106_);
lean_dec(v___y_105_);
lean_dec(v___y_104_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0_spec__0(lean_object* v_msgData_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v___x_129_; lean_object* v_env_130_; lean_object* v___x_131_; lean_object* v_toCold_132_; lean_object* v_mctx_133_; lean_object* v_lctx_134_; lean_object* v_options_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_129_ = lean_st_ref_get(v___y_127_);
v_env_130_ = lean_ctor_get(v___x_129_, 0);
lean_inc_ref(v_env_130_);
lean_dec(v___x_129_);
v___x_131_ = lean_st_ref_get(v___y_125_);
v_toCold_132_ = lean_ctor_get(v___y_126_, 0);
v_mctx_133_ = lean_ctor_get(v___x_131_, 0);
lean_inc_ref(v_mctx_133_);
lean_dec(v___x_131_);
v_lctx_134_ = lean_ctor_get(v___y_124_, 2);
v_options_135_ = lean_ctor_get(v_toCold_132_, 2);
lean_inc_ref(v_options_135_);
lean_inc_ref(v_lctx_134_);
v___x_136_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_136_, 0, v_env_130_);
lean_ctor_set(v___x_136_, 1, v_mctx_133_);
lean_ctor_set(v___x_136_, 2, v_lctx_134_);
lean_ctor_set(v___x_136_, 3, v_options_135_);
v___x_137_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v_msgData_123_);
v___x_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0_spec__0___boxed(lean_object* v_msgData_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0_spec__0(v_msgData_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg(lean_object* v_msg_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_ref_152_; lean_object* v___x_153_; lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_162_; 
v_ref_152_ = lean_ctor_get(v___y_149_, 2);
v___x_153_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0_spec__0(v_msg_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
v_a_154_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_162_ == 0)
{
v___x_156_ = v___x_153_;
v_isShared_157_ = v_isSharedCheck_162_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_153_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_162_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v___x_160_; 
lean_inc(v_ref_152_);
v___x_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_158_, 0, v_ref_152_);
lean_ctor_set(v___x_158_, 1, v_a_154_);
if (v_isShared_157_ == 0)
{
lean_ctor_set_tag(v___x_156_, 1);
lean_ctor_set(v___x_156_, 0, v___x_158_);
v___x_160_ = v___x_156_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_158_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg___boxed(lean_object* v_msg_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg(v_msg_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
return v_res_169_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__1(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__0));
v___x_172_ = l_Lean_stringToMessageData(v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring(lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_179_, v_a_182_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_199_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_199_ == 0)
{
v___x_188_ = v___x_185_;
v_isShared_189_ = v_isSharedCheck_199_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_185_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_199_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v_ncSemirings_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v_ncSemirings_190_ = lean_ctor_get(v_a_186_, 4);
lean_inc_ref(v_ncSemirings_190_);
lean_dec(v_a_186_);
v___x_191_ = lean_array_get_size(v_ncSemirings_190_);
v___x_192_ = lean_nat_dec_lt(v_a_173_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec_ref(v_ncSemirings_190_);
lean_del_object(v___x_188_);
v___x_193_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__1);
v___x_194_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg(v___x_193_, v_a_180_, v_a_181_, v_a_182_, v_a_183_);
return v___x_194_;
}
else
{
lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_195_ = lean_array_fget(v_ncSemirings_190_, v_a_173_);
lean_dec_ref(v_ncSemirings_190_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v___x_195_);
v___x_197_ = v___x_188_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
v_a_200_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_185_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_185_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___boxed(lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring(v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
lean_dec(v_a_218_);
lean_dec_ref(v_a_217_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
lean_dec(v_a_210_);
lean_dec(v_a_209_);
lean_dec(v_a_208_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0(lean_object* v_00_u03b1_221_, lean_object* v_msg_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg(v_msg_222_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___boxed(lean_object* v_00_u03b1_236_, lean_object* v_msg_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0(v_00_u03b1_236_, v_msg_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v___y_240_);
lean_dec(v___y_239_);
lean_dec(v___y_238_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___lam__0(lean_object* v_a_251_, lean_object* v_f_252_, lean_object* v_s_253_){
_start:
{
lean_object* v_exp_254_; lean_object* v_rings_255_; lean_object* v_semirings_256_; lean_object* v_ncRings_257_; lean_object* v_ncSemirings_258_; lean_object* v_typeClassify_259_; lean_object* v_orders_260_; lean_object* v_typeOrderClassify_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v_exp_254_ = lean_ctor_get(v_s_253_, 0);
v_rings_255_ = lean_ctor_get(v_s_253_, 1);
v_semirings_256_ = lean_ctor_get(v_s_253_, 2);
v_ncRings_257_ = lean_ctor_get(v_s_253_, 3);
v_ncSemirings_258_ = lean_ctor_get(v_s_253_, 4);
v_typeClassify_259_ = lean_ctor_get(v_s_253_, 5);
v_orders_260_ = lean_ctor_get(v_s_253_, 6);
v_typeOrderClassify_261_ = lean_ctor_get(v_s_253_, 7);
v___x_262_ = lean_array_get_size(v_ncSemirings_258_);
v___x_263_ = lean_nat_dec_lt(v_a_251_, v___x_262_);
if (v___x_263_ == 0)
{
lean_dec_ref(v_f_252_);
return v_s_253_;
}
else
{
lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_275_; 
lean_inc_ref(v_typeOrderClassify_261_);
lean_inc_ref(v_orders_260_);
lean_inc_ref(v_typeClassify_259_);
lean_inc_ref(v_ncSemirings_258_);
lean_inc_ref(v_ncRings_257_);
lean_inc_ref(v_semirings_256_);
lean_inc_ref(v_rings_255_);
lean_inc(v_exp_254_);
v_isSharedCheck_275_ = !lean_is_exclusive(v_s_253_);
if (v_isSharedCheck_275_ == 0)
{
lean_object* v_unused_276_; lean_object* v_unused_277_; lean_object* v_unused_278_; lean_object* v_unused_279_; lean_object* v_unused_280_; lean_object* v_unused_281_; lean_object* v_unused_282_; lean_object* v_unused_283_; 
v_unused_276_ = lean_ctor_get(v_s_253_, 7);
lean_dec(v_unused_276_);
v_unused_277_ = lean_ctor_get(v_s_253_, 6);
lean_dec(v_unused_277_);
v_unused_278_ = lean_ctor_get(v_s_253_, 5);
lean_dec(v_unused_278_);
v_unused_279_ = lean_ctor_get(v_s_253_, 4);
lean_dec(v_unused_279_);
v_unused_280_ = lean_ctor_get(v_s_253_, 3);
lean_dec(v_unused_280_);
v_unused_281_ = lean_ctor_get(v_s_253_, 2);
lean_dec(v_unused_281_);
v_unused_282_ = lean_ctor_get(v_s_253_, 1);
lean_dec(v_unused_282_);
v_unused_283_ = lean_ctor_get(v_s_253_, 0);
lean_dec(v_unused_283_);
v___x_265_ = v_s_253_;
v_isShared_266_ = v_isSharedCheck_275_;
goto v_resetjp_264_;
}
else
{
lean_dec(v_s_253_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_275_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v_v_267_; lean_object* v___x_268_; lean_object* v_xs_x27_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_273_; 
v_v_267_ = lean_array_fget(v_ncSemirings_258_, v_a_251_);
v___x_268_ = lean_box(0);
v_xs_x27_269_ = lean_array_fset(v_ncSemirings_258_, v_a_251_, v___x_268_);
v___x_270_ = lean_apply_1(v_f_252_, v_v_267_);
v___x_271_ = lean_array_fset(v_xs_x27_269_, v_a_251_, v___x_270_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 4, v___x_271_);
v___x_273_ = v___x_265_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_exp_254_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_rings_255_);
lean_ctor_set(v_reuseFailAlloc_274_, 2, v_semirings_256_);
lean_ctor_set(v_reuseFailAlloc_274_, 3, v_ncRings_257_);
lean_ctor_set(v_reuseFailAlloc_274_, 4, v___x_271_);
lean_ctor_set(v_reuseFailAlloc_274_, 5, v_typeClassify_259_);
lean_ctor_set(v_reuseFailAlloc_274_, 6, v_orders_260_);
lean_ctor_set(v_reuseFailAlloc_274_, 7, v_typeOrderClassify_261_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___lam__0___boxed(lean_object* v_a_284_, lean_object* v_f_285_, lean_object* v_s_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___lam__0(v_a_284_, v_f_285_, v_s_286_);
lean_dec(v_a_284_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg(lean_object* v_f_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v___f_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
lean_inc(v_a_289_);
v___f_292_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_292_, 0, v_a_289_);
lean_closure_set(v___f_292_, 1, v_f_288_);
v___x_293_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_294_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_293_, v___f_292_, v_a_290_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___boxed(lean_object* v_f_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg(v_f_295_, v_a_296_, v_a_297_);
lean_dec(v_a_297_);
lean_dec(v_a_296_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring(lean_object* v_f_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg(v_f_300_, v_a_301_, v_a_307_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___boxed(lean_object* v_f_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring(v_f_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
lean_dec(v_a_321_);
lean_dec_ref(v_a_320_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
lean_dec(v_a_317_);
lean_dec(v_a_316_);
lean_dec(v_a_315_);
return v_res_327_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__1(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__0));
v___x_330_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___boxed), 12, 0);
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v___x_329_);
return v___x_331_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM(void){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__1);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState___redArg(lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_334_, v_a_335_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_346_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_346_ == 0)
{
v___x_340_ = v___x_337_;
v_isShared_341_ = v_isSharedCheck_346_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_346_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; lean_object* v___x_344_; 
v___x_342_ = l_Lean_Meta_Grind_Arith_CommRing_State_getNCSemiring(v_a_338_, v_a_333_);
lean_dec(v_a_338_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_342_);
v___x_344_ = v___x_340_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_342_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
v_a_347_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_337_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_337_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState___redArg___boxed(lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState___redArg(v_a_355_, v_a_356_, v_a_357_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_356_);
lean_dec(v_a_355_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState(lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState___redArg(v_a_360_, v_a_361_, v_a_369_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState___boxed(lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState(v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_);
lean_dec(v_a_383_);
lean_dec_ref(v_a_382_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec(v_a_375_);
lean_dec(v_a_374_);
lean_dec(v_a_373_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg___lam__0(lean_object* v_a_386_, lean_object* v_f_387_, lean_object* v_s_388_){
_start:
{
lean_object* v_rings_389_; lean_object* v_exprToRingId_390_; lean_object* v_semirings_391_; lean_object* v_exprToSemiringId_392_; lean_object* v_ncRings_393_; lean_object* v_exprToNCRingId_394_; lean_object* v_ncSemirings_395_; lean_object* v_exprToNCSemiringId_396_; lean_object* v_steps_397_; uint8_t v_reportedMaxDegreeIssue_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_419_; 
v_rings_389_ = lean_ctor_get(v_s_388_, 0);
v_exprToRingId_390_ = lean_ctor_get(v_s_388_, 1);
v_semirings_391_ = lean_ctor_get(v_s_388_, 2);
v_exprToSemiringId_392_ = lean_ctor_get(v_s_388_, 3);
v_ncRings_393_ = lean_ctor_get(v_s_388_, 4);
v_exprToNCRingId_394_ = lean_ctor_get(v_s_388_, 5);
v_ncSemirings_395_ = lean_ctor_get(v_s_388_, 6);
v_exprToNCSemiringId_396_ = lean_ctor_get(v_s_388_, 7);
v_steps_397_ = lean_ctor_get(v_s_388_, 8);
v_reportedMaxDegreeIssue_398_ = lean_ctor_get_uint8(v_s_388_, sizeof(void*)*9);
v_isSharedCheck_419_ = !lean_is_exclusive(v_s_388_);
if (v_isSharedCheck_419_ == 0)
{
v___x_400_ = v_s_388_;
v_isShared_401_ = v_isSharedCheck_419_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_steps_397_);
lean_inc(v_exprToNCSemiringId_396_);
lean_inc(v_ncSemirings_395_);
lean_inc(v_exprToNCRingId_394_);
lean_inc(v_ncRings_393_);
lean_inc(v_exprToSemiringId_392_);
lean_inc(v_semirings_391_);
lean_inc(v_exprToRingId_390_);
lean_inc(v_rings_389_);
lean_dec(v_s_388_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_419_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_402_ = lean_unsigned_to_nat(1u);
v___x_403_ = lean_nat_add(v_a_386_, v___x_402_);
v___x_404_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default;
v___x_405_ = l_Array_rightpad___redArg(v___x_403_, v___x_404_, v_ncSemirings_395_);
lean_dec(v___x_403_);
v___x_406_ = lean_array_get_size(v___x_405_);
v___x_407_ = lean_nat_dec_lt(v_a_386_, v___x_406_);
if (v___x_407_ == 0)
{
lean_object* v___x_409_; 
lean_dec_ref(v_f_387_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 6, v___x_405_);
v___x_409_ = v___x_400_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_rings_389_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_exprToRingId_390_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v_semirings_391_);
lean_ctor_set(v_reuseFailAlloc_410_, 3, v_exprToSemiringId_392_);
lean_ctor_set(v_reuseFailAlloc_410_, 4, v_ncRings_393_);
lean_ctor_set(v_reuseFailAlloc_410_, 5, v_exprToNCRingId_394_);
lean_ctor_set(v_reuseFailAlloc_410_, 6, v___x_405_);
lean_ctor_set(v_reuseFailAlloc_410_, 7, v_exprToNCSemiringId_396_);
lean_ctor_set(v_reuseFailAlloc_410_, 8, v_steps_397_);
lean_ctor_set_uint8(v_reuseFailAlloc_410_, sizeof(void*)*9, v_reportedMaxDegreeIssue_398_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
else
{
lean_object* v_v_411_; lean_object* v___x_412_; lean_object* v_xs_x27_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_417_; 
v_v_411_ = lean_array_fget(v___x_405_, v_a_386_);
v___x_412_ = lean_box(0);
v_xs_x27_413_ = lean_array_fset(v___x_405_, v_a_386_, v___x_412_);
v___x_414_ = lean_apply_1(v_f_387_, v_v_411_);
v___x_415_ = lean_array_fset(v_xs_x27_413_, v_a_386_, v___x_414_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 6, v___x_415_);
v___x_417_ = v___x_400_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_rings_389_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_exprToRingId_390_);
lean_ctor_set(v_reuseFailAlloc_418_, 2, v_semirings_391_);
lean_ctor_set(v_reuseFailAlloc_418_, 3, v_exprToSemiringId_392_);
lean_ctor_set(v_reuseFailAlloc_418_, 4, v_ncRings_393_);
lean_ctor_set(v_reuseFailAlloc_418_, 5, v_exprToNCRingId_394_);
lean_ctor_set(v_reuseFailAlloc_418_, 6, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_418_, 7, v_exprToNCSemiringId_396_);
lean_ctor_set(v_reuseFailAlloc_418_, 8, v_steps_397_);
lean_ctor_set_uint8(v_reuseFailAlloc_418_, sizeof(void*)*9, v_reportedMaxDegreeIssue_398_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg___lam__0___boxed(lean_object* v_a_420_, lean_object* v_f_421_, lean_object* v_s_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg___lam__0(v_a_420_, v_f_421_, v_s_422_);
lean_dec(v_a_420_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg(lean_object* v_f_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v___f_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
lean_inc(v_a_425_);
v___f_428_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_428_, 0, v_a_425_);
lean_closure_set(v___f_428_, 1, v_f_424_);
v___x_429_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_430_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_429_, v___f_428_, v_a_426_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg___boxed(lean_object* v_f_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg(v_f_431_, v_a_432_, v_a_433_);
lean_dec(v_a_433_);
lean_dec(v_a_432_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState(lean_object* v_f_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg(v_f_436_, v_a_437_, v_a_438_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___boxed(lean_object* v_f_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState(v_f_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_);
lean_dec(v_a_461_);
lean_dec_ref(v_a_460_);
lean_dec(v_a_459_);
lean_dec_ref(v_a_458_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
lean_dec(v_a_453_);
lean_dec(v_a_452_);
lean_dec(v_a_451_);
return v_res_463_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM___closed__1(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM___closed__0));
v___x_466_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState___boxed), 12, 0);
v___x_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
lean_ctor_set(v___x_467_, 1, v___x_465_);
return v___x_467_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM(void){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM___closed__1);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_469_, lean_object* v_vals_470_, lean_object* v_i_471_, lean_object* v_k_472_){
_start:
{
lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_473_ = lean_array_get_size(v_keys_469_);
v___x_474_ = lean_nat_dec_lt(v_i_471_, v___x_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; 
lean_dec(v_i_471_);
v___x_475_ = lean_box(0);
return v___x_475_;
}
else
{
lean_object* v_k_x27_476_; size_t v___x_477_; size_t v___x_478_; uint8_t v___x_479_; 
v_k_x27_476_ = lean_array_fget_borrowed(v_keys_469_, v_i_471_);
v___x_477_ = lean_ptr_addr(v_k_472_);
v___x_478_ = lean_ptr_addr(v_k_x27_476_);
v___x_479_ = lean_usize_dec_eq(v___x_477_, v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_unsigned_to_nat(1u);
v___x_481_ = lean_nat_add(v_i_471_, v___x_480_);
lean_dec(v_i_471_);
v_i_471_ = v___x_481_;
goto _start;
}
else
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_array_fget_borrowed(v_vals_470_, v_i_471_);
lean_dec(v_i_471_);
lean_inc(v___x_483_);
v___x_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
return v___x_484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_485_, lean_object* v_vals_486_, lean_object* v_i_487_, lean_object* v_k_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_485_, v_vals_486_, v_i_487_, v_k_488_);
lean_dec_ref(v_k_488_);
lean_dec_ref(v_vals_486_);
lean_dec_ref(v_keys_485_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg(lean_object* v_x_490_, size_t v_x_491_, lean_object* v_x_492_){
_start:
{
if (lean_obj_tag(v_x_490_) == 0)
{
lean_object* v_es_493_; lean_object* v___x_494_; size_t v___x_495_; size_t v___x_496_; lean_object* v_j_497_; lean_object* v___x_498_; 
v_es_493_ = lean_ctor_get(v_x_490_, 0);
v___x_494_ = lean_box(2);
v___x_495_ = ((size_t)31ULL);
v___x_496_ = lean_usize_land(v_x_491_, v___x_495_);
v_j_497_ = lean_usize_to_nat(v___x_496_);
v___x_498_ = lean_array_get_borrowed(v___x_494_, v_es_493_, v_j_497_);
lean_dec(v_j_497_);
switch(lean_obj_tag(v___x_498_))
{
case 0:
{
lean_object* v_key_499_; lean_object* v_val_500_; size_t v___x_501_; size_t v___x_502_; uint8_t v___x_503_; 
v_key_499_ = lean_ctor_get(v___x_498_, 0);
v_val_500_ = lean_ctor_get(v___x_498_, 1);
v___x_501_ = lean_ptr_addr(v_x_492_);
v___x_502_ = lean_ptr_addr(v_key_499_);
v___x_503_ = lean_usize_dec_eq(v___x_501_, v___x_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; 
v___x_504_ = lean_box(0);
return v___x_504_;
}
else
{
lean_object* v___x_505_; 
lean_inc(v_val_500_);
v___x_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_505_, 0, v_val_500_);
return v___x_505_;
}
}
case 1:
{
lean_object* v_node_506_; size_t v___x_507_; size_t v___x_508_; 
v_node_506_ = lean_ctor_get(v___x_498_, 0);
v___x_507_ = ((size_t)5ULL);
v___x_508_ = lean_usize_shift_right(v_x_491_, v___x_507_);
v_x_490_ = v_node_506_;
v_x_491_ = v___x_508_;
goto _start;
}
default: 
{
lean_object* v___x_510_; 
v___x_510_ = lean_box(0);
return v___x_510_;
}
}
}
else
{
lean_object* v_ks_511_; lean_object* v_vs_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v_ks_511_ = lean_ctor_get(v_x_490_, 0);
v_vs_512_ = lean_ctor_get(v_x_490_, 1);
v___x_513_ = lean_unsigned_to_nat(0u);
v___x_514_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_511_, v_vs_512_, v___x_513_, v_x_492_);
return v___x_514_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_515_, lean_object* v_x_516_, lean_object* v_x_517_){
_start:
{
size_t v_x_905__boxed_518_; lean_object* v_res_519_; 
v_x_905__boxed_518_ = lean_unbox_usize(v_x_516_);
lean_dec(v_x_516_);
v_res_519_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg(v_x_515_, v_x_905__boxed_518_, v_x_517_);
lean_dec_ref(v_x_517_);
lean_dec_ref(v_x_515_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg(lean_object* v_x_520_, lean_object* v_x_521_){
_start:
{
size_t v___x_522_; size_t v___x_523_; size_t v___x_524_; uint64_t v___x_525_; size_t v___x_526_; lean_object* v___x_527_; 
v___x_522_ = lean_ptr_addr(v_x_521_);
v___x_523_ = ((size_t)3ULL);
v___x_524_ = lean_usize_shift_right(v___x_522_, v___x_523_);
v___x_525_ = lean_usize_to_uint64(v___x_524_);
v___x_526_ = lean_uint64_to_usize(v___x_525_);
v___x_527_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg(v_x_520_, v___x_526_, v_x_521_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg___boxed(lean_object* v_x_528_, lean_object* v_x_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg(v_x_528_, v_x_529_);
lean_dec_ref(v_x_529_);
lean_dec_ref(v_x_528_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg(lean_object* v_e_531_, lean_object* v_a_532_, lean_object* v_a_533_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_532_, v_a_533_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_545_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_545_ == 0)
{
v___x_538_ = v___x_535_;
v_isShared_539_ = v_isSharedCheck_545_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_535_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_545_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v_exprToNCSemiringId_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
v_exprToNCSemiringId_540_ = lean_ctor_get(v_a_536_, 7);
lean_inc_ref(v_exprToNCSemiringId_540_);
lean_dec(v_a_536_);
v___x_541_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg(v_exprToNCSemiringId_540_, v_e_531_);
lean_dec_ref(v_exprToNCSemiringId_540_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 0, v___x_541_);
v___x_543_ = v___x_538_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
else
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_553_; 
v_a_546_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_553_ == 0)
{
v___x_548_ = v___x_535_;
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_535_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_546_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg___boxed(lean_object* v_e_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg(v_e_554_, v_a_555_, v_a_556_);
lean_dec_ref(v_a_556_);
lean_dec(v_a_555_);
lean_dec_ref(v_e_554_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f(lean_object* v_e_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg(v_e_559_, v_a_560_, v_a_568_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___boxed(lean_object* v_e_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f(v_e_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec(v_a_573_);
lean_dec_ref(v_e_572_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0(lean_object* v_00_u03b2_585_, lean_object* v_x_586_, lean_object* v_x_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg(v_x_586_, v_x_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___boxed(lean_object* v_00_u03b2_589_, lean_object* v_x_590_, lean_object* v_x_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0(v_00_u03b2_589_, v_x_590_, v_x_591_);
lean_dec_ref(v_x_591_);
lean_dec_ref(v_x_590_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_593_, lean_object* v_x_594_, size_t v_x_595_, lean_object* v_x_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg(v_x_594_, v_x_595_, v_x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_598_, lean_object* v_x_599_, lean_object* v_x_600_, lean_object* v_x_601_){
_start:
{
size_t v_x_1026__boxed_602_; lean_object* v_res_603_; 
v_x_1026__boxed_602_ = lean_unbox_usize(v_x_600_);
lean_dec(v_x_600_);
v_res_603_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0(v_00_u03b2_598_, v_x_599_, v_x_1026__boxed_602_, v_x_601_);
lean_dec_ref(v_x_601_);
lean_dec_ref(v_x_599_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_604_, lean_object* v_keys_605_, lean_object* v_vals_606_, lean_object* v_heq_607_, lean_object* v_i_608_, lean_object* v_k_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_605_, v_vals_606_, v_i_608_, v_k_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_611_, lean_object* v_keys_612_, lean_object* v_vals_613_, lean_object* v_heq_614_, lean_object* v_i_615_, lean_object* v_k_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_611_, v_keys_612_, v_vals_613_, v_heq_614_, v_i_615_, v_k_616_);
lean_dec_ref(v_k_616_);
lean_dec_ref(v_vals_613_);
lean_dec_ref(v_keys_612_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_618_, lean_object* v_x_619_, lean_object* v_x_620_, lean_object* v_x_621_){
_start:
{
lean_object* v_ks_622_; lean_object* v_vs_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_649_; 
v_ks_622_ = lean_ctor_get(v_x_618_, 0);
v_vs_623_ = lean_ctor_get(v_x_618_, 1);
v_isSharedCheck_649_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_649_ == 0)
{
v___x_625_ = v_x_618_;
v_isShared_626_ = v_isSharedCheck_649_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_vs_623_);
lean_inc(v_ks_622_);
lean_dec(v_x_618_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_649_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_627_ = lean_array_get_size(v_ks_622_);
v___x_628_ = lean_nat_dec_lt(v_x_619_, v___x_627_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_632_; 
lean_dec(v_x_619_);
v___x_629_ = lean_array_push(v_ks_622_, v_x_620_);
v___x_630_ = lean_array_push(v_vs_623_, v_x_621_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v___x_630_);
lean_ctor_set(v___x_625_, 0, v___x_629_);
v___x_632_ = v___x_625_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v___x_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
else
{
lean_object* v_k_x27_634_; size_t v___x_635_; size_t v___x_636_; uint8_t v___x_637_; 
v_k_x27_634_ = lean_array_fget_borrowed(v_ks_622_, v_x_619_);
v___x_635_ = lean_ptr_addr(v_x_620_);
v___x_636_ = lean_ptr_addr(v_k_x27_634_);
v___x_637_ = lean_usize_dec_eq(v___x_635_, v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_639_; 
if (v_isShared_626_ == 0)
{
v___x_639_ = v___x_625_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_ks_622_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_vs_623_);
v___x_639_ = v_reuseFailAlloc_643_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_unsigned_to_nat(1u);
v___x_641_ = lean_nat_add(v_x_619_, v___x_640_);
lean_dec(v_x_619_);
v_x_618_ = v___x_639_;
v_x_619_ = v___x_641_;
goto _start;
}
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_644_ = lean_array_fset(v_ks_622_, v_x_619_, v_x_620_);
v___x_645_ = lean_array_fset(v_vs_623_, v_x_619_, v_x_621_);
lean_dec(v_x_619_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v___x_645_);
lean_ctor_set(v___x_625_, 0, v___x_644_);
v___x_647_ = v___x_625_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_644_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v___x_645_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_650_, lean_object* v_k_651_, lean_object* v_v_652_){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = lean_unsigned_to_nat(0u);
v___x_654_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_650_, v___x_653_, v_k_651_, v_v_652_);
return v___x_654_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(lean_object* v_x_656_, size_t v_x_657_, size_t v_x_658_, lean_object* v_x_659_, lean_object* v_x_660_){
_start:
{
if (lean_obj_tag(v_x_656_) == 0)
{
lean_object* v_es_661_; size_t v___x_662_; size_t v___x_663_; lean_object* v_j_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v_es_661_ = lean_ctor_get(v_x_656_, 0);
v___x_662_ = ((size_t)31ULL);
v___x_663_ = lean_usize_land(v_x_657_, v___x_662_);
v_j_664_ = lean_usize_to_nat(v___x_663_);
v___x_665_ = lean_array_get_size(v_es_661_);
v___x_666_ = lean_nat_dec_lt(v_j_664_, v___x_665_);
if (v___x_666_ == 0)
{
lean_dec(v_j_664_);
lean_dec(v_x_660_);
lean_dec_ref(v_x_659_);
return v_x_656_;
}
else
{
lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_707_; 
lean_inc_ref(v_es_661_);
v_isSharedCheck_707_ = !lean_is_exclusive(v_x_656_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; 
v_unused_708_ = lean_ctor_get(v_x_656_, 0);
lean_dec(v_unused_708_);
v___x_668_ = v_x_656_;
v_isShared_669_ = v_isSharedCheck_707_;
goto v_resetjp_667_;
}
else
{
lean_dec(v_x_656_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_707_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v_v_670_; lean_object* v___x_671_; lean_object* v_xs_x27_672_; lean_object* v___y_674_; 
v_v_670_ = lean_array_fget(v_es_661_, v_j_664_);
v___x_671_ = lean_box(0);
v_xs_x27_672_ = lean_array_fset(v_es_661_, v_j_664_, v___x_671_);
switch(lean_obj_tag(v_v_670_))
{
case 0:
{
lean_object* v_key_679_; lean_object* v_val_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_692_; 
v_key_679_ = lean_ctor_get(v_v_670_, 0);
v_val_680_ = lean_ctor_get(v_v_670_, 1);
v_isSharedCheck_692_ = !lean_is_exclusive(v_v_670_);
if (v_isSharedCheck_692_ == 0)
{
v___x_682_ = v_v_670_;
v_isShared_683_ = v_isSharedCheck_692_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_val_680_);
lean_inc(v_key_679_);
lean_dec(v_v_670_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_692_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
size_t v___x_684_; size_t v___x_685_; uint8_t v___x_686_; 
v___x_684_ = lean_ptr_addr(v_x_659_);
v___x_685_ = lean_ptr_addr(v_key_679_);
v___x_686_ = lean_usize_dec_eq(v___x_684_, v___x_685_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; lean_object* v___x_688_; 
lean_del_object(v___x_682_);
v___x_687_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_679_, v_val_680_, v_x_659_, v_x_660_);
v___x_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
v___y_674_ = v___x_688_;
goto v___jp_673_;
}
else
{
lean_object* v___x_690_; 
lean_dec(v_val_680_);
lean_dec(v_key_679_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v_x_660_);
lean_ctor_set(v___x_682_, 0, v_x_659_);
v___x_690_ = v___x_682_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_x_659_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_x_660_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
v___y_674_ = v___x_690_;
goto v___jp_673_;
}
}
}
}
case 1:
{
lean_object* v_node_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_705_; 
v_node_693_ = lean_ctor_get(v_v_670_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v_v_670_);
if (v_isSharedCheck_705_ == 0)
{
v___x_695_ = v_v_670_;
v_isShared_696_ = v_isSharedCheck_705_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_node_693_);
lean_dec(v_v_670_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_705_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
size_t v___x_697_; size_t v___x_698_; size_t v___x_699_; size_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_697_ = ((size_t)5ULL);
v___x_698_ = lean_usize_shift_right(v_x_657_, v___x_697_);
v___x_699_ = ((size_t)1ULL);
v___x_700_ = lean_usize_add(v_x_658_, v___x_699_);
v___x_701_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(v_node_693_, v___x_698_, v___x_700_, v_x_659_, v_x_660_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_701_);
v___x_703_ = v___x_695_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
v___y_674_ = v___x_703_;
goto v___jp_673_;
}
}
}
default: 
{
lean_object* v___x_706_; 
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v_x_659_);
lean_ctor_set(v___x_706_, 1, v_x_660_);
v___y_674_ = v___x_706_;
goto v___jp_673_;
}
}
v___jp_673_:
{
lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_675_ = lean_array_fset(v_xs_x27_672_, v_j_664_, v___y_674_);
lean_dec(v_j_664_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v___x_675_);
v___x_677_ = v___x_668_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
else
{
lean_object* v_ks_709_; lean_object* v_vs_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_728_; 
v_ks_709_ = lean_ctor_get(v_x_656_, 0);
v_vs_710_ = lean_ctor_get(v_x_656_, 1);
v_isSharedCheck_728_ = !lean_is_exclusive(v_x_656_);
if (v_isSharedCheck_728_ == 0)
{
v___x_712_ = v_x_656_;
v_isShared_713_ = v_isSharedCheck_728_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_vs_710_);
lean_inc(v_ks_709_);
lean_dec(v_x_656_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_728_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_ks_709_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_vs_710_);
v___x_715_ = v_reuseFailAlloc_727_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v_newNode_716_; size_t v___x_717_; uint8_t v___x_718_; 
v_newNode_716_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1___redArg(v___x_715_, v_x_659_, v_x_660_);
v___x_717_ = ((size_t)7ULL);
v___x_718_ = lean_usize_dec_le(v___x_717_, v_x_658_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_719_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_716_);
v___x_720_ = lean_unsigned_to_nat(4u);
v___x_721_ = lean_nat_dec_lt(v___x_719_, v___x_720_);
lean_dec(v___x_719_);
if (v___x_721_ == 0)
{
lean_object* v_ks_722_; lean_object* v_vs_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v_ks_722_ = lean_ctor_get(v_newNode_716_, 0);
lean_inc_ref(v_ks_722_);
v_vs_723_ = lean_ctor_get(v_newNode_716_, 1);
lean_inc_ref(v_vs_723_);
lean_dec_ref(v_newNode_716_);
v___x_724_ = lean_unsigned_to_nat(0u);
v___x_725_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___closed__0);
v___x_726_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg(v_x_658_, v_ks_722_, v_vs_723_, v___x_724_, v___x_725_);
lean_dec_ref(v_vs_723_);
lean_dec_ref(v_ks_722_);
return v___x_726_;
}
else
{
return v_newNode_716_;
}
}
else
{
return v_newNode_716_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg(size_t v_depth_729_, lean_object* v_keys_730_, lean_object* v_vals_731_, lean_object* v_i_732_, lean_object* v_entries_733_){
_start:
{
lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_734_ = lean_array_get_size(v_keys_730_);
v___x_735_ = lean_nat_dec_lt(v_i_732_, v___x_734_);
if (v___x_735_ == 0)
{
lean_dec(v_i_732_);
return v_entries_733_;
}
else
{
lean_object* v_k_736_; lean_object* v_v_737_; size_t v___x_738_; size_t v___x_739_; size_t v___x_740_; uint64_t v___x_741_; size_t v_h_742_; size_t v___x_743_; lean_object* v___x_744_; size_t v___x_745_; size_t v___x_746_; size_t v___x_747_; size_t v_h_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v_k_736_ = lean_array_fget_borrowed(v_keys_730_, v_i_732_);
v_v_737_ = lean_array_fget_borrowed(v_vals_731_, v_i_732_);
v___x_738_ = lean_ptr_addr(v_k_736_);
v___x_739_ = ((size_t)3ULL);
v___x_740_ = lean_usize_shift_right(v___x_738_, v___x_739_);
v___x_741_ = lean_usize_to_uint64(v___x_740_);
v_h_742_ = lean_uint64_to_usize(v___x_741_);
v___x_743_ = ((size_t)5ULL);
v___x_744_ = lean_unsigned_to_nat(1u);
v___x_745_ = ((size_t)1ULL);
v___x_746_ = lean_usize_sub(v_depth_729_, v___x_745_);
v___x_747_ = lean_usize_mul(v___x_743_, v___x_746_);
v_h_748_ = lean_usize_shift_right(v_h_742_, v___x_747_);
v___x_749_ = lean_nat_add(v_i_732_, v___x_744_);
lean_dec(v_i_732_);
lean_inc(v_v_737_);
lean_inc(v_k_736_);
v___x_750_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(v_entries_733_, v_h_748_, v_depth_729_, v_k_736_, v_v_737_);
v_i_732_ = v___x_749_;
v_entries_733_ = v___x_750_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_752_, lean_object* v_keys_753_, lean_object* v_vals_754_, lean_object* v_i_755_, lean_object* v_entries_756_){
_start:
{
size_t v_depth_boxed_757_; lean_object* v_res_758_; 
v_depth_boxed_757_ = lean_unbox_usize(v_depth_752_);
lean_dec(v_depth_752_);
v_res_758_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_757_, v_keys_753_, v_vals_754_, v_i_755_, v_entries_756_);
lean_dec_ref(v_vals_754_);
lean_dec_ref(v_keys_753_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___boxed(lean_object* v_x_759_, lean_object* v_x_760_, lean_object* v_x_761_, lean_object* v_x_762_, lean_object* v_x_763_){
_start:
{
size_t v_x_7502__boxed_764_; size_t v_x_7503__boxed_765_; lean_object* v_res_766_; 
v_x_7502__boxed_764_ = lean_unbox_usize(v_x_760_);
lean_dec(v_x_760_);
v_x_7503__boxed_765_ = lean_unbox_usize(v_x_761_);
lean_dec(v_x_761_);
v_res_766_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(v_x_759_, v_x_7502__boxed_764_, v_x_7503__boxed_765_, v_x_762_, v_x_763_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0___redArg(lean_object* v_x_767_, lean_object* v_x_768_, lean_object* v_x_769_){
_start:
{
size_t v___x_770_; size_t v___x_771_; size_t v___x_772_; uint64_t v___x_773_; size_t v___x_774_; size_t v___x_775_; lean_object* v___x_776_; 
v___x_770_ = lean_ptr_addr(v_x_768_);
v___x_771_ = ((size_t)3ULL);
v___x_772_ = lean_usize_shift_right(v___x_770_, v___x_771_);
v___x_773_ = lean_usize_to_uint64(v___x_772_);
v___x_774_ = lean_uint64_to_usize(v___x_773_);
v___x_775_ = ((size_t)1ULL);
v___x_776_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(v_x_767_, v___x_774_, v___x_775_, v_x_768_, v_x_769_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___lam__0(lean_object* v_e_777_, lean_object* v_a_778_, lean_object* v_s_779_){
_start:
{
lean_object* v_rings_780_; lean_object* v_exprToRingId_781_; lean_object* v_semirings_782_; lean_object* v_exprToSemiringId_783_; lean_object* v_ncRings_784_; lean_object* v_exprToNCRingId_785_; lean_object* v_ncSemirings_786_; lean_object* v_exprToNCSemiringId_787_; lean_object* v_steps_788_; uint8_t v_reportedMaxDegreeIssue_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_797_; 
v_rings_780_ = lean_ctor_get(v_s_779_, 0);
v_exprToRingId_781_ = lean_ctor_get(v_s_779_, 1);
v_semirings_782_ = lean_ctor_get(v_s_779_, 2);
v_exprToSemiringId_783_ = lean_ctor_get(v_s_779_, 3);
v_ncRings_784_ = lean_ctor_get(v_s_779_, 4);
v_exprToNCRingId_785_ = lean_ctor_get(v_s_779_, 5);
v_ncSemirings_786_ = lean_ctor_get(v_s_779_, 6);
v_exprToNCSemiringId_787_ = lean_ctor_get(v_s_779_, 7);
v_steps_788_ = lean_ctor_get(v_s_779_, 8);
v_reportedMaxDegreeIssue_789_ = lean_ctor_get_uint8(v_s_779_, sizeof(void*)*9);
v_isSharedCheck_797_ = !lean_is_exclusive(v_s_779_);
if (v_isSharedCheck_797_ == 0)
{
v___x_791_ = v_s_779_;
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_steps_788_);
lean_inc(v_exprToNCSemiringId_787_);
lean_inc(v_ncSemirings_786_);
lean_inc(v_exprToNCRingId_785_);
lean_inc(v_ncRings_784_);
lean_inc(v_exprToSemiringId_783_);
lean_inc(v_semirings_782_);
lean_inc(v_exprToRingId_781_);
lean_inc(v_rings_780_);
lean_dec(v_s_779_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_795_; 
lean_inc(v_a_778_);
v___x_793_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0___redArg(v_exprToNCSemiringId_787_, v_e_777_, v_a_778_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 7, v___x_793_);
v___x_795_ = v___x_791_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_rings_780_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_exprToRingId_781_);
lean_ctor_set(v_reuseFailAlloc_796_, 2, v_semirings_782_);
lean_ctor_set(v_reuseFailAlloc_796_, 3, v_exprToSemiringId_783_);
lean_ctor_set(v_reuseFailAlloc_796_, 4, v_ncRings_784_);
lean_ctor_set(v_reuseFailAlloc_796_, 5, v_exprToNCRingId_785_);
lean_ctor_set(v_reuseFailAlloc_796_, 6, v_ncSemirings_786_);
lean_ctor_set(v_reuseFailAlloc_796_, 7, v___x_793_);
lean_ctor_set(v_reuseFailAlloc_796_, 8, v_steps_788_);
lean_ctor_set_uint8(v_reuseFailAlloc_796_, sizeof(void*)*9, v_reportedMaxDegreeIssue_789_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___lam__0___boxed(lean_object* v_e_798_, lean_object* v_a_799_, lean_object* v_s_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___lam__0(v_e_798_, v_a_799_, v_s_800_);
lean_dec(v_a_799_);
return v_res_801_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__1(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__0));
v___x_804_ = l_Lean_stringToMessageData(v___x_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(lean_object* v_e_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v___f_818_; lean_object* v___x_819_; 
lean_inc(v_a_806_);
lean_inc_ref(v_e_805_);
v___f_818_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_818_, 0, v_e_805_);
lean_closure_set(v___f_818_, 1, v_a_806_);
v___x_819_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg(v_e_805_, v_a_807_, v_a_812_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_a_820_);
lean_dec_ref_known(v___x_819_, 1);
if (lean_obj_tag(v_a_820_) == 1)
{
lean_object* v_val_821_; uint8_t v___x_822_; 
lean_dec_ref(v___f_818_);
v_val_821_ = lean_ctor_get(v_a_820_, 0);
lean_inc(v_val_821_);
lean_dec_ref_known(v_a_820_, 1);
v___x_822_ = lean_nat_dec_eq(v_val_821_, v_a_806_);
lean_dec(v_val_821_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_823_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__1);
v___x_824_ = l_Lean_indentExpr(v_e_805_);
v___x_825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_823_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_808_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; uint8_t v_verbose_828_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_a_827_);
lean_dec_ref_known(v___x_826_, 1);
v_verbose_828_ = lean_ctor_get_uint8(v_a_827_, 0);
lean_dec(v_a_827_);
if (v_verbose_828_ == 0)
{
lean_dec_ref_known(v___x_825_, 2);
goto v___jp_815_;
}
else
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_Meta_Sym_reportIssue(v___x_825_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_dec_ref_known(v___x_829_, 1);
goto v___jp_815_;
}
else
{
return v___x_829_;
}
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec_ref_known(v___x_825_, 2);
v_a_830_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_826_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_826_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
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
lean_dec_ref(v_e_805_);
goto v___jp_815_;
}
}
else
{
lean_object* v___x_838_; lean_object* v___x_839_; 
lean_dec(v_a_820_);
lean_dec_ref(v_e_805_);
v___x_838_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_839_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_838_, v___f_818_, v_a_807_);
return v___x_839_;
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec_ref(v___f_818_);
lean_dec_ref(v_e_805_);
v_a_840_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_819_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_819_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
v___jp_815_:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = lean_box(0);
v___x_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
return v___x_817_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___boxed(lean_object* v_e_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(v_e_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_);
lean_dec(v_a_856_);
lean_dec_ref(v_a_855_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_a_852_);
lean_dec_ref(v_a_851_);
lean_dec(v_a_850_);
lean_dec(v_a_849_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId(lean_object* v_e_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(v_e_859_, v_a_860_, v_a_861_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___boxed(lean_object* v_e_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId(v_e_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_a_876_);
lean_dec(v_a_875_);
lean_dec(v_a_874_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0(lean_object* v_00_u03b2_887_, lean_object* v_x_888_, lean_object* v_x_889_, lean_object* v_x_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0___redArg(v_x_888_, v_x_889_, v_x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0(lean_object* v_00_u03b2_892_, lean_object* v_x_893_, size_t v_x_894_, size_t v_x_895_, lean_object* v_x_896_, lean_object* v_x_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(v_x_893_, v_x_894_, v_x_895_, v_x_896_, v_x_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_899_, lean_object* v_x_900_, lean_object* v_x_901_, lean_object* v_x_902_, lean_object* v_x_903_, lean_object* v_x_904_){
_start:
{
size_t v_x_7788__boxed_905_; size_t v_x_7789__boxed_906_; lean_object* v_res_907_; 
v_x_7788__boxed_905_ = lean_unbox_usize(v_x_901_);
lean_dec(v_x_901_);
v_x_7789__boxed_906_ = lean_unbox_usize(v_x_902_);
lean_dec(v_x_902_);
v_res_907_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0(v_00_u03b2_899_, v_x_900_, v_x_7788__boxed_905_, v_x_7789__boxed_906_, v_x_903_, v_x_904_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_908_, lean_object* v_n_909_, lean_object* v_k_910_, lean_object* v_v_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1___redArg(v_n_909_, v_k_910_, v_v_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_913_, size_t v_depth_914_, lean_object* v_keys_915_, lean_object* v_vals_916_, lean_object* v_heq_917_, lean_object* v_i_918_, lean_object* v_entries_919_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_914_, v_keys_915_, v_vals_916_, v_i_918_, v_entries_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_921_, lean_object* v_depth_922_, lean_object* v_keys_923_, lean_object* v_vals_924_, lean_object* v_heq_925_, lean_object* v_i_926_, lean_object* v_entries_927_){
_start:
{
size_t v_depth_boxed_928_; lean_object* v_res_929_; 
v_depth_boxed_928_ = lean_unbox_usize(v_depth_922_);
lean_dec(v_depth_922_);
v_res_929_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2(v_00_u03b2_921_, v_depth_boxed_928_, v_keys_923_, v_vals_924_, v_heq_925_, v_i_926_, v_entries_927_);
lean_dec_ref(v_vals_924_);
lean_dec_ref(v_keys_923_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_930_, lean_object* v_x_931_, lean_object* v_x_932_, lean_object* v_x_933_, lean_object* v_x_934_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_931_, v_x_932_, v_x_933_, v_x_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___lam__0(lean_object* v_e_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(v_e_936_, v___y_937_, v___y_938_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___lam__0___boxed(lean_object* v_e_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___lam__0(v_e_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec(v___y_952_);
lean_dec(v___y_951_);
return v_res_963_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0___closed__1(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0___closed__0));
v___x_968_ = l_Lean_stringToMessageData(v___x_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0(lean_object* v___x_969_, lean_object* v___x_970_, lean_object* v___f_971_, lean_object* v___x_972_, lean_object* v___f_973_, lean_object* v_e_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_974_, v___y_976_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; uint8_t v___x_989_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref_known(v___x_987_, 1);
v___x_989_ = lean_unbox(v_a_988_);
lean_dec(v_a_988_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_1449__overap_993_; lean_object* v___x_994_; 
v___x_990_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0___closed__1);
lean_inc_ref(v_e_974_);
v___x_991_ = l_Lean_indentExpr(v_e_974_);
v___x_992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_990_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
lean_inc_ref(v___x_969_);
v___x_1449__overap_993_ = l_Lean_throwError___redArg(v___x_969_, v___x_970_, v___x_992_);
lean_inc(v___y_985_);
lean_inc_ref(v___y_984_);
lean_inc(v___y_983_);
lean_inc_ref(v___y_982_);
lean_inc(v___y_981_);
lean_inc_ref(v___y_980_);
lean_inc(v___y_979_);
lean_inc_ref(v___y_978_);
lean_inc(v___y_977_);
lean_inc(v___y_976_);
lean_inc(v___y_975_);
v___x_994_ = lean_apply_12(v___x_1449__overap_993_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, lean_box(0));
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v___x_1452__overap_995_; lean_object* v___x_996_; 
lean_dec_ref_known(v___x_994_, 1);
v___x_1452__overap_995_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(v___f_971_, v___x_969_, v___x_972_, v___f_973_, v_e_974_);
lean_inc(v___y_985_);
lean_inc_ref(v___y_984_);
lean_inc(v___y_983_);
lean_inc_ref(v___y_982_);
lean_inc(v___y_981_);
lean_inc_ref(v___y_980_);
lean_inc(v___y_979_);
lean_inc_ref(v___y_978_);
lean_inc(v___y_977_);
lean_inc(v___y_976_);
lean_inc(v___y_975_);
v___x_996_ = lean_apply_12(v___x_1452__overap_995_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, lean_box(0));
return v___x_996_;
}
else
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
lean_dec_ref(v_e_974_);
lean_dec_ref(v___f_973_);
lean_dec_ref(v___x_972_);
lean_dec(v___f_971_);
lean_dec_ref(v___x_969_);
v_a_997_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_994_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_994_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
else
{
lean_object* v___x_1456__overap_1005_; lean_object* v___x_1006_; 
lean_dec_ref(v___x_970_);
v___x_1456__overap_1005_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(v___f_971_, v___x_969_, v___x_972_, v___f_973_, v_e_974_);
lean_inc(v___y_985_);
lean_inc_ref(v___y_984_);
lean_inc(v___y_983_);
lean_inc_ref(v___y_982_);
lean_inc(v___y_981_);
lean_inc_ref(v___y_980_);
lean_inc(v___y_979_);
lean_inc_ref(v___y_978_);
lean_inc(v___y_977_);
lean_inc(v___y_976_);
lean_inc(v___y_975_);
v___x_1006_ = lean_apply_12(v___x_1456__overap_1005_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, lean_box(0));
return v___x_1006_;
}
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec_ref(v_e_974_);
lean_dec_ref(v___f_973_);
lean_dec_ref(v___x_972_);
lean_dec(v___f_971_);
lean_dec_ref(v___x_970_);
lean_dec_ref(v___x_969_);
v_a_1007_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_987_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_987_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0___boxed(lean_object** _args){
lean_object* v___x_1015_ = _args[0];
lean_object* v___x_1016_ = _args[1];
lean_object* v___f_1017_ = _args[2];
lean_object* v___x_1018_ = _args[3];
lean_object* v___f_1019_ = _args[4];
lean_object* v_e_1020_ = _args[5];
lean_object* v___y_1021_ = _args[6];
lean_object* v___y_1022_ = _args[7];
lean_object* v___y_1023_ = _args[8];
lean_object* v___y_1024_ = _args[9];
lean_object* v___y_1025_ = _args[10];
lean_object* v___y_1026_ = _args[11];
lean_object* v___y_1027_ = _args[12];
lean_object* v___y_1028_ = _args[13];
lean_object* v___y_1029_ = _args[14];
lean_object* v___y_1030_ = _args[15];
lean_object* v___y_1031_ = _args[16];
lean_object* v___y_1032_ = _args[17];
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0(v___x_1015_, v___x_1016_, v___f_1017_, v___x_1018_, v___f_1019_, v_e_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec(v___y_1021_);
return v_res_1033_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__0(void){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_instMonadEIO___redArg();
return v___x_1034_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__1(void){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__0);
v___x_1036_ = l_StateRefT_x27_instMonad___redArg(v___x_1035_);
return v___x_1036_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__7(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___f_1043_; 
v___x_1042_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_1043_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1043_, 0, v___x_1042_);
return v___f_1043_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__8(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___f_1045_; 
v___x_1044_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_1045_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1045_, 0, v___x_1044_);
return v___f_1045_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__9(void){
_start:
{
lean_object* v___f_1046_; lean_object* v___f_1047_; lean_object* v___x_1048_; 
v___f_1046_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__8, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__8_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__8);
v___f_1047_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__7, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__7_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__7);
v___x_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___f_1047_);
lean_ctor_set(v___x_1048_, 1, v___f_1046_);
return v___x_1048_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__10(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___f_1050_; 
v___x_1049_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__9, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__9_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__9);
v___f_1050_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1050_, 0, v___x_1049_);
return v___f_1050_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__11(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___f_1052_; 
v___x_1051_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__9, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__9_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__9);
v___f_1052_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1052_, 0, v___x_1051_);
return v___f_1052_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__12(void){
_start:
{
lean_object* v___f_1053_; lean_object* v___f_1054_; lean_object* v___x_1055_; 
v___f_1053_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__11, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__11_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__11);
v___f_1054_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__10, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__10_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__10);
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___f_1054_);
lean_ctor_set(v___x_1055_, 1, v___f_1053_);
return v___x_1055_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__13(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___f_1057_; 
v___x_1056_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__12);
v___f_1057_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1057_, 0, v___x_1056_);
return v___f_1057_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__14(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___f_1059_; 
v___x_1058_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__12);
v___f_1059_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1059_, 0, v___x_1058_);
return v___f_1059_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__15(void){
_start:
{
lean_object* v___f_1060_; lean_object* v___f_1061_; lean_object* v___x_1062_; 
v___f_1060_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__14, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__14_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__14);
v___f_1061_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__13, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__13_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__13);
v___x_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___f_1061_);
lean_ctor_set(v___x_1062_, 1, v___f_1060_);
return v___x_1062_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__16(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___f_1064_; 
v___x_1063_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__15, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__15_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__15);
v___f_1064_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1064_, 0, v___x_1063_);
return v___f_1064_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__17(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___f_1066_; 
v___x_1065_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__15, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__15_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__15);
v___f_1066_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1066_, 0, v___x_1065_);
return v___f_1066_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__18(void){
_start:
{
lean_object* v___f_1067_; lean_object* v___f_1068_; lean_object* v___x_1069_; 
v___f_1067_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__17, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__17_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__17);
v___f_1068_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__16, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__16_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__16);
v___x_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___f_1068_);
lean_ctor_set(v___x_1069_, 1, v___f_1067_);
return v___x_1069_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__19(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___f_1071_; 
v___x_1070_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__18, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__18_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__18);
v___f_1071_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1071_, 0, v___x_1070_);
return v___f_1071_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__20(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___f_1073_; 
v___x_1072_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__18, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__18_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__18);
v___f_1073_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1073_, 0, v___x_1072_);
return v___f_1073_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__21(void){
_start:
{
lean_object* v___f_1074_; lean_object* v___f_1075_; lean_object* v___x_1076_; 
v___f_1074_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__20, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__20_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__20);
v___f_1075_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__19, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__19_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__19);
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___f_1075_);
lean_ctor_set(v___x_1076_, 1, v___f_1074_);
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__22(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___f_1078_; 
v___x_1077_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__21, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__21_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__21);
v___f_1078_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1078_, 0, v___x_1077_);
return v___f_1078_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__23(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___f_1080_; 
v___x_1079_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__21, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__21_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__21);
v___f_1080_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1080_, 0, v___x_1079_);
return v___f_1080_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__24(void){
_start:
{
lean_object* v___f_1081_; lean_object* v___f_1082_; lean_object* v___x_1083_; 
v___f_1081_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__23, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__23_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__23);
v___f_1082_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__22, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__22_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__22);
v___x_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___f_1082_);
lean_ctor_set(v___x_1083_, 1, v___f_1081_);
return v___x_1083_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__25(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___f_1085_; 
v___x_1084_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__24, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__24_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__24);
v___f_1085_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1085_, 0, v___x_1084_);
return v___f_1085_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__26(void){
_start:
{
lean_object* v___x_1086_; lean_object* v___f_1087_; 
v___x_1086_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__24, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__24_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__24);
v___f_1087_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1087_, 0, v___x_1086_);
return v___f_1087_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__27(void){
_start:
{
lean_object* v___f_1088_; lean_object* v___f_1089_; lean_object* v___x_1090_; 
v___f_1088_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__26, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__26_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__26);
v___f_1089_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__25, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__25_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__25);
v___x_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___f_1089_);
lean_ctor_set(v___x_1090_, 1, v___f_1088_);
return v___x_1090_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__28(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___f_1092_; 
v___x_1091_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__27, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__27_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__27);
v___f_1092_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1092_, 0, v___x_1091_);
return v___f_1092_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__29(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___f_1094_; 
v___x_1093_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__27, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__27_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__27);
v___f_1094_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1094_, 0, v___x_1093_);
return v___f_1094_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__30(void){
_start:
{
lean_object* v___f_1095_; lean_object* v___f_1096_; lean_object* v___x_1097_; 
v___f_1095_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__29, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__29_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__29);
v___f_1096_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__28, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__28_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__28);
v___x_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___f_1096_);
lean_ctor_set(v___x_1097_, 1, v___f_1095_);
return v___x_1097_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__31(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___f_1099_; 
v___x_1098_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__30, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__30_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__30);
v___f_1099_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1099_, 0, v___x_1098_);
return v___f_1099_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__32(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___f_1101_; 
v___x_1100_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__30, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__30_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__30);
v___f_1101_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1101_, 0, v___x_1100_);
return v___f_1101_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__33(void){
_start:
{
lean_object* v___f_1102_; lean_object* v___f_1103_; lean_object* v___x_1104_; 
v___f_1102_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__32, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__32_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__32);
v___f_1103_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__31, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__31_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__31);
v___x_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___f_1103_);
lean_ctor_set(v___x_1104_, 1, v___f_1102_);
return v___x_1104_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__37(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1108_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1109_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__36));
v___x_1110_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__35));
v___x_1111_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1110_, v___x_1109_, v___x_1108_);
return v___x_1111_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__38(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___f_1113_; lean_object* v___f_1114_; lean_object* v___x_1115_; 
v___x_1112_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__37, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__37_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__37);
v___f_1113_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6));
v___f_1114_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__34));
v___x_1115_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1114_, v___f_1113_, v___x_1112_);
return v___x_1115_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__39(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1116_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__38, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__38_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__38);
v___x_1117_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__36));
v___x_1118_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__35));
v___x_1119_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1118_, v___x_1117_, v___x_1116_);
return v___x_1119_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__40(void){
_start:
{
lean_object* v___x_1120_; lean_object* v___f_1121_; lean_object* v___f_1122_; lean_object* v___x_1123_; 
v___x_1120_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__39, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__39_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__39);
v___f_1121_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6));
v___f_1122_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__34));
v___x_1123_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1122_, v___f_1121_, v___x_1120_);
return v___x_1123_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__41(void){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1124_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__40, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__40_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__40);
v___x_1125_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__36));
v___x_1126_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__35));
v___x_1127_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1126_, v___x_1125_, v___x_1124_);
return v___x_1127_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__42(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___f_1129_; lean_object* v___f_1130_; lean_object* v___x_1131_; 
v___x_1128_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__41, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__41_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__41);
v___f_1129_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6));
v___f_1130_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__34));
v___x_1131_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1130_, v___f_1129_, v___x_1128_);
return v___x_1131_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__43(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___f_1133_; lean_object* v___f_1134_; lean_object* v___x_1135_; 
v___x_1132_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__42, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__42_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__42);
v___f_1133_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6));
v___f_1134_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__34));
v___x_1135_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1134_, v___f_1133_, v___x_1132_);
return v___x_1135_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__44(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1136_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__43, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__43_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__43);
v___x_1137_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__36));
v___x_1138_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__35));
v___x_1139_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1138_, v___x_1137_, v___x_1136_);
return v___x_1139_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__45(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___f_1141_; lean_object* v___f_1142_; lean_object* v___x_1143_; 
v___x_1140_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__44, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__44_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__44);
v___f_1141_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6));
v___f_1142_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__34));
v___x_1143_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1142_, v___f_1141_, v___x_1140_);
return v___x_1143_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__48(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___f_1150_; 
v___x_1148_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__36));
v___x_1149_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_1150_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1150_, 0, v___x_1149_);
lean_closure_set(v___f_1150_, 1, v___x_1148_);
return v___f_1150_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__49(void){
_start:
{
lean_object* v___f_1151_; lean_object* v___f_1152_; lean_object* v___f_1153_; 
v___f_1151_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6));
v___f_1152_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__48, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__48_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__48);
v___f_1153_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1153_, 0, v___f_1152_);
lean_closure_set(v___f_1153_, 1, v___f_1151_);
return v___f_1153_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__50(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___f_1155_; lean_object* v___f_1156_; 
v___x_1154_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__36));
v___f_1155_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__49, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__49_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__49);
v___f_1156_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1156_, 0, v___f_1155_);
lean_closure_set(v___f_1156_, 1, v___x_1154_);
return v___f_1156_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__51(void){
_start:
{
lean_object* v___f_1157_; lean_object* v___f_1158_; lean_object* v___f_1159_; 
v___f_1157_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6));
v___f_1158_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__50, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__50_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__50);
v___f_1159_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1159_, 0, v___f_1158_);
lean_closure_set(v___f_1159_, 1, v___f_1157_);
return v___f_1159_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__52(void){
_start:
{
lean_object* v___f_1160_; lean_object* v___f_1161_; lean_object* v___f_1162_; 
v___f_1160_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6));
v___f_1161_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__51, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__51_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__51);
v___f_1162_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1162_, 0, v___f_1161_);
lean_closure_set(v___f_1162_, 1, v___f_1160_);
return v___f_1162_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__53(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___f_1164_; lean_object* v___f_1165_; 
v___x_1163_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__36));
v___f_1164_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__52, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__52_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__52);
v___f_1165_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1165_, 0, v___f_1164_);
lean_closure_set(v___f_1165_, 1, v___x_1163_);
return v___f_1165_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__54(void){
_start:
{
lean_object* v___f_1166_; lean_object* v___f_1167_; lean_object* v___f_1168_; 
v___f_1166_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6));
v___f_1167_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__53, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__53_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__53);
v___f_1168_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1168_, 0, v___f_1167_);
lean_closure_set(v___f_1168_, 1, v___f_1166_);
return v___f_1168_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM(void){
_start:
{
lean_object* v___x_1169_; lean_object* v_toApplicative_1170_; lean_object* v_toFunctor_1171_; lean_object* v_toSeq_1172_; lean_object* v_toSeqLeft_1173_; lean_object* v_toSeqRight_1174_; lean_object* v___f_1175_; lean_object* v___f_1176_; lean_object* v___f_1177_; lean_object* v___f_1178_; lean_object* v___x_1179_; lean_object* v___f_1180_; lean_object* v___f_1181_; lean_object* v___f_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v_toApplicative_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1230_; 
v___x_1169_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__1);
v_toApplicative_1170_ = lean_ctor_get(v___x_1169_, 0);
v_toFunctor_1171_ = lean_ctor_get(v_toApplicative_1170_, 0);
v_toSeq_1172_ = lean_ctor_get(v_toApplicative_1170_, 2);
v_toSeqLeft_1173_ = lean_ctor_get(v_toApplicative_1170_, 3);
v_toSeqRight_1174_ = lean_ctor_get(v_toApplicative_1170_, 4);
v___f_1175_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__2));
v___f_1176_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__3));
lean_inc_ref_n(v_toFunctor_1171_, 2);
v___f_1177_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1177_, 0, v_toFunctor_1171_);
v___f_1178_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1178_, 0, v_toFunctor_1171_);
v___x_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___f_1177_);
lean_ctor_set(v___x_1179_, 1, v___f_1178_);
lean_inc(v_toSeqRight_1174_);
v___f_1180_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1180_, 0, v_toSeqRight_1174_);
lean_inc(v_toSeqLeft_1173_);
v___f_1181_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1181_, 0, v_toSeqLeft_1173_);
lean_inc(v_toSeq_1172_);
v___f_1182_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1182_, 0, v_toSeq_1172_);
v___x_1183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1179_);
lean_ctor_set(v___x_1183_, 1, v___f_1175_);
lean_ctor_set(v___x_1183_, 2, v___f_1182_);
lean_ctor_set(v___x_1183_, 3, v___f_1181_);
lean_ctor_set(v___x_1183_, 4, v___f_1180_);
v___x_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
lean_ctor_set(v___x_1184_, 1, v___f_1176_);
v___x_1185_ = l_StateRefT_x27_instMonad___redArg(v___x_1184_);
v_toApplicative_1186_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; 
v_unused_1231_ = lean_ctor_get(v___x_1185_, 1);
lean_dec(v_unused_1231_);
v___x_1188_ = v___x_1185_;
v_isShared_1189_ = v_isSharedCheck_1230_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_toApplicative_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1230_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v_toFunctor_1190_; lean_object* v_toSeq_1191_; lean_object* v_toSeqLeft_1192_; lean_object* v_toSeqRight_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1228_; 
v_toFunctor_1190_ = lean_ctor_get(v_toApplicative_1186_, 0);
v_toSeq_1191_ = lean_ctor_get(v_toApplicative_1186_, 2);
v_toSeqLeft_1192_ = lean_ctor_get(v_toApplicative_1186_, 3);
v_toSeqRight_1193_ = lean_ctor_get(v_toApplicative_1186_, 4);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_toApplicative_1186_);
if (v_isSharedCheck_1228_ == 0)
{
lean_object* v_unused_1229_; 
v_unused_1229_ = lean_ctor_get(v_toApplicative_1186_, 1);
lean_dec(v_unused_1229_);
v___x_1195_ = v_toApplicative_1186_;
v_isShared_1196_ = v_isSharedCheck_1228_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_toSeqRight_1193_);
lean_inc(v_toSeqLeft_1192_);
lean_inc(v_toSeq_1191_);
lean_inc(v_toFunctor_1190_);
lean_dec(v_toApplicative_1186_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1228_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___f_1197_; lean_object* v___f_1198_; lean_object* v___f_1199_; lean_object* v___f_1200_; lean_object* v___x_1201_; lean_object* v___f_1202_; lean_object* v___f_1203_; lean_object* v___f_1204_; lean_object* v___x_1206_; 
v___f_1197_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__4));
v___f_1198_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__5));
lean_inc_ref(v_toFunctor_1190_);
v___f_1199_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1199_, 0, v_toFunctor_1190_);
v___f_1200_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1200_, 0, v_toFunctor_1190_);
v___x_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___f_1199_);
lean_ctor_set(v___x_1201_, 1, v___f_1200_);
v___f_1202_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1202_, 0, v_toSeqRight_1193_);
v___f_1203_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1203_, 0, v_toSeqLeft_1192_);
v___f_1204_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1204_, 0, v_toSeq_1191_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 4, v___f_1202_);
lean_ctor_set(v___x_1195_, 3, v___f_1203_);
lean_ctor_set(v___x_1195_, 2, v___f_1204_);
lean_ctor_set(v___x_1195_, 1, v___f_1197_);
lean_ctor_set(v___x_1195_, 0, v___x_1201_);
v___x_1206_ = v___x_1195_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1201_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v___f_1197_);
lean_ctor_set(v_reuseFailAlloc_1227_, 2, v___f_1204_);
lean_ctor_set(v_reuseFailAlloc_1227_, 3, v___f_1203_);
lean_ctor_set(v_reuseFailAlloc_1227_, 4, v___f_1202_);
v___x_1206_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1208_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 1, v___f_1198_);
lean_ctor_set(v___x_1188_, 0, v___x_1206_);
v___x_1208_ = v___x_1188_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v___f_1198_);
v___x_1208_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v_toMonadRef_1219_; lean_object* v___f_1220_; lean_object* v___f_1221_; lean_object* v___f_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___f_1225_; 
v___x_1209_ = l_StateRefT_x27_instMonad___redArg(v___x_1208_);
v___x_1210_ = l_ReaderT_instMonad___redArg(v___x_1209_);
v___x_1211_ = l_StateRefT_x27_instMonad___redArg(v___x_1210_);
v___x_1212_ = l_ReaderT_instMonad___redArg(v___x_1211_);
v___x_1213_ = l_ReaderT_instMonad___redArg(v___x_1212_);
v___x_1214_ = l_StateRefT_x27_instMonad___redArg(v___x_1213_);
v___x_1215_ = l_ReaderT_instMonad___redArg(v___x_1214_);
v___x_1216_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM;
v___x_1217_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__33, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__33_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__33);
v___x_1218_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__45, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__45_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__45);
v_toMonadRef_1219_ = lean_ctor_get(v___x_1218_, 0);
v___f_1220_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__47));
v___f_1221_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___closed__0));
v___f_1222_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__54, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__54_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__54);
lean_inc_ref(v___x_1215_);
v___x_1223_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1222_, v___x_1215_);
lean_inc_ref(v_toMonadRef_1219_);
v___x_1224_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1217_);
lean_ctor_set(v___x_1224_, 1, v_toMonadRef_1219_);
lean_ctor_set(v___x_1224_, 2, v___x_1223_);
v___f_1225_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0___boxed), 18, 5);
lean_closure_set(v___f_1225_, 0, v___x_1215_);
lean_closure_set(v___f_1225_, 1, v___x_1224_);
lean_closure_set(v___f_1225_, 2, v___f_1220_);
lean_closure_set(v___f_1225_, 3, v___x_1216_);
lean_closure_set(v___f_1225_, 4, v___f_1221_);
return v___f_1225_;
}
}
}
}
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM = _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM);
l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM = _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM);
l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM = _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM(builtin);
}
#ifdef __cplusplus
}
#endif
