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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run___redArg(lean_object* v_semiringId_1_, lean_object* v_x_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
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
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run___redArg_0interp(lean_interpreter_value* stack)
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
v_res_15_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run___redArg(v_semiringId_1_, v_x_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
stack->m_obj
 = v_res_15_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run___redArg___boxed(lean_object* v_semiringId_16_, lean_object* v_x_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run___redArg(v_semiringId_16_, v_x_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_, v_a_27_);
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
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run(lean_object* v_00_u03b1_30_, lean_object* v_semiringId_31_, lean_object* v_x_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_){
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
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run_0interp(lean_interpreter_value* stack)
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
v_res_45_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run(lean_box(0), v_semiringId_31_, v_x_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run___boxed(lean_object* v_00_u03b1_46_, lean_object* v_semiringId_47_, lean_object* v_x_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run(v_00_u03b1_46_, v_semiringId_47_, v_x_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_);
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
lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__0(lean_object* v_e_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Meta_Sym_canon(v_e_61_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_);
if (lean_obj_tag(v___x_74_) == 0)
{
lean_object* v_a_75_; lean_object* v___x_76_; 
v_a_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc(v_a_75_);
lean_dec_ref_known(v___x_74_, 1);
v___x_76_ = l_Lean_Meta_Sym_shareCommon(v_a_75_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_);
return v___x_76_;
}
else
{
return v___x_74_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_61_ = stack[0].m_obj;
lean_object* v___y_62_ = stack[1].m_obj;
lean_object* v___y_63_ = stack[2].m_obj;
lean_object* v___y_64_ = stack[3].m_obj;
lean_object* v___y_65_ = stack[4].m_obj;
lean_object* v___y_66_ = stack[5].m_obj;
lean_object* v___y_67_ = stack[6].m_obj;
lean_object* v___y_68_ = stack[7].m_obj;
lean_object* v___y_69_ = stack[8].m_obj;
lean_object* v___y_70_ = stack[9].m_obj;
lean_object* v___y_71_ = stack[10].m_obj;
lean_object* v___y_72_ = stack[11].m_obj;
lean_object* v_res_77_;
v_res_77_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__0(v_e_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_);
stack->m_obj
 = v_res_77_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__0___boxed(lean_object* v_e_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__0(v_e_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec(v___y_80_);
lean_dec(v___y_79_);
return v_res_91_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__1(lean_object* v_e_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_e_92_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
return v___x_105_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_92_ = stack[0].m_obj;
lean_object* v___y_93_ = stack[1].m_obj;
lean_object* v___y_94_ = stack[2].m_obj;
lean_object* v___y_95_ = stack[3].m_obj;
lean_object* v___y_96_ = stack[4].m_obj;
lean_object* v___y_97_ = stack[5].m_obj;
lean_object* v___y_98_ = stack[6].m_obj;
lean_object* v___y_99_ = stack[7].m_obj;
lean_object* v___y_100_ = stack[8].m_obj;
lean_object* v___y_101_ = stack[9].m_obj;
lean_object* v___y_102_ = stack[10].m_obj;
lean_object* v___y_103_ = stack[11].m_obj;
lean_object* v_res_106_;
v_res_106_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__1(v_e_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
stack->m_obj
 = v_res_106_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__1___boxed(lean_object* v_e_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__1(v_e_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_);
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
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0_spec__0(lean_object* v_msgData_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v___x_133_; lean_object* v_env_134_; uint8_t v___x_135_; lean_object* v_env_136_; lean_object* v___x_137_; lean_object* v_toCold_138_; lean_object* v_mctx_139_; lean_object* v_lctx_140_; lean_object* v_options_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_133_ = lean_st_ref_get(v___y_131_);
v_env_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc_ref(v_env_134_);
lean_dec(v___x_133_);
v___x_135_ = 0;
v_env_136_ = l_Lean_Environment_setRecordingDeps(v_env_134_, v___x_135_);
v___x_137_ = lean_st_ref_get(v___y_129_);
v_toCold_138_ = lean_ctor_get(v___y_130_, 0);
v_mctx_139_ = lean_ctor_get(v___x_137_, 0);
lean_inc_ref(v_mctx_139_);
lean_dec(v___x_137_);
v_lctx_140_ = lean_ctor_get(v___y_128_, 2);
v_options_141_ = lean_ctor_get(v_toCold_138_, 2);
lean_inc_ref(v_options_141_);
lean_inc_ref(v_lctx_140_);
v___x_142_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_142_, 0, v_env_136_);
lean_ctor_set(v___x_142_, 1, v_mctx_139_);
lean_ctor_set(v___x_142_, 2, v_lctx_140_);
lean_ctor_set(v___x_142_, 3, v_options_141_);
v___x_143_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v_msgData_127_);
v___x_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_127_ = stack[0].m_obj;
lean_object* v___y_128_ = stack[1].m_obj;
lean_object* v___y_129_ = stack[2].m_obj;
lean_object* v___y_130_ = stack[3].m_obj;
lean_object* v___y_131_ = stack[4].m_obj;
lean_object* v_res_145_;
v_res_145_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0_spec__0(v_msgData_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_);
stack->m_obj
 = v_res_145_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0_spec__0___boxed(lean_object* v_msgData_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0_spec__0(v_msgData_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
return v_res_152_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg(lean_object* v_msg_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_ref_159_; lean_object* v___x_160_; lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_169_; 
v_ref_159_ = lean_ctor_get(v___y_156_, 2);
v___x_160_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0_spec__0(v_msg_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
v_a_161_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_169_ == 0)
{
v___x_163_ = v___x_160_;
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_160_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_165_; lean_object* v___x_167_; 
lean_inc(v_ref_159_);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v_ref_159_);
lean_ctor_set(v___x_165_, 1, v_a_161_);
if (v_isShared_164_ == 0)
{
lean_ctor_set_tag(v___x_163_, 1);
lean_ctor_set(v___x_163_, 0, v___x_165_);
v___x_167_ = v___x_163_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_153_ = stack[0].m_obj;
lean_object* v___y_154_ = stack[1].m_obj;
lean_object* v___y_155_ = stack[2].m_obj;
lean_object* v___y_156_ = stack[3].m_obj;
lean_object* v___y_157_ = stack[4].m_obj;
lean_object* v_res_170_;
v_res_170_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg(v_msg_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
stack->m_obj
 = v_res_170_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg___boxed(lean_object* v_msg_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg(v_msg_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
return v_res_177_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__1(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__0));
v___x_180_ = l_Lean_stringToMessageData(v___x_179_);
return v___x_180_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring(lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_187_, v_a_190_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_207_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_207_ == 0)
{
v___x_196_ = v___x_193_;
v_isShared_197_ = v_isSharedCheck_207_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_193_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_207_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v_ncSemirings_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v_ncSemirings_198_ = lean_ctor_get(v_a_194_, 4);
lean_inc_ref(v_ncSemirings_198_);
lean_dec(v_a_194_);
v___x_199_ = lean_array_get_size(v_ncSemirings_198_);
v___x_200_ = lean_nat_dec_lt(v_a_181_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_dec_ref(v_ncSemirings_198_);
lean_del_object(v___x_196_);
v___x_201_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__1);
v___x_202_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg(v___x_201_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
return v___x_202_;
}
else
{
lean_object* v___x_203_; lean_object* v___x_205_; 
v___x_203_ = lean_array_fget(v_ncSemirings_198_, v_a_181_);
lean_dec_ref(v_ncSemirings_198_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_203_);
v___x_205_ = v___x_196_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_203_);
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
else
{
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
v_a_208_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_215_ == 0)
{
v___x_210_ = v___x_193_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_193_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_a_208_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_181_ = stack[0].m_obj;
lean_object* v_a_182_ = stack[1].m_obj;
lean_object* v_a_183_ = stack[2].m_obj;
lean_object* v_a_184_ = stack[3].m_obj;
lean_object* v_a_185_ = stack[4].m_obj;
lean_object* v_a_186_ = stack[5].m_obj;
lean_object* v_a_187_ = stack[6].m_obj;
lean_object* v_a_188_ = stack[7].m_obj;
lean_object* v_a_189_ = stack[8].m_obj;
lean_object* v_a_190_ = stack[9].m_obj;
lean_object* v_a_191_ = stack[10].m_obj;
lean_object* v_res_216_;
v_res_216_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring(v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
stack->m_obj
 = v_res_216_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___boxed(lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring(v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec(v_a_218_);
lean_dec(v_a_217_);
return v_res_229_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0(lean_object* v_00_u03b1_230_, lean_object* v_msg_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg(v_msg_231_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
return v___x_244_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_231_ = stack[1].m_obj;
lean_object* v___y_232_ = stack[2].m_obj;
lean_object* v___y_233_ = stack[3].m_obj;
lean_object* v___y_234_ = stack[4].m_obj;
lean_object* v___y_235_ = stack[5].m_obj;
lean_object* v___y_236_ = stack[6].m_obj;
lean_object* v___y_237_ = stack[7].m_obj;
lean_object* v___y_238_ = stack[8].m_obj;
lean_object* v___y_239_ = stack[9].m_obj;
lean_object* v___y_240_ = stack[10].m_obj;
lean_object* v___y_241_ = stack[11].m_obj;
lean_object* v___y_242_ = stack[12].m_obj;
lean_object* v_res_245_;
v_res_245_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0(lean_box(0), v_msg_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
stack->m_obj
 = v_res_245_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___boxed(lean_object* v_00_u03b1_246_, lean_object* v_msg_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0(v_00_u03b1_246_, v_msg_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
lean_dec(v___y_250_);
lean_dec(v___y_249_);
lean_dec(v___y_248_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___lam__0(lean_object* v_a_261_, lean_object* v_f_262_, lean_object* v_s_263_){
_start:
{
lean_object* v_exp_264_; lean_object* v_rings_265_; lean_object* v_semirings_266_; lean_object* v_ncRings_267_; lean_object* v_ncSemirings_268_; lean_object* v_typeClassify_269_; lean_object* v_orders_270_; lean_object* v_typeOrderClassify_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v_exp_264_ = lean_ctor_get(v_s_263_, 0);
v_rings_265_ = lean_ctor_get(v_s_263_, 1);
v_semirings_266_ = lean_ctor_get(v_s_263_, 2);
v_ncRings_267_ = lean_ctor_get(v_s_263_, 3);
v_ncSemirings_268_ = lean_ctor_get(v_s_263_, 4);
v_typeClassify_269_ = lean_ctor_get(v_s_263_, 5);
v_orders_270_ = lean_ctor_get(v_s_263_, 6);
v_typeOrderClassify_271_ = lean_ctor_get(v_s_263_, 7);
v___x_272_ = lean_array_get_size(v_ncSemirings_268_);
v___x_273_ = lean_nat_dec_lt(v_a_261_, v___x_272_);
if (v___x_273_ == 0)
{
lean_dec_ref(v_f_262_);
return v_s_263_;
}
else
{
lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_285_; 
lean_inc_ref(v_typeOrderClassify_271_);
lean_inc_ref(v_orders_270_);
lean_inc_ref(v_typeClassify_269_);
lean_inc_ref(v_ncSemirings_268_);
lean_inc_ref(v_ncRings_267_);
lean_inc_ref(v_semirings_266_);
lean_inc_ref(v_rings_265_);
lean_inc(v_exp_264_);
v_isSharedCheck_285_ = !lean_is_exclusive(v_s_263_);
if (v_isSharedCheck_285_ == 0)
{
lean_object* v_unused_286_; lean_object* v_unused_287_; lean_object* v_unused_288_; lean_object* v_unused_289_; lean_object* v_unused_290_; lean_object* v_unused_291_; lean_object* v_unused_292_; lean_object* v_unused_293_; 
v_unused_286_ = lean_ctor_get(v_s_263_, 7);
lean_dec(v_unused_286_);
v_unused_287_ = lean_ctor_get(v_s_263_, 6);
lean_dec(v_unused_287_);
v_unused_288_ = lean_ctor_get(v_s_263_, 5);
lean_dec(v_unused_288_);
v_unused_289_ = lean_ctor_get(v_s_263_, 4);
lean_dec(v_unused_289_);
v_unused_290_ = lean_ctor_get(v_s_263_, 3);
lean_dec(v_unused_290_);
v_unused_291_ = lean_ctor_get(v_s_263_, 2);
lean_dec(v_unused_291_);
v_unused_292_ = lean_ctor_get(v_s_263_, 1);
lean_dec(v_unused_292_);
v_unused_293_ = lean_ctor_get(v_s_263_, 0);
lean_dec(v_unused_293_);
v___x_275_ = v_s_263_;
v_isShared_276_ = v_isSharedCheck_285_;
goto v_resetjp_274_;
}
else
{
lean_dec(v_s_263_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_285_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v_v_277_; lean_object* v___x_278_; lean_object* v_xs_x27_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_283_; 
v_v_277_ = lean_array_fget(v_ncSemirings_268_, v_a_261_);
v___x_278_ = lean_box(0);
v_xs_x27_279_ = lean_array_fset(v_ncSemirings_268_, v_a_261_, v___x_278_);
v___x_280_ = lean_apply_1(v_f_262_, v_v_277_);
v___x_281_ = lean_array_fset(v_xs_x27_279_, v_a_261_, v___x_280_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 4, v___x_281_);
v___x_283_ = v___x_275_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_exp_264_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v_rings_265_);
lean_ctor_set(v_reuseFailAlloc_284_, 2, v_semirings_266_);
lean_ctor_set(v_reuseFailAlloc_284_, 3, v_ncRings_267_);
lean_ctor_set(v_reuseFailAlloc_284_, 4, v___x_281_);
lean_ctor_set(v_reuseFailAlloc_284_, 5, v_typeClassify_269_);
lean_ctor_set(v_reuseFailAlloc_284_, 6, v_orders_270_);
lean_ctor_set(v_reuseFailAlloc_284_, 7, v_typeOrderClassify_271_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___lam__0___boxed(lean_object* v_a_294_, lean_object* v_f_295_, lean_object* v_s_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___lam__0(v_a_294_, v_f_295_, v_s_296_);
lean_dec(v_a_294_);
return v_res_297_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg(lean_object* v_f_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v___f_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
lean_inc(v_a_299_);
v___f_302_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_302_, 0, v_a_299_);
lean_closure_set(v___f_302_, 1, v_f_298_);
v___x_303_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_304_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_303_, v___f_302_, v_a_300_);
return v___x_304_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_298_ = stack[0].m_obj;
lean_object* v_a_299_ = stack[1].m_obj;
lean_object* v_a_300_ = stack[2].m_obj;
lean_object* v_res_305_;
v_res_305_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg(v_f_298_, v_a_299_, v_a_300_);
stack->m_obj
 = v_res_305_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___boxed(lean_object* v_f_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg(v_f_306_, v_a_307_, v_a_308_);
lean_dec(v_a_308_);
lean_dec(v_a_307_);
return v_res_310_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring(lean_object* v_f_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg(v_f_311_, v_a_312_, v_a_318_);
return v___x_324_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_311_ = stack[0].m_obj;
lean_object* v_a_312_ = stack[1].m_obj;
lean_object* v_a_313_ = stack[2].m_obj;
lean_object* v_a_314_ = stack[3].m_obj;
lean_object* v_a_315_ = stack[4].m_obj;
lean_object* v_a_316_ = stack[5].m_obj;
lean_object* v_a_317_ = stack[6].m_obj;
lean_object* v_a_318_ = stack[7].m_obj;
lean_object* v_a_319_ = stack[8].m_obj;
lean_object* v_a_320_ = stack[9].m_obj;
lean_object* v_a_321_ = stack[10].m_obj;
lean_object* v_a_322_ = stack[11].m_obj;
lean_object* v_res_325_;
v_res_325_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring(v_f_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
stack->m_obj
 = v_res_325_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___boxed(lean_object* v_f_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring(v_f_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec(v_a_328_);
lean_dec(v_a_327_);
return v_res_339_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__1(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__0));
v___x_342_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___boxed), 12, 0);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___x_341_);
return v___x_343_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM(void){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__1);
return v___x_344_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState___redArg(lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_346_, v_a_347_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_358_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_358_ == 0)
{
v___x_352_ = v___x_349_;
v_isShared_353_ = v_isSharedCheck_358_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_349_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_358_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_354_ = l_Lean_Meta_Grind_Arith_CommRing_State_getNCSemiring(v_a_350_, v_a_345_);
lean_dec(v_a_350_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v___x_354_);
v___x_356_ = v___x_352_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_354_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
v_a_359_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_349_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_349_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_345_ = stack[0].m_obj;
lean_object* v_a_346_ = stack[1].m_obj;
lean_object* v_a_347_ = stack[2].m_obj;
lean_object* v_res_367_;
v_res_367_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState___redArg(v_a_345_, v_a_346_, v_a_347_);
stack->m_obj
 = v_res_367_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState___redArg___boxed(lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState___redArg(v_a_368_, v_a_369_, v_a_370_);
lean_dec_ref(v_a_370_);
lean_dec(v_a_369_);
lean_dec(v_a_368_);
return v_res_372_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState(lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState___redArg(v_a_373_, v_a_374_, v_a_382_);
return v___x_385_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_373_ = stack[0].m_obj;
lean_object* v_a_374_ = stack[1].m_obj;
lean_object* v_a_375_ = stack[2].m_obj;
lean_object* v_a_376_ = stack[3].m_obj;
lean_object* v_a_377_ = stack[4].m_obj;
lean_object* v_a_378_ = stack[5].m_obj;
lean_object* v_a_379_ = stack[6].m_obj;
lean_object* v_a_380_ = stack[7].m_obj;
lean_object* v_a_381_ = stack[8].m_obj;
lean_object* v_a_382_ = stack[9].m_obj;
lean_object* v_a_383_ = stack[10].m_obj;
lean_object* v_res_386_;
v_res_386_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState(v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_);
stack->m_obj
 = v_res_386_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState___boxed(lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState(v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
lean_dec(v_a_393_);
lean_dec_ref(v_a_392_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec(v_a_388_);
lean_dec(v_a_387_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg___lam__0(lean_object* v_a_400_, lean_object* v_f_401_, lean_object* v_s_402_){
_start:
{
lean_object* v_rings_403_; lean_object* v_exprToRingId_404_; lean_object* v_semirings_405_; lean_object* v_exprToSemiringId_406_; lean_object* v_ncRings_407_; lean_object* v_exprToNCRingId_408_; lean_object* v_ncSemirings_409_; lean_object* v_exprToNCSemiringId_410_; lean_object* v_steps_411_; uint8_t v_reportedMaxDegreeIssue_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_433_; 
v_rings_403_ = lean_ctor_get(v_s_402_, 0);
v_exprToRingId_404_ = lean_ctor_get(v_s_402_, 1);
v_semirings_405_ = lean_ctor_get(v_s_402_, 2);
v_exprToSemiringId_406_ = lean_ctor_get(v_s_402_, 3);
v_ncRings_407_ = lean_ctor_get(v_s_402_, 4);
v_exprToNCRingId_408_ = lean_ctor_get(v_s_402_, 5);
v_ncSemirings_409_ = lean_ctor_get(v_s_402_, 6);
v_exprToNCSemiringId_410_ = lean_ctor_get(v_s_402_, 7);
v_steps_411_ = lean_ctor_get(v_s_402_, 8);
v_reportedMaxDegreeIssue_412_ = lean_ctor_get_uint8(v_s_402_, sizeof(void*)*9);
v_isSharedCheck_433_ = !lean_is_exclusive(v_s_402_);
if (v_isSharedCheck_433_ == 0)
{
v___x_414_ = v_s_402_;
v_isShared_415_ = v_isSharedCheck_433_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_steps_411_);
lean_inc(v_exprToNCSemiringId_410_);
lean_inc(v_ncSemirings_409_);
lean_inc(v_exprToNCRingId_408_);
lean_inc(v_ncRings_407_);
lean_inc(v_exprToSemiringId_406_);
lean_inc(v_semirings_405_);
lean_inc(v_exprToRingId_404_);
lean_inc(v_rings_403_);
lean_dec(v_s_402_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_433_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_416_ = lean_unsigned_to_nat(1u);
v___x_417_ = lean_nat_add(v_a_400_, v___x_416_);
v___x_418_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default;
v___x_419_ = l_Array_rightpad___redArg(v___x_417_, v___x_418_, v_ncSemirings_409_);
lean_dec(v___x_417_);
v___x_420_ = lean_array_get_size(v___x_419_);
v___x_421_ = lean_nat_dec_lt(v_a_400_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_423_; 
lean_dec_ref(v_f_401_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 6, v___x_419_);
v___x_423_ = v___x_414_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_rings_403_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_exprToRingId_404_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_semirings_405_);
lean_ctor_set(v_reuseFailAlloc_424_, 3, v_exprToSemiringId_406_);
lean_ctor_set(v_reuseFailAlloc_424_, 4, v_ncRings_407_);
lean_ctor_set(v_reuseFailAlloc_424_, 5, v_exprToNCRingId_408_);
lean_ctor_set(v_reuseFailAlloc_424_, 6, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_424_, 7, v_exprToNCSemiringId_410_);
lean_ctor_set(v_reuseFailAlloc_424_, 8, v_steps_411_);
lean_ctor_set_uint8(v_reuseFailAlloc_424_, sizeof(void*)*9, v_reportedMaxDegreeIssue_412_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
else
{
lean_object* v_v_425_; lean_object* v___x_426_; lean_object* v_xs_x27_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
v_v_425_ = lean_array_fget(v___x_419_, v_a_400_);
v___x_426_ = lean_box(0);
v_xs_x27_427_ = lean_array_fset(v___x_419_, v_a_400_, v___x_426_);
v___x_428_ = lean_apply_1(v_f_401_, v_v_425_);
v___x_429_ = lean_array_fset(v_xs_x27_427_, v_a_400_, v___x_428_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 6, v___x_429_);
v___x_431_ = v___x_414_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_rings_403_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_exprToRingId_404_);
lean_ctor_set(v_reuseFailAlloc_432_, 2, v_semirings_405_);
lean_ctor_set(v_reuseFailAlloc_432_, 3, v_exprToSemiringId_406_);
lean_ctor_set(v_reuseFailAlloc_432_, 4, v_ncRings_407_);
lean_ctor_set(v_reuseFailAlloc_432_, 5, v_exprToNCRingId_408_);
lean_ctor_set(v_reuseFailAlloc_432_, 6, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_432_, 7, v_exprToNCSemiringId_410_);
lean_ctor_set(v_reuseFailAlloc_432_, 8, v_steps_411_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, sizeof(void*)*9, v_reportedMaxDegreeIssue_412_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg___lam__0___boxed(lean_object* v_a_434_, lean_object* v_f_435_, lean_object* v_s_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg___lam__0(v_a_434_, v_f_435_, v_s_436_);
lean_dec(v_a_434_);
return v_res_437_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg(lean_object* v_f_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
lean_object* v___f_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
lean_inc(v_a_439_);
v___f_442_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_442_, 0, v_a_439_);
lean_closure_set(v___f_442_, 1, v_f_438_);
v___x_443_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_444_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_443_, v___f_442_, v_a_440_);
return v___x_444_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_438_ = stack[0].m_obj;
lean_object* v_a_439_ = stack[1].m_obj;
lean_object* v_a_440_ = stack[2].m_obj;
lean_object* v_res_445_;
v_res_445_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg(v_f_438_, v_a_439_, v_a_440_);
stack->m_obj
 = v_res_445_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg___boxed(lean_object* v_f_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg(v_f_446_, v_a_447_, v_a_448_);
lean_dec(v_a_448_);
lean_dec(v_a_447_);
return v_res_450_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState(lean_object* v_f_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg(v_f_451_, v_a_452_, v_a_453_);
return v___x_464_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_451_ = stack[0].m_obj;
lean_object* v_a_452_ = stack[1].m_obj;
lean_object* v_a_453_ = stack[2].m_obj;
lean_object* v_a_454_ = stack[3].m_obj;
lean_object* v_a_455_ = stack[4].m_obj;
lean_object* v_a_456_ = stack[5].m_obj;
lean_object* v_a_457_ = stack[6].m_obj;
lean_object* v_a_458_ = stack[7].m_obj;
lean_object* v_a_459_ = stack[8].m_obj;
lean_object* v_a_460_ = stack[9].m_obj;
lean_object* v_a_461_ = stack[10].m_obj;
lean_object* v_a_462_ = stack[11].m_obj;
lean_object* v_res_465_;
v_res_465_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState(v_f_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
stack->m_obj
 = v_res_465_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___boxed(lean_object* v_f_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState(v_f_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
lean_dec(v_a_475_);
lean_dec_ref(v_a_474_);
lean_dec(v_a_473_);
lean_dec_ref(v_a_472_);
lean_dec(v_a_471_);
lean_dec_ref(v_a_470_);
lean_dec(v_a_469_);
lean_dec(v_a_468_);
lean_dec(v_a_467_);
return v_res_479_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM___closed__1(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_481_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM___closed__0));
v___x_482_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState___boxed), 12, 0);
v___x_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set(v___x_483_, 1, v___x_481_);
return v___x_483_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM(void){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM___closed__1);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_485_, lean_object* v_vals_486_, lean_object* v_i_487_, lean_object* v_k_488_){
_start:
{
lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_489_ = lean_array_get_size(v_keys_485_);
v___x_490_ = lean_nat_dec_lt(v_i_487_, v___x_489_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; 
lean_dec(v_i_487_);
v___x_491_ = lean_box(0);
return v___x_491_;
}
else
{
lean_object* v_k_x27_492_; size_t v___x_493_; size_t v___x_494_; uint8_t v___x_495_; 
v_k_x27_492_ = lean_array_fget_borrowed(v_keys_485_, v_i_487_);
v___x_493_ = lean_ptr_addr(v_k_488_);
v___x_494_ = lean_ptr_addr(v_k_x27_492_);
v___x_495_ = lean_usize_dec_eq(v___x_493_, v___x_494_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_unsigned_to_nat(1u);
v___x_497_ = lean_nat_add(v_i_487_, v___x_496_);
lean_dec(v_i_487_);
v_i_487_ = v___x_497_;
goto _start;
}
else
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_array_fget_borrowed(v_vals_486_, v_i_487_);
lean_dec(v_i_487_);
lean_inc(v___x_499_);
v___x_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
return v___x_500_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_501_, lean_object* v_vals_502_, lean_object* v_i_503_, lean_object* v_k_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_501_, v_vals_502_, v_i_503_, v_k_504_);
lean_dec_ref(v_k_504_);
lean_dec_ref(v_vals_502_);
lean_dec_ref(v_keys_501_);
return v_res_505_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg(lean_object* v_x_506_, size_t v_x_507_, lean_object* v_x_508_){
_start:
{
if (lean_obj_tag(v_x_506_) == 0)
{
lean_object* v_es_509_; lean_object* v___x_510_; size_t v___x_511_; size_t v___x_512_; lean_object* v_j_513_; lean_object* v___x_514_; 
v_es_509_ = lean_ctor_get(v_x_506_, 0);
v___x_510_ = lean_box(2);
v___x_511_ = ((size_t)31ULL);
v___x_512_ = lean_usize_land(v_x_507_, v___x_511_);
v_j_513_ = lean_usize_to_nat(v___x_512_);
v___x_514_ = lean_array_get_borrowed(v___x_510_, v_es_509_, v_j_513_);
lean_dec(v_j_513_);
switch(lean_obj_tag(v___x_514_))
{
case 0:
{
lean_object* v_key_515_; lean_object* v_val_516_; size_t v___x_517_; size_t v___x_518_; uint8_t v___x_519_; 
v_key_515_ = lean_ctor_get(v___x_514_, 0);
v_val_516_ = lean_ctor_get(v___x_514_, 1);
v___x_517_ = lean_ptr_addr(v_x_508_);
v___x_518_ = lean_ptr_addr(v_key_515_);
v___x_519_ = lean_usize_dec_eq(v___x_517_, v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; 
v___x_520_ = lean_box(0);
return v___x_520_;
}
else
{
lean_object* v___x_521_; 
lean_inc(v_val_516_);
v___x_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_521_, 0, v_val_516_);
return v___x_521_;
}
}
case 1:
{
lean_object* v_node_522_; size_t v___x_523_; size_t v___x_524_; 
v_node_522_ = lean_ctor_get(v___x_514_, 0);
v___x_523_ = ((size_t)5ULL);
v___x_524_ = lean_usize_shift_right(v_x_507_, v___x_523_);
v_x_506_ = v_node_522_;
v_x_507_ = v___x_524_;
goto _start;
}
default: 
{
lean_object* v___x_526_; 
v___x_526_ = lean_box(0);
return v___x_526_;
}
}
}
else
{
lean_object* v_ks_527_; lean_object* v_vs_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v_ks_527_ = lean_ctor_get(v_x_506_, 0);
v_vs_528_ = lean_ctor_get(v_x_506_, 1);
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_527_, v_vs_528_, v___x_529_, v_x_508_);
return v___x_530_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_506_ = stack[0].m_obj;
size_t v_x_507_ = stack[1].m_num;
lean_object* v_x_508_ = stack[2].m_obj;
lean_object* v_res_531_;
v_res_531_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg(v_x_506_, v_x_507_, v_x_508_);
stack->m_obj
 = v_res_531_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_532_, lean_object* v_x_533_, lean_object* v_x_534_){
_start:
{
size_t v_x_916__boxed_535_; lean_object* v_res_536_; 
v_x_916__boxed_535_ = lean_unbox_usize(v_x_533_);
lean_dec(v_x_533_);
v_res_536_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg(v_x_532_, v_x_916__boxed_535_, v_x_534_);
lean_dec_ref(v_x_534_);
lean_dec_ref(v_x_532_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg(lean_object* v_x_537_, lean_object* v_x_538_){
_start:
{
size_t v___x_539_; size_t v___x_540_; size_t v___x_541_; uint64_t v___x_542_; size_t v___x_543_; lean_object* v___x_544_; 
v___x_539_ = lean_ptr_addr(v_x_538_);
v___x_540_ = ((size_t)3ULL);
v___x_541_ = lean_usize_shift_right(v___x_539_, v___x_540_);
v___x_542_ = lean_usize_to_uint64(v___x_541_);
v___x_543_ = lean_uint64_to_usize(v___x_542_);
v___x_544_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg(v_x_537_, v___x_543_, v_x_538_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg___boxed(lean_object* v_x_545_, lean_object* v_x_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg(v_x_545_, v_x_546_);
lean_dec_ref(v_x_546_);
lean_dec_ref(v_x_545_);
return v_res_547_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg(lean_object* v_e_548_, lean_object* v_a_549_, lean_object* v_a_550_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_549_, v_a_550_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_562_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_562_ == 0)
{
v___x_555_ = v___x_552_;
v_isShared_556_ = v_isSharedCheck_562_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_552_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_562_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v_exprToNCSemiringId_557_; lean_object* v___x_558_; lean_object* v___x_560_; 
v_exprToNCSemiringId_557_ = lean_ctor_get(v_a_553_, 7);
lean_inc_ref(v_exprToNCSemiringId_557_);
lean_dec(v_a_553_);
v___x_558_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg(v_exprToNCSemiringId_557_, v_e_548_);
lean_dec_ref(v_exprToNCSemiringId_557_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v___x_558_);
v___x_560_ = v___x_555_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
v_a_563_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_552_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_552_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_548_ = stack[0].m_obj;
lean_object* v_a_549_ = stack[1].m_obj;
lean_object* v_a_550_ = stack[2].m_obj;
lean_object* v_res_571_;
v_res_571_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg(v_e_548_, v_a_549_, v_a_550_);
stack->m_obj
 = v_res_571_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg___boxed(lean_object* v_e_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg(v_e_572_, v_a_573_, v_a_574_);
lean_dec_ref(v_a_574_);
lean_dec(v_a_573_);
lean_dec_ref(v_e_572_);
return v_res_576_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f(lean_object* v_e_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg(v_e_577_, v_a_578_, v_a_586_);
return v___x_589_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_577_ = stack[0].m_obj;
lean_object* v_a_578_ = stack[1].m_obj;
lean_object* v_a_579_ = stack[2].m_obj;
lean_object* v_a_580_ = stack[3].m_obj;
lean_object* v_a_581_ = stack[4].m_obj;
lean_object* v_a_582_ = stack[5].m_obj;
lean_object* v_a_583_ = stack[6].m_obj;
lean_object* v_a_584_ = stack[7].m_obj;
lean_object* v_a_585_ = stack[8].m_obj;
lean_object* v_a_586_ = stack[9].m_obj;
lean_object* v_a_587_ = stack[10].m_obj;
lean_object* v_res_590_;
v_res_590_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f(v_e_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
stack->m_obj
 = v_res_590_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___boxed(lean_object* v_e_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f(v_e_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
lean_dec(v_a_597_);
lean_dec_ref(v_a_596_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
lean_dec(v_a_593_);
lean_dec(v_a_592_);
lean_dec_ref(v_e_591_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0(lean_object* v_00_u03b2_604_, lean_object* v_x_605_, lean_object* v_x_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg(v_x_605_, v_x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___boxed(lean_object* v_00_u03b2_608_, lean_object* v_x_609_, lean_object* v_x_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0(v_00_u03b2_608_, v_x_609_, v_x_610_);
lean_dec_ref(v_x_610_);
lean_dec_ref(v_x_609_);
return v_res_611_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_612_, lean_object* v_x_613_, size_t v_x_614_, lean_object* v_x_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg(v_x_613_, v_x_614_, v_x_615_);
return v___x_616_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_613_ = stack[1].m_obj;
size_t v_x_614_ = stack[2].m_num;
lean_object* v_x_615_ = stack[3].m_obj;
lean_object* v_res_617_;
v_res_617_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0(lean_box(0), v_x_613_, v_x_614_, v_x_615_);
stack->m_obj
 = v_res_617_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_618_, lean_object* v_x_619_, lean_object* v_x_620_, lean_object* v_x_621_){
_start:
{
size_t v_x_1102__boxed_622_; lean_object* v_res_623_; 
v_x_1102__boxed_622_ = lean_unbox_usize(v_x_620_);
lean_dec(v_x_620_);
v_res_623_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0(v_00_u03b2_618_, v_x_619_, v_x_1102__boxed_622_, v_x_621_);
lean_dec_ref(v_x_621_);
lean_dec_ref(v_x_619_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_624_, lean_object* v_keys_625_, lean_object* v_vals_626_, lean_object* v_heq_627_, lean_object* v_i_628_, lean_object* v_k_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_625_, v_vals_626_, v_i_628_, v_k_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_631_, lean_object* v_keys_632_, lean_object* v_vals_633_, lean_object* v_heq_634_, lean_object* v_i_635_, lean_object* v_k_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_631_, v_keys_632_, v_vals_633_, v_heq_634_, v_i_635_, v_k_636_);
lean_dec_ref(v_k_636_);
lean_dec_ref(v_vals_633_);
lean_dec_ref(v_keys_632_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_638_, lean_object* v_x_639_, lean_object* v_x_640_, lean_object* v_x_641_){
_start:
{
lean_object* v_ks_642_; lean_object* v_vs_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_669_; 
v_ks_642_ = lean_ctor_get(v_x_638_, 0);
v_vs_643_ = lean_ctor_get(v_x_638_, 1);
v_isSharedCheck_669_ = !lean_is_exclusive(v_x_638_);
if (v_isSharedCheck_669_ == 0)
{
v___x_645_ = v_x_638_;
v_isShared_646_ = v_isSharedCheck_669_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_vs_643_);
lean_inc(v_ks_642_);
lean_dec(v_x_638_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_669_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_647_ = lean_array_get_size(v_ks_642_);
v___x_648_ = lean_nat_dec_lt(v_x_639_, v___x_647_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_652_; 
lean_dec(v_x_639_);
v___x_649_ = lean_array_push(v_ks_642_, v_x_640_);
v___x_650_ = lean_array_push(v_vs_643_, v_x_641_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 1, v___x_650_);
lean_ctor_set(v___x_645_, 0, v___x_649_);
v___x_652_ = v___x_645_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
else
{
lean_object* v_k_x27_654_; size_t v___x_655_; size_t v___x_656_; uint8_t v___x_657_; 
v_k_x27_654_ = lean_array_fget_borrowed(v_ks_642_, v_x_639_);
v___x_655_ = lean_ptr_addr(v_x_640_);
v___x_656_ = lean_ptr_addr(v_k_x27_654_);
v___x_657_ = lean_usize_dec_eq(v___x_655_, v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_659_; 
if (v_isShared_646_ == 0)
{
v___x_659_ = v___x_645_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_ks_642_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_vs_643_);
v___x_659_ = v_reuseFailAlloc_663_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = lean_unsigned_to_nat(1u);
v___x_661_ = lean_nat_add(v_x_639_, v___x_660_);
lean_dec(v_x_639_);
v_x_638_ = v___x_659_;
v_x_639_ = v___x_661_;
goto _start;
}
}
else
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
v___x_664_ = lean_array_fset(v_ks_642_, v_x_639_, v_x_640_);
v___x_665_ = lean_array_fset(v_vs_643_, v_x_639_, v_x_641_);
lean_dec(v_x_639_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 1, v___x_665_);
lean_ctor_set(v___x_645_, 0, v___x_664_);
v___x_667_ = v___x_645_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_664_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_670_, lean_object* v_k_671_, lean_object* v_v_672_){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_670_, v___x_673_, v_k_671_, v_v_672_);
return v___x_674_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_675_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(lean_object* v_x_676_, size_t v_x_677_, size_t v_x_678_, lean_object* v_x_679_, lean_object* v_x_680_){
_start:
{
if (lean_obj_tag(v_x_676_) == 0)
{
lean_object* v_es_681_; size_t v___x_682_; size_t v___x_683_; lean_object* v_j_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v_es_681_ = lean_ctor_get(v_x_676_, 0);
v___x_682_ = ((size_t)31ULL);
v___x_683_ = lean_usize_land(v_x_677_, v___x_682_);
v_j_684_ = lean_usize_to_nat(v___x_683_);
v___x_685_ = lean_array_get_size(v_es_681_);
v___x_686_ = lean_nat_dec_lt(v_j_684_, v___x_685_);
if (v___x_686_ == 0)
{
lean_dec(v_j_684_);
lean_dec(v_x_680_);
lean_dec_ref(v_x_679_);
return v_x_676_;
}
else
{
lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_727_; 
lean_inc_ref(v_es_681_);
v_isSharedCheck_727_ = !lean_is_exclusive(v_x_676_);
if (v_isSharedCheck_727_ == 0)
{
lean_object* v_unused_728_; 
v_unused_728_ = lean_ctor_get(v_x_676_, 0);
lean_dec(v_unused_728_);
v___x_688_ = v_x_676_;
v_isShared_689_ = v_isSharedCheck_727_;
goto v_resetjp_687_;
}
else
{
lean_dec(v_x_676_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_727_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_v_690_; lean_object* v___x_691_; lean_object* v_xs_x27_692_; lean_object* v___y_694_; 
v_v_690_ = lean_array_fget(v_es_681_, v_j_684_);
v___x_691_ = lean_box(0);
v_xs_x27_692_ = lean_array_fset(v_es_681_, v_j_684_, v___x_691_);
switch(lean_obj_tag(v_v_690_))
{
case 0:
{
lean_object* v_key_699_; lean_object* v_val_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_712_; 
v_key_699_ = lean_ctor_get(v_v_690_, 0);
v_val_700_ = lean_ctor_get(v_v_690_, 1);
v_isSharedCheck_712_ = !lean_is_exclusive(v_v_690_);
if (v_isSharedCheck_712_ == 0)
{
v___x_702_ = v_v_690_;
v_isShared_703_ = v_isSharedCheck_712_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_val_700_);
lean_inc(v_key_699_);
lean_dec(v_v_690_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_712_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
size_t v___x_704_; size_t v___x_705_; uint8_t v___x_706_; 
v___x_704_ = lean_ptr_addr(v_x_679_);
v___x_705_ = lean_ptr_addr(v_key_699_);
v___x_706_ = lean_usize_dec_eq(v___x_704_, v___x_705_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; lean_object* v___x_708_; 
lean_del_object(v___x_702_);
v___x_707_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_699_, v_val_700_, v_x_679_, v_x_680_);
v___x_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
v___y_694_ = v___x_708_;
goto v___jp_693_;
}
else
{
lean_object* v___x_710_; 
lean_dec(v_val_700_);
lean_dec(v_key_699_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 1, v_x_680_);
lean_ctor_set(v___x_702_, 0, v_x_679_);
v___x_710_ = v___x_702_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_x_679_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_x_680_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
v___y_694_ = v___x_710_;
goto v___jp_693_;
}
}
}
}
case 1:
{
lean_object* v_node_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_725_; 
v_node_713_ = lean_ctor_get(v_v_690_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v_v_690_);
if (v_isSharedCheck_725_ == 0)
{
v___x_715_ = v_v_690_;
v_isShared_716_ = v_isSharedCheck_725_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_node_713_);
lean_dec(v_v_690_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_725_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
size_t v___x_717_; size_t v___x_718_; size_t v___x_719_; size_t v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
v___x_717_ = ((size_t)5ULL);
v___x_718_ = lean_usize_shift_right(v_x_677_, v___x_717_);
v___x_719_ = ((size_t)1ULL);
v___x_720_ = lean_usize_add(v_x_678_, v___x_719_);
v___x_721_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(v_node_713_, v___x_718_, v___x_720_, v_x_679_, v_x_680_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_721_);
v___x_723_ = v___x_715_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
v___y_694_ = v___x_723_;
goto v___jp_693_;
}
}
}
default: 
{
lean_object* v___x_726_; 
v___x_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_726_, 0, v_x_679_);
lean_ctor_set(v___x_726_, 1, v_x_680_);
v___y_694_ = v___x_726_;
goto v___jp_693_;
}
}
v___jp_693_:
{
lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_695_ = lean_array_fset(v_xs_x27_692_, v_j_684_, v___y_694_);
lean_dec(v_j_684_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_695_);
v___x_697_ = v___x_688_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
else
{
lean_object* v_ks_729_; lean_object* v_vs_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_748_; 
v_ks_729_ = lean_ctor_get(v_x_676_, 0);
v_vs_730_ = lean_ctor_get(v_x_676_, 1);
v_isSharedCheck_748_ = !lean_is_exclusive(v_x_676_);
if (v_isSharedCheck_748_ == 0)
{
v___x_732_ = v_x_676_;
v_isShared_733_ = v_isSharedCheck_748_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_vs_730_);
lean_inc(v_ks_729_);
lean_dec(v_x_676_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_748_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_ks_729_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_vs_730_);
v___x_735_ = v_reuseFailAlloc_747_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v_newNode_736_; size_t v___x_737_; uint8_t v___x_738_; 
v_newNode_736_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1___redArg(v___x_735_, v_x_679_, v_x_680_);
v___x_737_ = ((size_t)7ULL);
v___x_738_ = lean_usize_dec_le(v___x_737_, v_x_678_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_739_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_736_);
v___x_740_ = lean_unsigned_to_nat(4u);
v___x_741_ = lean_nat_dec_lt(v___x_739_, v___x_740_);
lean_dec(v___x_739_);
if (v___x_741_ == 0)
{
lean_object* v_ks_742_; lean_object* v_vs_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v_ks_742_ = lean_ctor_get(v_newNode_736_, 0);
lean_inc_ref(v_ks_742_);
v_vs_743_ = lean_ctor_get(v_newNode_736_, 1);
lean_inc_ref(v_vs_743_);
lean_dec_ref(v_newNode_736_);
v___x_744_ = lean_unsigned_to_nat(0u);
v___x_745_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___closed__0);
v___x_746_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg(v_x_678_, v_ks_742_, v_vs_743_, v___x_744_, v___x_745_);
lean_dec_ref(v_vs_743_);
lean_dec_ref(v_ks_742_);
return v___x_746_;
}
else
{
return v_newNode_736_;
}
}
else
{
return v_newNode_736_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_676_ = stack[0].m_obj;
size_t v_x_677_ = stack[1].m_num;
size_t v_x_678_ = stack[2].m_num;
lean_object* v_x_679_ = stack[3].m_obj;
lean_object* v_x_680_ = stack[4].m_obj;
lean_object* v_res_749_;
v_res_749_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(v_x_676_, v_x_677_, v_x_678_, v_x_679_, v_x_680_);
stack->m_obj
 = v_res_749_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg(size_t v_depth_750_, lean_object* v_keys_751_, lean_object* v_vals_752_, lean_object* v_i_753_, lean_object* v_entries_754_){
_start:
{
lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_755_ = lean_array_get_size(v_keys_751_);
v___x_756_ = lean_nat_dec_lt(v_i_753_, v___x_755_);
if (v___x_756_ == 0)
{
lean_dec(v_i_753_);
return v_entries_754_;
}
else
{
lean_object* v_k_757_; lean_object* v_v_758_; size_t v___x_759_; size_t v___x_760_; size_t v___x_761_; uint64_t v___x_762_; size_t v_h_763_; size_t v___x_764_; lean_object* v___x_765_; size_t v___x_766_; size_t v___x_767_; size_t v___x_768_; size_t v_h_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v_k_757_ = lean_array_fget_borrowed(v_keys_751_, v_i_753_);
v_v_758_ = lean_array_fget_borrowed(v_vals_752_, v_i_753_);
v___x_759_ = lean_ptr_addr(v_k_757_);
v___x_760_ = ((size_t)3ULL);
v___x_761_ = lean_usize_shift_right(v___x_759_, v___x_760_);
v___x_762_ = lean_usize_to_uint64(v___x_761_);
v_h_763_ = lean_uint64_to_usize(v___x_762_);
v___x_764_ = ((size_t)5ULL);
v___x_765_ = lean_unsigned_to_nat(1u);
v___x_766_ = ((size_t)1ULL);
v___x_767_ = lean_usize_sub(v_depth_750_, v___x_766_);
v___x_768_ = lean_usize_mul(v___x_764_, v___x_767_);
v_h_769_ = lean_usize_shift_right(v_h_763_, v___x_768_);
v___x_770_ = lean_nat_add(v_i_753_, v___x_765_);
lean_dec(v_i_753_);
lean_inc(v_v_758_);
lean_inc(v_k_757_);
v___x_771_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(v_entries_754_, v_h_769_, v_depth_750_, v_k_757_, v_v_758_);
v_i_753_ = v___x_770_;
v_entries_754_ = v___x_771_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_750_ = stack[0].m_num;
lean_object* v_keys_751_ = stack[1].m_obj;
lean_object* v_vals_752_ = stack[2].m_obj;
lean_object* v_i_753_ = stack[3].m_obj;
lean_object* v_entries_754_ = stack[4].m_obj;
lean_object* v_res_773_;
v_res_773_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_750_, v_keys_751_, v_vals_752_, v_i_753_, v_entries_754_);
stack->m_obj
 = v_res_773_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_774_, lean_object* v_keys_775_, lean_object* v_vals_776_, lean_object* v_i_777_, lean_object* v_entries_778_){
_start:
{
size_t v_depth_boxed_779_; lean_object* v_res_780_; 
v_depth_boxed_779_ = lean_unbox_usize(v_depth_774_);
lean_dec(v_depth_774_);
v_res_780_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_779_, v_keys_775_, v_vals_776_, v_i_777_, v_entries_778_);
lean_dec_ref(v_vals_776_);
lean_dec_ref(v_keys_775_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___boxed(lean_object* v_x_781_, lean_object* v_x_782_, lean_object* v_x_783_, lean_object* v_x_784_, lean_object* v_x_785_){
_start:
{
size_t v_x_7535__boxed_786_; size_t v_x_7536__boxed_787_; lean_object* v_res_788_; 
v_x_7535__boxed_786_ = lean_unbox_usize(v_x_782_);
lean_dec(v_x_782_);
v_x_7536__boxed_787_ = lean_unbox_usize(v_x_783_);
lean_dec(v_x_783_);
v_res_788_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(v_x_781_, v_x_7535__boxed_786_, v_x_7536__boxed_787_, v_x_784_, v_x_785_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0___redArg(lean_object* v_x_789_, lean_object* v_x_790_, lean_object* v_x_791_){
_start:
{
size_t v___x_792_; size_t v___x_793_; size_t v___x_794_; uint64_t v___x_795_; size_t v___x_796_; size_t v___x_797_; lean_object* v___x_798_; 
v___x_792_ = lean_ptr_addr(v_x_790_);
v___x_793_ = ((size_t)3ULL);
v___x_794_ = lean_usize_shift_right(v___x_792_, v___x_793_);
v___x_795_ = lean_usize_to_uint64(v___x_794_);
v___x_796_ = lean_uint64_to_usize(v___x_795_);
v___x_797_ = ((size_t)1ULL);
v___x_798_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(v_x_789_, v___x_796_, v___x_797_, v_x_790_, v_x_791_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___lam__0(lean_object* v_e_799_, lean_object* v_a_800_, lean_object* v_s_801_){
_start:
{
lean_object* v_rings_802_; lean_object* v_exprToRingId_803_; lean_object* v_semirings_804_; lean_object* v_exprToSemiringId_805_; lean_object* v_ncRings_806_; lean_object* v_exprToNCRingId_807_; lean_object* v_ncSemirings_808_; lean_object* v_exprToNCSemiringId_809_; lean_object* v_steps_810_; uint8_t v_reportedMaxDegreeIssue_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_819_; 
v_rings_802_ = lean_ctor_get(v_s_801_, 0);
v_exprToRingId_803_ = lean_ctor_get(v_s_801_, 1);
v_semirings_804_ = lean_ctor_get(v_s_801_, 2);
v_exprToSemiringId_805_ = lean_ctor_get(v_s_801_, 3);
v_ncRings_806_ = lean_ctor_get(v_s_801_, 4);
v_exprToNCRingId_807_ = lean_ctor_get(v_s_801_, 5);
v_ncSemirings_808_ = lean_ctor_get(v_s_801_, 6);
v_exprToNCSemiringId_809_ = lean_ctor_get(v_s_801_, 7);
v_steps_810_ = lean_ctor_get(v_s_801_, 8);
v_reportedMaxDegreeIssue_811_ = lean_ctor_get_uint8(v_s_801_, sizeof(void*)*9);
v_isSharedCheck_819_ = !lean_is_exclusive(v_s_801_);
if (v_isSharedCheck_819_ == 0)
{
v___x_813_ = v_s_801_;
v_isShared_814_ = v_isSharedCheck_819_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_steps_810_);
lean_inc(v_exprToNCSemiringId_809_);
lean_inc(v_ncSemirings_808_);
lean_inc(v_exprToNCRingId_807_);
lean_inc(v_ncRings_806_);
lean_inc(v_exprToSemiringId_805_);
lean_inc(v_semirings_804_);
lean_inc(v_exprToRingId_803_);
lean_inc(v_rings_802_);
lean_dec(v_s_801_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_819_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; lean_object* v___x_817_; 
lean_inc(v_a_800_);
v___x_815_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0___redArg(v_exprToNCSemiringId_809_, v_e_799_, v_a_800_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 7, v___x_815_);
v___x_817_ = v___x_813_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_rings_802_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_exprToRingId_803_);
lean_ctor_set(v_reuseFailAlloc_818_, 2, v_semirings_804_);
lean_ctor_set(v_reuseFailAlloc_818_, 3, v_exprToSemiringId_805_);
lean_ctor_set(v_reuseFailAlloc_818_, 4, v_ncRings_806_);
lean_ctor_set(v_reuseFailAlloc_818_, 5, v_exprToNCRingId_807_);
lean_ctor_set(v_reuseFailAlloc_818_, 6, v_ncSemirings_808_);
lean_ctor_set(v_reuseFailAlloc_818_, 7, v___x_815_);
lean_ctor_set(v_reuseFailAlloc_818_, 8, v_steps_810_);
lean_ctor_set_uint8(v_reuseFailAlloc_818_, sizeof(void*)*9, v_reportedMaxDegreeIssue_811_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___lam__0___boxed(lean_object* v_e_820_, lean_object* v_a_821_, lean_object* v_s_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___lam__0(v_e_820_, v_a_821_, v_s_822_);
lean_dec(v_a_821_);
return v_res_823_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__1(void){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__0));
v___x_826_ = l_Lean_stringToMessageData(v___x_825_);
return v___x_826_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(lean_object* v_e_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
lean_object* v___f_840_; lean_object* v___x_841_; 
lean_inc(v_a_828_);
lean_inc_ref(v_e_827_);
v___f_840_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_840_, 0, v_e_827_);
lean_closure_set(v___f_840_, 1, v_a_828_);
v___x_841_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg(v_e_827_, v_a_829_, v_a_834_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_a_842_);
lean_dec_ref_known(v___x_841_, 1);
if (lean_obj_tag(v_a_842_) == 1)
{
lean_object* v_val_843_; uint8_t v___x_844_; 
lean_dec_ref(v___f_840_);
v_val_843_ = lean_ctor_get(v_a_842_, 0);
lean_inc(v_val_843_);
lean_dec_ref_known(v_a_842_, 1);
v___x_844_ = lean_nat_dec_eq(v_val_843_, v_a_828_);
lean_dec(v_val_843_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_845_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__1);
v___x_846_ = l_Lean_indentExpr(v_e_827_);
v___x_847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_845_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v___x_848_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_830_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; uint8_t v_verbose_850_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_849_);
lean_dec_ref_known(v___x_848_, 1);
v_verbose_850_ = lean_ctor_get_uint8(v_a_849_, 0);
lean_dec(v_a_849_);
if (v_verbose_850_ == 0)
{
lean_dec_ref_known(v___x_847_, 2);
goto v___jp_837_;
}
else
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_Meta_Sym_reportIssue(v___x_847_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_dec_ref_known(v___x_851_, 1);
goto v___jp_837_;
}
else
{
return v___x_851_;
}
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_dec_ref_known(v___x_847_, 2);
v_a_852_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_848_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_848_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
else
{
lean_dec_ref(v_e_827_);
goto v___jp_837_;
}
}
else
{
lean_object* v___x_860_; lean_object* v___x_861_; 
lean_dec(v_a_842_);
lean_dec_ref(v_e_827_);
v___x_860_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_861_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_860_, v___f_840_, v_a_829_);
return v___x_861_;
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_dec_ref(v___f_840_);
lean_dec_ref(v_e_827_);
v_a_862_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_841_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_841_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
v___jp_837_:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = lean_box(0);
v___x_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
return v___x_839_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_827_ = stack[0].m_obj;
lean_object* v_a_828_ = stack[1].m_obj;
lean_object* v_a_829_ = stack[2].m_obj;
lean_object* v_a_830_ = stack[3].m_obj;
lean_object* v_a_831_ = stack[4].m_obj;
lean_object* v_a_832_ = stack[5].m_obj;
lean_object* v_a_833_ = stack[6].m_obj;
lean_object* v_a_834_ = stack[7].m_obj;
lean_object* v_a_835_ = stack[8].m_obj;
lean_object* v_res_870_;
v_res_870_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(v_e_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
stack->m_obj
 = v_res_870_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___boxed(lean_object* v_e_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(v_e_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec(v_a_872_);
return v_res_881_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId(lean_object* v_e_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(v_e_882_, v_a_883_, v_a_884_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_);
return v___x_895_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_882_ = stack[0].m_obj;
lean_object* v_a_883_ = stack[1].m_obj;
lean_object* v_a_884_ = stack[2].m_obj;
lean_object* v_a_885_ = stack[3].m_obj;
lean_object* v_a_886_ = stack[4].m_obj;
lean_object* v_a_887_ = stack[5].m_obj;
lean_object* v_a_888_ = stack[6].m_obj;
lean_object* v_a_889_ = stack[7].m_obj;
lean_object* v_a_890_ = stack[8].m_obj;
lean_object* v_a_891_ = stack[9].m_obj;
lean_object* v_a_892_ = stack[10].m_obj;
lean_object* v_a_893_ = stack[11].m_obj;
lean_object* v_res_896_;
v_res_896_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId(v_e_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_);
stack->m_obj
 = v_res_896_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___boxed(lean_object* v_e_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId(v_e_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
lean_dec(v_a_902_);
lean_dec_ref(v_a_901_);
lean_dec(v_a_900_);
lean_dec(v_a_899_);
lean_dec(v_a_898_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0(lean_object* v_00_u03b2_911_, lean_object* v_x_912_, lean_object* v_x_913_, lean_object* v_x_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0___redArg(v_x_912_, v_x_913_, v_x_914_);
return v___x_915_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0(lean_object* v_00_u03b2_916_, lean_object* v_x_917_, size_t v_x_918_, size_t v_x_919_, lean_object* v_x_920_, lean_object* v_x_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(v_x_917_, v_x_918_, v_x_919_, v_x_920_, v_x_921_);
return v___x_922_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_917_ = stack[1].m_obj;
size_t v_x_918_ = stack[2].m_num;
size_t v_x_919_ = stack[3].m_num;
lean_object* v_x_920_ = stack[4].m_obj;
lean_object* v_x_921_ = stack[5].m_obj;
lean_object* v_res_923_;
v_res_923_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0(lean_box(0), v_x_917_, v_x_918_, v_x_919_, v_x_920_, v_x_921_);
stack->m_obj
 = v_res_923_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_924_, lean_object* v_x_925_, lean_object* v_x_926_, lean_object* v_x_927_, lean_object* v_x_928_, lean_object* v_x_929_){
_start:
{
size_t v_x_7972__boxed_930_; size_t v_x_7973__boxed_931_; lean_object* v_res_932_; 
v_x_7972__boxed_930_ = lean_unbox_usize(v_x_926_);
lean_dec(v_x_926_);
v_x_7973__boxed_931_ = lean_unbox_usize(v_x_927_);
lean_dec(v_x_927_);
v_res_932_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0(v_00_u03b2_924_, v_x_925_, v_x_7972__boxed_930_, v_x_7973__boxed_931_, v_x_928_, v_x_929_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_933_, lean_object* v_n_934_, lean_object* v_k_935_, lean_object* v_v_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1___redArg(v_n_934_, v_k_935_, v_v_936_);
return v___x_937_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_938_, size_t v_depth_939_, lean_object* v_keys_940_, lean_object* v_vals_941_, lean_object* v_heq_942_, lean_object* v_i_943_, lean_object* v_entries_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_939_, v_keys_940_, v_vals_941_, v_i_943_, v_entries_944_);
return v___x_945_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_depth_939_ = stack[1].m_num;
lean_object* v_keys_940_ = stack[2].m_obj;
lean_object* v_vals_941_ = stack[3].m_obj;
lean_object* v_i_943_ = stack[5].m_obj;
lean_object* v_entries_944_ = stack[6].m_obj;
lean_object* v_res_946_;
v_res_946_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2(lean_box(0), v_depth_939_, v_keys_940_, v_vals_941_, lean_box(0), v_i_943_, v_entries_944_);
stack->m_obj
 = v_res_946_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_947_, lean_object* v_depth_948_, lean_object* v_keys_949_, lean_object* v_vals_950_, lean_object* v_heq_951_, lean_object* v_i_952_, lean_object* v_entries_953_){
_start:
{
size_t v_depth_boxed_954_; lean_object* v_res_955_; 
v_depth_boxed_954_ = lean_unbox_usize(v_depth_948_);
lean_dec(v_depth_948_);
v_res_955_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2(v_00_u03b2_947_, v_depth_boxed_954_, v_keys_949_, v_vals_950_, v_heq_951_, v_i_952_, v_entries_953_);
lean_dec_ref(v_vals_950_);
lean_dec_ref(v_keys_949_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_956_, lean_object* v_x_957_, lean_object* v_x_958_, lean_object* v_x_959_, lean_object* v_x_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_957_, v_x_958_, v_x_959_, v_x_960_);
return v___x_961_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___lam__0(lean_object* v_e_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(v_e_962_, v___y_963_, v___y_964_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
return v___x_975_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_962_ = stack[0].m_obj;
lean_object* v___y_963_ = stack[1].m_obj;
lean_object* v___y_964_ = stack[2].m_obj;
lean_object* v___y_965_ = stack[3].m_obj;
lean_object* v___y_966_ = stack[4].m_obj;
lean_object* v___y_967_ = stack[5].m_obj;
lean_object* v___y_968_ = stack[6].m_obj;
lean_object* v___y_969_ = stack[7].m_obj;
lean_object* v___y_970_ = stack[8].m_obj;
lean_object* v___y_971_ = stack[9].m_obj;
lean_object* v___y_972_ = stack[10].m_obj;
lean_object* v___y_973_ = stack[11].m_obj;
lean_object* v_res_976_;
v_res_976_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___lam__0(v_e_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
stack->m_obj
 = v_res_976_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___lam__0___boxed(lean_object* v_e_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___lam__0(v_e_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec(v___y_979_);
lean_dec(v___y_978_);
return v_res_990_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0___closed__1(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0___closed__0));
v___x_995_ = l_Lean_stringToMessageData(v___x_994_);
return v___x_995_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0(lean_object* v___x_996_, lean_object* v___x_997_, lean_object* v___f_998_, lean_object* v___x_999_, lean_object* v___f_1000_, lean_object* v_e_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_1001_, v___y_1003_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; uint8_t v___x_1016_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
lean_dec_ref_known(v___x_1014_, 1);
v___x_1016_ = lean_unbox(v_a_1015_);
lean_dec(v_a_1015_);
if (v___x_1016_ == 0)
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1449__overap_1020_; lean_object* v___x_1021_; 
v___x_1017_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0___closed__1);
lean_inc_ref(v_e_1001_);
v___x_1018_ = l_Lean_indentExpr(v_e_1001_);
v___x_1019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
lean_inc_ref(v___x_996_);
v___x_1449__overap_1020_ = l_Lean_throwError___redArg(v___x_996_, v___x_997_, v___x_1019_);
lean_inc(v___y_1012_);
lean_inc_ref(v___y_1011_);
lean_inc(v___y_1010_);
lean_inc_ref(v___y_1009_);
lean_inc(v___y_1008_);
lean_inc_ref(v___y_1007_);
lean_inc(v___y_1006_);
lean_inc_ref(v___y_1005_);
lean_inc(v___y_1004_);
lean_inc(v___y_1003_);
lean_inc(v___y_1002_);
v___x_1021_ = lean_apply_12(v___x_1449__overap_1020_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, lean_box(0));
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v___x_1452__overap_1022_; lean_object* v___x_1023_; 
lean_dec_ref_known(v___x_1021_, 1);
v___x_1452__overap_1022_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(v___f_998_, v___x_996_, v___x_999_, v___f_1000_, v_e_1001_);
lean_inc(v___y_1012_);
lean_inc_ref(v___y_1011_);
lean_inc(v___y_1010_);
lean_inc_ref(v___y_1009_);
lean_inc(v___y_1008_);
lean_inc_ref(v___y_1007_);
lean_inc(v___y_1006_);
lean_inc_ref(v___y_1005_);
lean_inc(v___y_1004_);
lean_inc(v___y_1003_);
lean_inc(v___y_1002_);
v___x_1023_ = lean_apply_12(v___x_1452__overap_1022_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, lean_box(0));
return v___x_1023_;
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_dec_ref(v_e_1001_);
lean_dec_ref(v___f_1000_);
lean_dec_ref(v___x_999_);
lean_dec(v___f_998_);
lean_dec_ref(v___x_996_);
v_a_1024_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1021_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1021_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
else
{
lean_object* v___x_1456__overap_1032_; lean_object* v___x_1033_; 
lean_dec_ref(v___x_997_);
v___x_1456__overap_1032_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(v___f_998_, v___x_996_, v___x_999_, v___f_1000_, v_e_1001_);
lean_inc(v___y_1012_);
lean_inc_ref(v___y_1011_);
lean_inc(v___y_1010_);
lean_inc_ref(v___y_1009_);
lean_inc(v___y_1008_);
lean_inc_ref(v___y_1007_);
lean_inc(v___y_1006_);
lean_inc_ref(v___y_1005_);
lean_inc(v___y_1004_);
lean_inc(v___y_1003_);
lean_inc(v___y_1002_);
v___x_1033_ = lean_apply_12(v___x_1456__overap_1032_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, lean_box(0));
return v___x_1033_;
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec_ref(v_e_1001_);
lean_dec_ref(v___f_1000_);
lean_dec_ref(v___x_999_);
lean_dec(v___f_998_);
lean_dec_ref(v___x_997_);
lean_dec_ref(v___x_996_);
v_a_1034_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_1014_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1014_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_996_ = stack[0].m_obj;
lean_object* v___x_997_ = stack[1].m_obj;
lean_object* v___f_998_ = stack[2].m_obj;
lean_object* v___x_999_ = stack[3].m_obj;
lean_object* v___f_1000_ = stack[4].m_obj;
lean_object* v_e_1001_ = stack[5].m_obj;
lean_object* v___y_1002_ = stack[6].m_obj;
lean_object* v___y_1003_ = stack[7].m_obj;
lean_object* v___y_1004_ = stack[8].m_obj;
lean_object* v___y_1005_ = stack[9].m_obj;
lean_object* v___y_1006_ = stack[10].m_obj;
lean_object* v___y_1007_ = stack[11].m_obj;
lean_object* v___y_1008_ = stack[12].m_obj;
lean_object* v___y_1009_ = stack[13].m_obj;
lean_object* v___y_1010_ = stack[14].m_obj;
lean_object* v___y_1011_ = stack[15].m_obj;
lean_object* v___y_1012_ = stack[16].m_obj;
lean_object* v_res_1042_;
v_res_1042_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0(v___x_996_, v___x_997_, v___f_998_, v___x_999_, v___f_1000_, v_e_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
stack->m_obj
 = v_res_1042_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0___boxed(lean_object** _args){
lean_object* v___x_1043_ = _args[0];
lean_object* v___x_1044_ = _args[1];
lean_object* v___f_1045_ = _args[2];
lean_object* v___x_1046_ = _args[3];
lean_object* v___f_1047_ = _args[4];
lean_object* v_e_1048_ = _args[5];
lean_object* v___y_1049_ = _args[6];
lean_object* v___y_1050_ = _args[7];
lean_object* v___y_1051_ = _args[8];
lean_object* v___y_1052_ = _args[9];
lean_object* v___y_1053_ = _args[10];
lean_object* v___y_1054_ = _args[11];
lean_object* v___y_1055_ = _args[12];
lean_object* v___y_1056_ = _args[13];
lean_object* v___y_1057_ = _args[14];
lean_object* v___y_1058_ = _args[15];
lean_object* v___y_1059_ = _args[16];
lean_object* v___y_1060_ = _args[17];
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0(v___x_1043_, v___x_1044_, v___f_1045_, v___x_1046_, v___f_1047_, v_e_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec(v___y_1049_);
return v_res_1061_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__0(void){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_instMonadEIO___redArg();
return v___x_1062_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__1(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__0);
v___x_1064_ = l_StateRefT_x27_instMonad___redArg(v___x_1063_);
return v___x_1064_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__7(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___f_1071_; 
v___x_1070_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_1071_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1071_, 0, v___x_1070_);
return v___f_1071_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__8(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___f_1073_; 
v___x_1072_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_1073_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1073_, 0, v___x_1072_);
return v___f_1073_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__9(void){
_start:
{
lean_object* v___f_1074_; lean_object* v___f_1075_; lean_object* v___x_1076_; 
v___f_1074_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__8, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__8_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__8);
v___f_1075_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__7, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__7_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__7);
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___f_1075_);
lean_ctor_set(v___x_1076_, 1, v___f_1074_);
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__10(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___f_1078_; 
v___x_1077_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__9, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__9_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__9);
v___f_1078_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1078_, 0, v___x_1077_);
return v___f_1078_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__11(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___f_1080_; 
v___x_1079_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__9, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__9_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__9);
v___f_1080_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1080_, 0, v___x_1079_);
return v___f_1080_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__12(void){
_start:
{
lean_object* v___f_1081_; lean_object* v___f_1082_; lean_object* v___x_1083_; 
v___f_1081_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__11, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__11_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__11);
v___f_1082_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__10, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__10_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__10);
v___x_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___f_1082_);
lean_ctor_set(v___x_1083_, 1, v___f_1081_);
return v___x_1083_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__13(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___f_1085_; 
v___x_1084_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__12);
v___f_1085_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1085_, 0, v___x_1084_);
return v___f_1085_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__14(void){
_start:
{
lean_object* v___x_1086_; lean_object* v___f_1087_; 
v___x_1086_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__12);
v___f_1087_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1087_, 0, v___x_1086_);
return v___f_1087_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__15(void){
_start:
{
lean_object* v___f_1088_; lean_object* v___f_1089_; lean_object* v___x_1090_; 
v___f_1088_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__14, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__14_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__14);
v___f_1089_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__13, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__13_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__13);
v___x_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___f_1089_);
lean_ctor_set(v___x_1090_, 1, v___f_1088_);
return v___x_1090_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__16(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___f_1092_; 
v___x_1091_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__15, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__15_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__15);
v___f_1092_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1092_, 0, v___x_1091_);
return v___f_1092_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__17(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___f_1094_; 
v___x_1093_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__15, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__15_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__15);
v___f_1094_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1094_, 0, v___x_1093_);
return v___f_1094_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__18(void){
_start:
{
lean_object* v___f_1095_; lean_object* v___f_1096_; lean_object* v___x_1097_; 
v___f_1095_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__17, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__17_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__17);
v___f_1096_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__16, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__16_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__16);
v___x_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___f_1096_);
lean_ctor_set(v___x_1097_, 1, v___f_1095_);
return v___x_1097_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__19(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___f_1099_; 
v___x_1098_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__18, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__18_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__18);
v___f_1099_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1099_, 0, v___x_1098_);
return v___f_1099_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__20(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___f_1101_; 
v___x_1100_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__18, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__18_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__18);
v___f_1101_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1101_, 0, v___x_1100_);
return v___f_1101_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__21(void){
_start:
{
lean_object* v___f_1102_; lean_object* v___f_1103_; lean_object* v___x_1104_; 
v___f_1102_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__20, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__20_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__20);
v___f_1103_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__19, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__19_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__19);
v___x_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___f_1103_);
lean_ctor_set(v___x_1104_, 1, v___f_1102_);
return v___x_1104_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__22(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___f_1106_; 
v___x_1105_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__21, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__21_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__21);
v___f_1106_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1106_, 0, v___x_1105_);
return v___f_1106_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__23(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___f_1108_; 
v___x_1107_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__21, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__21_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__21);
v___f_1108_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1108_, 0, v___x_1107_);
return v___f_1108_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__24(void){
_start:
{
lean_object* v___f_1109_; lean_object* v___f_1110_; lean_object* v___x_1111_; 
v___f_1109_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__23, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__23_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__23);
v___f_1110_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__22, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__22_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__22);
v___x_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___f_1110_);
lean_ctor_set(v___x_1111_, 1, v___f_1109_);
return v___x_1111_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__25(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___f_1113_; 
v___x_1112_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__24, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__24_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__24);
v___f_1113_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1113_, 0, v___x_1112_);
return v___f_1113_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__26(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___f_1115_; 
v___x_1114_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__24, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__24_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__24);
v___f_1115_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1115_, 0, v___x_1114_);
return v___f_1115_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__27(void){
_start:
{
lean_object* v___f_1116_; lean_object* v___f_1117_; lean_object* v___x_1118_; 
v___f_1116_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__26, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__26_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__26);
v___f_1117_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__25, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__25_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__25);
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___f_1117_);
lean_ctor_set(v___x_1118_, 1, v___f_1116_);
return v___x_1118_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__28(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___f_1120_; 
v___x_1119_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__27, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__27_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__27);
v___f_1120_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1120_, 0, v___x_1119_);
return v___f_1120_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__29(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___f_1122_; 
v___x_1121_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__27, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__27_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__27);
v___f_1122_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1122_, 0, v___x_1121_);
return v___f_1122_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__30(void){
_start:
{
lean_object* v___f_1123_; lean_object* v___f_1124_; lean_object* v___x_1125_; 
v___f_1123_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__29, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__29_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__29);
v___f_1124_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__28, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__28_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__28);
v___x_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___f_1124_);
lean_ctor_set(v___x_1125_, 1, v___f_1123_);
return v___x_1125_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__31(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___f_1127_; 
v___x_1126_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__30, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__30_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__30);
v___f_1127_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1127_, 0, v___x_1126_);
return v___f_1127_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__32(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___f_1129_; 
v___x_1128_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__30, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__30_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__30);
v___f_1129_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1129_, 0, v___x_1128_);
return v___f_1129_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__33(void){
_start:
{
lean_object* v___f_1130_; lean_object* v___f_1131_; lean_object* v___x_1132_; 
v___f_1130_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__32, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__32_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__32);
v___f_1131_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__31, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__31_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__31);
v___x_1132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___f_1131_);
lean_ctor_set(v___x_1132_, 1, v___f_1130_);
return v___x_1132_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__37(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1136_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1137_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__36));
v___x_1138_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__35));
v___x_1139_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1138_, v___x_1137_, v___x_1136_);
return v___x_1139_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__38(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___f_1141_; lean_object* v___f_1142_; lean_object* v___x_1143_; 
v___x_1140_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__37, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__37_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__37);
v___f_1141_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6));
v___f_1142_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__34));
v___x_1143_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1142_, v___f_1141_, v___x_1140_);
return v___x_1143_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__39(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1144_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__38, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__38_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__38);
v___x_1145_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__36));
v___x_1146_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__35));
v___x_1147_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1146_, v___x_1145_, v___x_1144_);
return v___x_1147_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__40(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___f_1149_; lean_object* v___f_1150_; lean_object* v___x_1151_; 
v___x_1148_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__39, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__39_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__39);
v___f_1149_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6));
v___f_1150_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__34));
v___x_1151_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1150_, v___f_1149_, v___x_1148_);
return v___x_1151_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__41(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1152_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__40, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__40_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__40);
v___x_1153_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__36));
v___x_1154_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__35));
v___x_1155_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1154_, v___x_1153_, v___x_1152_);
return v___x_1155_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__42(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___f_1157_; lean_object* v___f_1158_; lean_object* v___x_1159_; 
v___x_1156_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__41, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__41_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__41);
v___f_1157_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6));
v___f_1158_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__34));
v___x_1159_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1158_, v___f_1157_, v___x_1156_);
return v___x_1159_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__43(void){
_start:
{
lean_object* v___x_1160_; lean_object* v___f_1161_; lean_object* v___f_1162_; lean_object* v___x_1163_; 
v___x_1160_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__42, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__42_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__42);
v___f_1161_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6));
v___f_1162_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__34));
v___x_1163_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1162_, v___f_1161_, v___x_1160_);
return v___x_1163_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__44(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1164_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__43, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__43_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__43);
v___x_1165_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__36));
v___x_1166_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__35));
v___x_1167_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1166_, v___x_1165_, v___x_1164_);
return v___x_1167_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__45(void){
_start:
{
lean_object* v___x_1168_; lean_object* v___f_1169_; lean_object* v___f_1170_; lean_object* v___x_1171_; 
v___x_1168_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__44, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__44_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__44);
v___f_1169_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6));
v___f_1170_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__34));
v___x_1171_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1170_, v___f_1169_, v___x_1168_);
return v___x_1171_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__48(void){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___f_1178_; 
v___x_1176_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__36));
v___x_1177_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_1178_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1178_, 0, v___x_1177_);
lean_closure_set(v___f_1178_, 1, v___x_1176_);
return v___f_1178_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__49(void){
_start:
{
lean_object* v___f_1179_; lean_object* v___f_1180_; lean_object* v___f_1181_; 
v___f_1179_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6));
v___f_1180_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__48, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__48_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__48);
v___f_1181_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1181_, 0, v___f_1180_);
lean_closure_set(v___f_1181_, 1, v___f_1179_);
return v___f_1181_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__50(void){
_start:
{
lean_object* v___x_1182_; lean_object* v___f_1183_; lean_object* v___f_1184_; 
v___x_1182_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__36));
v___f_1183_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__49, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__49_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__49);
v___f_1184_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1184_, 0, v___f_1183_);
lean_closure_set(v___f_1184_, 1, v___x_1182_);
return v___f_1184_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__51(void){
_start:
{
lean_object* v___f_1185_; lean_object* v___f_1186_; lean_object* v___f_1187_; 
v___f_1185_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6));
v___f_1186_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__50, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__50_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__50);
v___f_1187_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1187_, 0, v___f_1186_);
lean_closure_set(v___f_1187_, 1, v___f_1185_);
return v___f_1187_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__52(void){
_start:
{
lean_object* v___f_1188_; lean_object* v___f_1189_; lean_object* v___f_1190_; 
v___f_1188_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6));
v___f_1189_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__51, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__51_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__51);
v___f_1190_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1190_, 0, v___f_1189_);
lean_closure_set(v___f_1190_, 1, v___f_1188_);
return v___f_1190_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__53(void){
_start:
{
lean_object* v___x_1191_; lean_object* v___f_1192_; lean_object* v___f_1193_; 
v___x_1191_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__36));
v___f_1192_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__52, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__52_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__52);
v___f_1193_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1193_, 0, v___f_1192_);
lean_closure_set(v___f_1193_, 1, v___x_1191_);
return v___f_1193_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__54(void){
_start:
{
lean_object* v___f_1194_; lean_object* v___f_1195_; lean_object* v___f_1196_; 
v___f_1194_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6));
v___f_1195_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__53, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__53_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__53);
v___f_1196_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1196_, 0, v___f_1195_);
lean_closure_set(v___f_1196_, 1, v___f_1194_);
return v___f_1196_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM(void){
_start:
{
lean_object* v___x_1197_; lean_object* v_toApplicative_1198_; lean_object* v_toFunctor_1199_; lean_object* v_toSeq_1200_; lean_object* v_toSeqLeft_1201_; lean_object* v_toSeqRight_1202_; lean_object* v___f_1203_; lean_object* v___f_1204_; lean_object* v___f_1205_; lean_object* v___f_1206_; lean_object* v___x_1207_; lean_object* v___f_1208_; lean_object* v___f_1209_; lean_object* v___f_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v_toApplicative_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1258_; 
v___x_1197_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__1);
v_toApplicative_1198_ = lean_ctor_get(v___x_1197_, 0);
v_toFunctor_1199_ = lean_ctor_get(v_toApplicative_1198_, 0);
v_toSeq_1200_ = lean_ctor_get(v_toApplicative_1198_, 2);
v_toSeqLeft_1201_ = lean_ctor_get(v_toApplicative_1198_, 3);
v_toSeqRight_1202_ = lean_ctor_get(v_toApplicative_1198_, 4);
v___f_1203_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__2));
v___f_1204_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__3));
lean_inc_ref_n(v_toFunctor_1199_, 2);
v___f_1205_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1205_, 0, v_toFunctor_1199_);
v___f_1206_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1206_, 0, v_toFunctor_1199_);
v___x_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___f_1205_);
lean_ctor_set(v___x_1207_, 1, v___f_1206_);
lean_inc(v_toSeqRight_1202_);
v___f_1208_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1208_, 0, v_toSeqRight_1202_);
lean_inc(v_toSeqLeft_1201_);
v___f_1209_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1209_, 0, v_toSeqLeft_1201_);
lean_inc(v_toSeq_1200_);
v___f_1210_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1210_, 0, v_toSeq_1200_);
v___x_1211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1207_);
lean_ctor_set(v___x_1211_, 1, v___f_1203_);
lean_ctor_set(v___x_1211_, 2, v___f_1210_);
lean_ctor_set(v___x_1211_, 3, v___f_1209_);
lean_ctor_set(v___x_1211_, 4, v___f_1208_);
v___x_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
lean_ctor_set(v___x_1212_, 1, v___f_1204_);
v___x_1213_ = l_StateRefT_x27_instMonad___redArg(v___x_1212_);
v_toApplicative_1214_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; 
v_unused_1259_ = lean_ctor_get(v___x_1213_, 1);
lean_dec(v_unused_1259_);
v___x_1216_ = v___x_1213_;
v_isShared_1217_ = v_isSharedCheck_1258_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_toApplicative_1214_);
lean_dec(v___x_1213_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1258_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v_toFunctor_1218_; lean_object* v_toSeq_1219_; lean_object* v_toSeqLeft_1220_; lean_object* v_toSeqRight_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1256_; 
v_toFunctor_1218_ = lean_ctor_get(v_toApplicative_1214_, 0);
v_toSeq_1219_ = lean_ctor_get(v_toApplicative_1214_, 2);
v_toSeqLeft_1220_ = lean_ctor_get(v_toApplicative_1214_, 3);
v_toSeqRight_1221_ = lean_ctor_get(v_toApplicative_1214_, 4);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_toApplicative_1214_);
if (v_isSharedCheck_1256_ == 0)
{
lean_object* v_unused_1257_; 
v_unused_1257_ = lean_ctor_get(v_toApplicative_1214_, 1);
lean_dec(v_unused_1257_);
v___x_1223_ = v_toApplicative_1214_;
v_isShared_1224_ = v_isSharedCheck_1256_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_toSeqRight_1221_);
lean_inc(v_toSeqLeft_1220_);
lean_inc(v_toSeq_1219_);
lean_inc(v_toFunctor_1218_);
lean_dec(v_toApplicative_1214_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1256_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___f_1225_; lean_object* v___f_1226_; lean_object* v___f_1227_; lean_object* v___f_1228_; lean_object* v___x_1229_; lean_object* v___f_1230_; lean_object* v___f_1231_; lean_object* v___f_1232_; lean_object* v___x_1234_; 
v___f_1225_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__4));
v___f_1226_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__5));
lean_inc_ref(v_toFunctor_1218_);
v___f_1227_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1227_, 0, v_toFunctor_1218_);
v___f_1228_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1228_, 0, v_toFunctor_1218_);
v___x_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___f_1227_);
lean_ctor_set(v___x_1229_, 1, v___f_1228_);
v___f_1230_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1230_, 0, v_toSeqRight_1221_);
v___f_1231_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1231_, 0, v_toSeqLeft_1220_);
v___f_1232_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1232_, 0, v_toSeq_1219_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 4, v___f_1230_);
lean_ctor_set(v___x_1223_, 3, v___f_1231_);
lean_ctor_set(v___x_1223_, 2, v___f_1232_);
lean_ctor_set(v___x_1223_, 1, v___f_1225_);
lean_ctor_set(v___x_1223_, 0, v___x_1229_);
v___x_1234_ = v___x_1223_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1229_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v___f_1225_);
lean_ctor_set(v_reuseFailAlloc_1255_, 2, v___f_1232_);
lean_ctor_set(v_reuseFailAlloc_1255_, 3, v___f_1231_);
lean_ctor_set(v_reuseFailAlloc_1255_, 4, v___f_1230_);
v___x_1234_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
lean_object* v___x_1236_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 1, v___f_1226_);
lean_ctor_set(v___x_1216_, 0, v___x_1234_);
v___x_1236_ = v___x_1216_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v___f_1226_);
v___x_1236_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v_toMonadRef_1247_; lean_object* v___f_1248_; lean_object* v___f_1249_; lean_object* v___f_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___f_1253_; 
v___x_1237_ = l_StateRefT_x27_instMonad___redArg(v___x_1236_);
v___x_1238_ = l_ReaderT_instMonad___redArg(v___x_1237_);
v___x_1239_ = l_StateRefT_x27_instMonad___redArg(v___x_1238_);
v___x_1240_ = l_ReaderT_instMonad___redArg(v___x_1239_);
v___x_1241_ = l_ReaderT_instMonad___redArg(v___x_1240_);
v___x_1242_ = l_StateRefT_x27_instMonad___redArg(v___x_1241_);
v___x_1243_ = l_ReaderT_instMonad___redArg(v___x_1242_);
v___x_1244_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM;
v___x_1245_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__33, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__33_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__33);
v___x_1246_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__45, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__45_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__45);
v_toMonadRef_1247_ = lean_ctor_get(v___x_1246_, 0);
v___f_1248_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__47));
v___f_1249_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___closed__0));
v___f_1250_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__54, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__54_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__54);
lean_inc_ref(v___x_1243_);
v___x_1251_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1250_, v___x_1243_);
lean_inc_ref(v_toMonadRef_1247_);
v___x_1252_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1245_);
lean_ctor_set(v___x_1252_, 1, v_toMonadRef_1247_);
lean_ctor_set(v___x_1252_, 2, v___x_1251_);
v___f_1253_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0___boxed), 18, 5);
lean_closure_set(v___f_1253_, 0, v___x_1243_);
lean_closure_set(v___f_1253_, 1, v___x_1252_);
lean_closure_set(v___f_1253_, 2, v___f_1248_);
lean_closure_set(v___f_1253_, 3, v___x_1244_);
lean_closure_set(v___f_1253_, 4, v___f_1249_);
return v___f_1253_;
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
