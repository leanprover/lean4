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
lean_object* v___x_129_; lean_object* v_env_130_; uint8_t v___x_131_; lean_object* v_env_132_; lean_object* v___x_133_; lean_object* v_toCold_134_; lean_object* v_mctx_135_; lean_object* v_lctx_136_; lean_object* v_options_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_129_ = lean_st_ref_get(v___y_127_);
v_env_130_ = lean_ctor_get(v___x_129_, 0);
lean_inc_ref(v_env_130_);
lean_dec(v___x_129_);
v___x_131_ = 0;
v_env_132_ = l_Lean_Environment_setRecordingDeps(v_env_130_, v___x_131_);
v___x_133_ = lean_st_ref_get(v___y_125_);
v_toCold_134_ = lean_ctor_get(v___y_126_, 0);
v_mctx_135_ = lean_ctor_get(v___x_133_, 0);
lean_inc_ref(v_mctx_135_);
lean_dec(v___x_133_);
v_lctx_136_ = lean_ctor_get(v___y_124_, 2);
v_options_137_ = lean_ctor_get(v_toCold_134_, 2);
lean_inc_ref(v_options_137_);
lean_inc_ref(v_lctx_136_);
v___x_138_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_138_, 0, v_env_132_);
lean_ctor_set(v___x_138_, 1, v_mctx_135_);
lean_ctor_set(v___x_138_, 2, v_lctx_136_);
lean_ctor_set(v___x_138_, 3, v_options_137_);
v___x_139_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v_msgData_123_);
v___x_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0_spec__0___boxed(lean_object* v_msgData_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0_spec__0(v_msgData_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg(lean_object* v_msg_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v_ref_154_; lean_object* v___x_155_; lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_164_; 
v_ref_154_ = lean_ctor_get(v___y_151_, 2);
v___x_155_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0_spec__0(v_msg_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
v_a_156_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_164_ == 0)
{
v___x_158_ = v___x_155_;
v_isShared_159_ = v_isSharedCheck_164_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_155_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_164_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_160_; lean_object* v___x_162_; 
lean_inc(v_ref_154_);
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v_ref_154_);
lean_ctor_set(v___x_160_, 1, v_a_156_);
if (v_isShared_159_ == 0)
{
lean_ctor_set_tag(v___x_158_, 1);
lean_ctor_set(v___x_158_, 0, v___x_160_);
v___x_162_ = v___x_158_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg___boxed(lean_object* v_msg_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg(v_msg_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
return v_res_171_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__1(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__0));
v___x_174_ = l_Lean_stringToMessageData(v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring(lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_181_, v_a_184_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_201_; 
v_a_188_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_201_ == 0)
{
v___x_190_ = v___x_187_;
v_isShared_191_ = v_isSharedCheck_201_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_187_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_201_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v_ncSemirings_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v_ncSemirings_192_ = lean_ctor_get(v_a_188_, 4);
lean_inc_ref(v_ncSemirings_192_);
lean_dec(v_a_188_);
v___x_193_ = lean_array_get_size(v_ncSemirings_192_);
v___x_194_ = lean_nat_dec_lt(v_a_175_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; 
lean_dec_ref(v_ncSemirings_192_);
lean_del_object(v___x_190_);
v___x_195_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__1);
v___x_196_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg(v___x_195_, v_a_182_, v_a_183_, v_a_184_, v_a_185_);
return v___x_196_;
}
else
{
lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_197_ = lean_array_fget(v_ncSemirings_192_, v_a_175_);
lean_dec_ref(v_ncSemirings_192_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 0, v___x_197_);
v___x_199_ = v___x_190_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_197_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
v_a_202_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_187_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_187_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___boxed(lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring(v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_);
lean_dec(v_a_220_);
lean_dec_ref(v_a_219_);
lean_dec(v_a_218_);
lean_dec_ref(v_a_217_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
lean_dec(v_a_212_);
lean_dec(v_a_211_);
lean_dec(v_a_210_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0(lean_object* v_00_u03b1_223_, lean_object* v_msg_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg(v_msg_224_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___boxed(lean_object* v_00_u03b1_238_, lean_object* v_msg_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0(v_00_u03b1_238_, v_msg_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec(v___y_241_);
lean_dec(v___y_240_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___lam__0(lean_object* v_a_253_, lean_object* v_f_254_, lean_object* v_s_255_){
_start:
{
lean_object* v_exp_256_; lean_object* v_rings_257_; lean_object* v_semirings_258_; lean_object* v_ncRings_259_; lean_object* v_ncSemirings_260_; lean_object* v_typeClassify_261_; lean_object* v_orders_262_; lean_object* v_typeOrderClassify_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v_exp_256_ = lean_ctor_get(v_s_255_, 0);
v_rings_257_ = lean_ctor_get(v_s_255_, 1);
v_semirings_258_ = lean_ctor_get(v_s_255_, 2);
v_ncRings_259_ = lean_ctor_get(v_s_255_, 3);
v_ncSemirings_260_ = lean_ctor_get(v_s_255_, 4);
v_typeClassify_261_ = lean_ctor_get(v_s_255_, 5);
v_orders_262_ = lean_ctor_get(v_s_255_, 6);
v_typeOrderClassify_263_ = lean_ctor_get(v_s_255_, 7);
v___x_264_ = lean_array_get_size(v_ncSemirings_260_);
v___x_265_ = lean_nat_dec_lt(v_a_253_, v___x_264_);
if (v___x_265_ == 0)
{
lean_dec_ref(v_f_254_);
return v_s_255_;
}
else
{
lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_277_; 
lean_inc_ref(v_typeOrderClassify_263_);
lean_inc_ref(v_orders_262_);
lean_inc_ref(v_typeClassify_261_);
lean_inc_ref(v_ncSemirings_260_);
lean_inc_ref(v_ncRings_259_);
lean_inc_ref(v_semirings_258_);
lean_inc_ref(v_rings_257_);
lean_inc(v_exp_256_);
v_isSharedCheck_277_ = !lean_is_exclusive(v_s_255_);
if (v_isSharedCheck_277_ == 0)
{
lean_object* v_unused_278_; lean_object* v_unused_279_; lean_object* v_unused_280_; lean_object* v_unused_281_; lean_object* v_unused_282_; lean_object* v_unused_283_; lean_object* v_unused_284_; lean_object* v_unused_285_; 
v_unused_278_ = lean_ctor_get(v_s_255_, 7);
lean_dec(v_unused_278_);
v_unused_279_ = lean_ctor_get(v_s_255_, 6);
lean_dec(v_unused_279_);
v_unused_280_ = lean_ctor_get(v_s_255_, 5);
lean_dec(v_unused_280_);
v_unused_281_ = lean_ctor_get(v_s_255_, 4);
lean_dec(v_unused_281_);
v_unused_282_ = lean_ctor_get(v_s_255_, 3);
lean_dec(v_unused_282_);
v_unused_283_ = lean_ctor_get(v_s_255_, 2);
lean_dec(v_unused_283_);
v_unused_284_ = lean_ctor_get(v_s_255_, 1);
lean_dec(v_unused_284_);
v_unused_285_ = lean_ctor_get(v_s_255_, 0);
lean_dec(v_unused_285_);
v___x_267_ = v_s_255_;
v_isShared_268_ = v_isSharedCheck_277_;
goto v_resetjp_266_;
}
else
{
lean_dec(v_s_255_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_277_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v_v_269_; lean_object* v___x_270_; lean_object* v_xs_x27_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; 
v_v_269_ = lean_array_fget(v_ncSemirings_260_, v_a_253_);
v___x_270_ = lean_box(0);
v_xs_x27_271_ = lean_array_fset(v_ncSemirings_260_, v_a_253_, v___x_270_);
v___x_272_ = lean_apply_1(v_f_254_, v_v_269_);
v___x_273_ = lean_array_fset(v_xs_x27_271_, v_a_253_, v___x_272_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 4, v___x_273_);
v___x_275_ = v___x_267_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_exp_256_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v_rings_257_);
lean_ctor_set(v_reuseFailAlloc_276_, 2, v_semirings_258_);
lean_ctor_set(v_reuseFailAlloc_276_, 3, v_ncRings_259_);
lean_ctor_set(v_reuseFailAlloc_276_, 4, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_276_, 5, v_typeClassify_261_);
lean_ctor_set(v_reuseFailAlloc_276_, 6, v_orders_262_);
lean_ctor_set(v_reuseFailAlloc_276_, 7, v_typeOrderClassify_263_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___lam__0___boxed(lean_object* v_a_286_, lean_object* v_f_287_, lean_object* v_s_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___lam__0(v_a_286_, v_f_287_, v_s_288_);
lean_dec(v_a_286_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg(lean_object* v_f_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v___f_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
lean_inc(v_a_291_);
v___f_294_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_294_, 0, v_a_291_);
lean_closure_set(v___f_294_, 1, v_f_290_);
v___x_295_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_296_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_295_, v___f_294_, v_a_292_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___boxed(lean_object* v_f_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg(v_f_297_, v_a_298_, v_a_299_);
lean_dec(v_a_299_);
lean_dec(v_a_298_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring(lean_object* v_f_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg(v_f_302_, v_a_303_, v_a_309_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___boxed(lean_object* v_f_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring(v_f_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
lean_dec(v_a_321_);
lean_dec_ref(v_a_320_);
lean_dec(v_a_319_);
lean_dec(v_a_318_);
lean_dec(v_a_317_);
return v_res_329_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__1(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__0));
v___x_332_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___boxed), 12, 0);
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v___x_331_);
return v___x_333_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM(void){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__1);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState___redArg(lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_336_, v_a_337_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_348_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_348_ == 0)
{
v___x_342_ = v___x_339_;
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_339_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_344_; lean_object* v___x_346_; 
v___x_344_ = l_Lean_Meta_Grind_Arith_CommRing_State_getNCSemiring(v_a_340_, v_a_335_);
lean_dec(v_a_340_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 0, v___x_344_);
v___x_346_ = v___x_342_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
else
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
v_a_349_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_339_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_339_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_349_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState___redArg___boxed(lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState___redArg(v_a_357_, v_a_358_, v_a_359_);
lean_dec_ref(v_a_359_);
lean_dec(v_a_358_);
lean_dec(v_a_357_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState(lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState___redArg(v_a_362_, v_a_363_, v_a_371_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState___boxed(lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState(v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
lean_dec(v_a_383_);
lean_dec_ref(v_a_382_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec(v_a_376_);
lean_dec(v_a_375_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg___lam__0(lean_object* v_a_388_, lean_object* v_f_389_, lean_object* v_s_390_){
_start:
{
lean_object* v_rings_391_; lean_object* v_exprToRingId_392_; lean_object* v_semirings_393_; lean_object* v_exprToSemiringId_394_; lean_object* v_ncRings_395_; lean_object* v_exprToNCRingId_396_; lean_object* v_ncSemirings_397_; lean_object* v_exprToNCSemiringId_398_; lean_object* v_steps_399_; uint8_t v_reportedMaxDegreeIssue_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_421_; 
v_rings_391_ = lean_ctor_get(v_s_390_, 0);
v_exprToRingId_392_ = lean_ctor_get(v_s_390_, 1);
v_semirings_393_ = lean_ctor_get(v_s_390_, 2);
v_exprToSemiringId_394_ = lean_ctor_get(v_s_390_, 3);
v_ncRings_395_ = lean_ctor_get(v_s_390_, 4);
v_exprToNCRingId_396_ = lean_ctor_get(v_s_390_, 5);
v_ncSemirings_397_ = lean_ctor_get(v_s_390_, 6);
v_exprToNCSemiringId_398_ = lean_ctor_get(v_s_390_, 7);
v_steps_399_ = lean_ctor_get(v_s_390_, 8);
v_reportedMaxDegreeIssue_400_ = lean_ctor_get_uint8(v_s_390_, sizeof(void*)*9);
v_isSharedCheck_421_ = !lean_is_exclusive(v_s_390_);
if (v_isSharedCheck_421_ == 0)
{
v___x_402_ = v_s_390_;
v_isShared_403_ = v_isSharedCheck_421_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_steps_399_);
lean_inc(v_exprToNCSemiringId_398_);
lean_inc(v_ncSemirings_397_);
lean_inc(v_exprToNCRingId_396_);
lean_inc(v_ncRings_395_);
lean_inc(v_exprToSemiringId_394_);
lean_inc(v_semirings_393_);
lean_inc(v_exprToRingId_392_);
lean_inc(v_rings_391_);
lean_dec(v_s_390_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_421_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_404_ = lean_unsigned_to_nat(1u);
v___x_405_ = lean_nat_add(v_a_388_, v___x_404_);
v___x_406_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default;
v___x_407_ = l_Array_rightpad___redArg(v___x_405_, v___x_406_, v_ncSemirings_397_);
lean_dec(v___x_405_);
v___x_408_ = lean_array_get_size(v___x_407_);
v___x_409_ = lean_nat_dec_lt(v_a_388_, v___x_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_411_; 
lean_dec_ref(v_f_389_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 6, v___x_407_);
v___x_411_ = v___x_402_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_rings_391_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_exprToRingId_392_);
lean_ctor_set(v_reuseFailAlloc_412_, 2, v_semirings_393_);
lean_ctor_set(v_reuseFailAlloc_412_, 3, v_exprToSemiringId_394_);
lean_ctor_set(v_reuseFailAlloc_412_, 4, v_ncRings_395_);
lean_ctor_set(v_reuseFailAlloc_412_, 5, v_exprToNCRingId_396_);
lean_ctor_set(v_reuseFailAlloc_412_, 6, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_412_, 7, v_exprToNCSemiringId_398_);
lean_ctor_set(v_reuseFailAlloc_412_, 8, v_steps_399_);
lean_ctor_set_uint8(v_reuseFailAlloc_412_, sizeof(void*)*9, v_reportedMaxDegreeIssue_400_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
else
{
lean_object* v_v_413_; lean_object* v___x_414_; lean_object* v_xs_x27_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
v_v_413_ = lean_array_fget(v___x_407_, v_a_388_);
v___x_414_ = lean_box(0);
v_xs_x27_415_ = lean_array_fset(v___x_407_, v_a_388_, v___x_414_);
v___x_416_ = lean_apply_1(v_f_389_, v_v_413_);
v___x_417_ = lean_array_fset(v_xs_x27_415_, v_a_388_, v___x_416_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 6, v___x_417_);
v___x_419_ = v___x_402_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_rings_391_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_exprToRingId_392_);
lean_ctor_set(v_reuseFailAlloc_420_, 2, v_semirings_393_);
lean_ctor_set(v_reuseFailAlloc_420_, 3, v_exprToSemiringId_394_);
lean_ctor_set(v_reuseFailAlloc_420_, 4, v_ncRings_395_);
lean_ctor_set(v_reuseFailAlloc_420_, 5, v_exprToNCRingId_396_);
lean_ctor_set(v_reuseFailAlloc_420_, 6, v___x_417_);
lean_ctor_set(v_reuseFailAlloc_420_, 7, v_exprToNCSemiringId_398_);
lean_ctor_set(v_reuseFailAlloc_420_, 8, v_steps_399_);
lean_ctor_set_uint8(v_reuseFailAlloc_420_, sizeof(void*)*9, v_reportedMaxDegreeIssue_400_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg___lam__0___boxed(lean_object* v_a_422_, lean_object* v_f_423_, lean_object* v_s_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg___lam__0(v_a_422_, v_f_423_, v_s_424_);
lean_dec(v_a_422_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg(lean_object* v_f_426_, lean_object* v_a_427_, lean_object* v_a_428_){
_start:
{
lean_object* v___f_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
lean_inc(v_a_427_);
v___f_430_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_430_, 0, v_a_427_);
lean_closure_set(v___f_430_, 1, v_f_426_);
v___x_431_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_432_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_431_, v___f_430_, v_a_428_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg___boxed(lean_object* v_f_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg(v_f_433_, v_a_434_, v_a_435_);
lean_dec(v_a_435_);
lean_dec(v_a_434_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState(lean_object* v_f_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg(v_f_438_, v_a_439_, v_a_440_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___boxed(lean_object* v_f_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState(v_f_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_);
lean_dec(v_a_463_);
lean_dec_ref(v_a_462_);
lean_dec(v_a_461_);
lean_dec_ref(v_a_460_);
lean_dec(v_a_459_);
lean_dec_ref(v_a_458_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec(v_a_454_);
lean_dec(v_a_453_);
return v_res_465_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM___closed__1(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_467_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM___closed__0));
v___x_468_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiringState___boxed), 12, 0);
v___x_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
lean_ctor_set(v___x_469_, 1, v___x_467_);
return v___x_469_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM(void){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM___closed__1);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_471_, lean_object* v_vals_472_, lean_object* v_i_473_, lean_object* v_k_474_){
_start:
{
lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_475_ = lean_array_get_size(v_keys_471_);
v___x_476_ = lean_nat_dec_lt(v_i_473_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; 
lean_dec(v_i_473_);
v___x_477_ = lean_box(0);
return v___x_477_;
}
else
{
lean_object* v_k_x27_478_; size_t v___x_479_; size_t v___x_480_; uint8_t v___x_481_; 
v_k_x27_478_ = lean_array_fget_borrowed(v_keys_471_, v_i_473_);
v___x_479_ = lean_ptr_addr(v_k_474_);
v___x_480_ = lean_ptr_addr(v_k_x27_478_);
v___x_481_ = lean_usize_dec_eq(v___x_479_, v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_unsigned_to_nat(1u);
v___x_483_ = lean_nat_add(v_i_473_, v___x_482_);
lean_dec(v_i_473_);
v_i_473_ = v___x_483_;
goto _start;
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_array_fget_borrowed(v_vals_472_, v_i_473_);
lean_dec(v_i_473_);
lean_inc(v___x_485_);
v___x_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_487_, lean_object* v_vals_488_, lean_object* v_i_489_, lean_object* v_k_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_487_, v_vals_488_, v_i_489_, v_k_490_);
lean_dec_ref(v_k_490_);
lean_dec_ref(v_vals_488_);
lean_dec_ref(v_keys_487_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg(lean_object* v_x_492_, size_t v_x_493_, lean_object* v_x_494_){
_start:
{
if (lean_obj_tag(v_x_492_) == 0)
{
lean_object* v_es_495_; lean_object* v___x_496_; size_t v___x_497_; size_t v___x_498_; lean_object* v_j_499_; lean_object* v___x_500_; 
v_es_495_ = lean_ctor_get(v_x_492_, 0);
v___x_496_ = lean_box(2);
v___x_497_ = ((size_t)31ULL);
v___x_498_ = lean_usize_land(v_x_493_, v___x_497_);
v_j_499_ = lean_usize_to_nat(v___x_498_);
v___x_500_ = lean_array_get_borrowed(v___x_496_, v_es_495_, v_j_499_);
lean_dec(v_j_499_);
switch(lean_obj_tag(v___x_500_))
{
case 0:
{
lean_object* v_key_501_; lean_object* v_val_502_; size_t v___x_503_; size_t v___x_504_; uint8_t v___x_505_; 
v_key_501_ = lean_ctor_get(v___x_500_, 0);
v_val_502_ = lean_ctor_get(v___x_500_, 1);
v___x_503_ = lean_ptr_addr(v_x_494_);
v___x_504_ = lean_ptr_addr(v_key_501_);
v___x_505_ = lean_usize_dec_eq(v___x_503_, v___x_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; 
v___x_506_ = lean_box(0);
return v___x_506_;
}
else
{
lean_object* v___x_507_; 
lean_inc(v_val_502_);
v___x_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_507_, 0, v_val_502_);
return v___x_507_;
}
}
case 1:
{
lean_object* v_node_508_; size_t v___x_509_; size_t v___x_510_; 
v_node_508_ = lean_ctor_get(v___x_500_, 0);
v___x_509_ = ((size_t)5ULL);
v___x_510_ = lean_usize_shift_right(v_x_493_, v___x_509_);
v_x_492_ = v_node_508_;
v_x_493_ = v___x_510_;
goto _start;
}
default: 
{
lean_object* v___x_512_; 
v___x_512_ = lean_box(0);
return v___x_512_;
}
}
}
else
{
lean_object* v_ks_513_; lean_object* v_vs_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v_ks_513_ = lean_ctor_get(v_x_492_, 0);
v_vs_514_ = lean_ctor_get(v_x_492_, 1);
v___x_515_ = lean_unsigned_to_nat(0u);
v___x_516_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_513_, v_vs_514_, v___x_515_, v_x_494_);
return v___x_516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_517_, lean_object* v_x_518_, lean_object* v_x_519_){
_start:
{
size_t v_x_905__boxed_520_; lean_object* v_res_521_; 
v_x_905__boxed_520_ = lean_unbox_usize(v_x_518_);
lean_dec(v_x_518_);
v_res_521_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg(v_x_517_, v_x_905__boxed_520_, v_x_519_);
lean_dec_ref(v_x_519_);
lean_dec_ref(v_x_517_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg(lean_object* v_x_522_, lean_object* v_x_523_){
_start:
{
size_t v___x_524_; size_t v___x_525_; size_t v___x_526_; uint64_t v___x_527_; size_t v___x_528_; lean_object* v___x_529_; 
v___x_524_ = lean_ptr_addr(v_x_523_);
v___x_525_ = ((size_t)3ULL);
v___x_526_ = lean_usize_shift_right(v___x_524_, v___x_525_);
v___x_527_ = lean_usize_to_uint64(v___x_526_);
v___x_528_ = lean_uint64_to_usize(v___x_527_);
v___x_529_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg(v_x_522_, v___x_528_, v_x_523_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg___boxed(lean_object* v_x_530_, lean_object* v_x_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg(v_x_530_, v_x_531_);
lean_dec_ref(v_x_531_);
lean_dec_ref(v_x_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg(lean_object* v_e_533_, lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_534_, v_a_535_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_547_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_547_ == 0)
{
v___x_540_ = v___x_537_;
v_isShared_541_ = v_isSharedCheck_547_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_537_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_547_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v_exprToNCSemiringId_542_; lean_object* v___x_543_; lean_object* v___x_545_; 
v_exprToNCSemiringId_542_ = lean_ctor_get(v_a_538_, 7);
lean_inc_ref(v_exprToNCSemiringId_542_);
lean_dec(v_a_538_);
v___x_543_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg(v_exprToNCSemiringId_542_, v_e_533_);
lean_dec_ref(v_exprToNCSemiringId_542_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 0, v___x_543_);
v___x_545_ = v___x_540_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_543_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
else
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
v_a_548_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_537_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_537_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_548_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg___boxed(lean_object* v_e_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg(v_e_556_, v_a_557_, v_a_558_);
lean_dec_ref(v_a_558_);
lean_dec(v_a_557_);
lean_dec_ref(v_e_556_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f(lean_object* v_e_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg(v_e_561_, v_a_562_, v_a_570_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___boxed(lean_object* v_e_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f(v_e_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_583_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
lean_dec(v_a_576_);
lean_dec(v_a_575_);
lean_dec_ref(v_e_574_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0(lean_object* v_00_u03b2_587_, lean_object* v_x_588_, lean_object* v_x_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg(v_x_588_, v_x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___boxed(lean_object* v_00_u03b2_591_, lean_object* v_x_592_, lean_object* v_x_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0(v_00_u03b2_591_, v_x_592_, v_x_593_);
lean_dec_ref(v_x_593_);
lean_dec_ref(v_x_592_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_595_, lean_object* v_x_596_, size_t v_x_597_, lean_object* v_x_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg(v_x_596_, v_x_597_, v_x_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_600_, lean_object* v_x_601_, lean_object* v_x_602_, lean_object* v_x_603_){
_start:
{
size_t v_x_1026__boxed_604_; lean_object* v_res_605_; 
v_x_1026__boxed_604_ = lean_unbox_usize(v_x_602_);
lean_dec(v_x_602_);
v_res_605_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0(v_00_u03b2_600_, v_x_601_, v_x_1026__boxed_604_, v_x_603_);
lean_dec_ref(v_x_603_);
lean_dec_ref(v_x_601_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_606_, lean_object* v_keys_607_, lean_object* v_vals_608_, lean_object* v_heq_609_, lean_object* v_i_610_, lean_object* v_k_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_607_, v_vals_608_, v_i_610_, v_k_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_613_, lean_object* v_keys_614_, lean_object* v_vals_615_, lean_object* v_heq_616_, lean_object* v_i_617_, lean_object* v_k_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_613_, v_keys_614_, v_vals_615_, v_heq_616_, v_i_617_, v_k_618_);
lean_dec_ref(v_k_618_);
lean_dec_ref(v_vals_615_);
lean_dec_ref(v_keys_614_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_620_, lean_object* v_x_621_, lean_object* v_x_622_, lean_object* v_x_623_){
_start:
{
lean_object* v_ks_624_; lean_object* v_vs_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_651_; 
v_ks_624_ = lean_ctor_get(v_x_620_, 0);
v_vs_625_ = lean_ctor_get(v_x_620_, 1);
v_isSharedCheck_651_ = !lean_is_exclusive(v_x_620_);
if (v_isSharedCheck_651_ == 0)
{
v___x_627_ = v_x_620_;
v_isShared_628_ = v_isSharedCheck_651_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_vs_625_);
lean_inc(v_ks_624_);
lean_dec(v_x_620_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_651_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_629_ = lean_array_get_size(v_ks_624_);
v___x_630_ = lean_nat_dec_lt(v_x_621_, v___x_629_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_634_; 
lean_dec(v_x_621_);
v___x_631_ = lean_array_push(v_ks_624_, v_x_622_);
v___x_632_ = lean_array_push(v_vs_625_, v_x_623_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v___x_632_);
lean_ctor_set(v___x_627_, 0, v___x_631_);
v___x_634_ = v___x_627_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v___x_632_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
else
{
lean_object* v_k_x27_636_; size_t v___x_637_; size_t v___x_638_; uint8_t v___x_639_; 
v_k_x27_636_ = lean_array_fget_borrowed(v_ks_624_, v_x_621_);
v___x_637_ = lean_ptr_addr(v_x_622_);
v___x_638_ = lean_ptr_addr(v_k_x27_636_);
v___x_639_ = lean_usize_dec_eq(v___x_637_, v___x_638_);
if (v___x_639_ == 0)
{
lean_object* v___x_641_; 
if (v_isShared_628_ == 0)
{
v___x_641_ = v___x_627_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_ks_624_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_vs_625_);
v___x_641_ = v_reuseFailAlloc_645_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_unsigned_to_nat(1u);
v___x_643_ = lean_nat_add(v_x_621_, v___x_642_);
lean_dec(v_x_621_);
v_x_620_ = v___x_641_;
v_x_621_ = v___x_643_;
goto _start;
}
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_646_ = lean_array_fset(v_ks_624_, v_x_621_, v_x_622_);
v___x_647_ = lean_array_fset(v_vs_625_, v_x_621_, v_x_623_);
lean_dec(v_x_621_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v___x_647_);
lean_ctor_set(v___x_627_, 0, v___x_646_);
v___x_649_ = v___x_627_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_646_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_652_, lean_object* v_k_653_, lean_object* v_v_654_){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = lean_unsigned_to_nat(0u);
v___x_656_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_652_, v___x_655_, v_k_653_, v_v_654_);
return v___x_656_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(lean_object* v_x_658_, size_t v_x_659_, size_t v_x_660_, lean_object* v_x_661_, lean_object* v_x_662_){
_start:
{
if (lean_obj_tag(v_x_658_) == 0)
{
lean_object* v_es_663_; size_t v___x_664_; size_t v___x_665_; lean_object* v_j_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v_es_663_ = lean_ctor_get(v_x_658_, 0);
v___x_664_ = ((size_t)31ULL);
v___x_665_ = lean_usize_land(v_x_659_, v___x_664_);
v_j_666_ = lean_usize_to_nat(v___x_665_);
v___x_667_ = lean_array_get_size(v_es_663_);
v___x_668_ = lean_nat_dec_lt(v_j_666_, v___x_667_);
if (v___x_668_ == 0)
{
lean_dec(v_j_666_);
lean_dec(v_x_662_);
lean_dec_ref(v_x_661_);
return v_x_658_;
}
else
{
lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_709_; 
lean_inc_ref(v_es_663_);
v_isSharedCheck_709_ = !lean_is_exclusive(v_x_658_);
if (v_isSharedCheck_709_ == 0)
{
lean_object* v_unused_710_; 
v_unused_710_ = lean_ctor_get(v_x_658_, 0);
lean_dec(v_unused_710_);
v___x_670_ = v_x_658_;
v_isShared_671_ = v_isSharedCheck_709_;
goto v_resetjp_669_;
}
else
{
lean_dec(v_x_658_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_709_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v_v_672_; lean_object* v___x_673_; lean_object* v_xs_x27_674_; lean_object* v___y_676_; 
v_v_672_ = lean_array_fget(v_es_663_, v_j_666_);
v___x_673_ = lean_box(0);
v_xs_x27_674_ = lean_array_fset(v_es_663_, v_j_666_, v___x_673_);
switch(lean_obj_tag(v_v_672_))
{
case 0:
{
lean_object* v_key_681_; lean_object* v_val_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_694_; 
v_key_681_ = lean_ctor_get(v_v_672_, 0);
v_val_682_ = lean_ctor_get(v_v_672_, 1);
v_isSharedCheck_694_ = !lean_is_exclusive(v_v_672_);
if (v_isSharedCheck_694_ == 0)
{
v___x_684_ = v_v_672_;
v_isShared_685_ = v_isSharedCheck_694_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_val_682_);
lean_inc(v_key_681_);
lean_dec(v_v_672_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_694_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
size_t v___x_686_; size_t v___x_687_; uint8_t v___x_688_; 
v___x_686_ = lean_ptr_addr(v_x_661_);
v___x_687_ = lean_ptr_addr(v_key_681_);
v___x_688_ = lean_usize_dec_eq(v___x_686_, v___x_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_690_; 
lean_del_object(v___x_684_);
v___x_689_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_681_, v_val_682_, v_x_661_, v_x_662_);
v___x_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
v___y_676_ = v___x_690_;
goto v___jp_675_;
}
else
{
lean_object* v___x_692_; 
lean_dec(v_val_682_);
lean_dec(v_key_681_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v_x_662_);
lean_ctor_set(v___x_684_, 0, v_x_661_);
v___x_692_ = v___x_684_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_x_661_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_x_662_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
v___y_676_ = v___x_692_;
goto v___jp_675_;
}
}
}
}
case 1:
{
lean_object* v_node_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_707_; 
v_node_695_ = lean_ctor_get(v_v_672_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v_v_672_);
if (v_isSharedCheck_707_ == 0)
{
v___x_697_ = v_v_672_;
v_isShared_698_ = v_isSharedCheck_707_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_node_695_);
lean_dec(v_v_672_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_707_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
size_t v___x_699_; size_t v___x_700_; size_t v___x_701_; size_t v___x_702_; lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_699_ = ((size_t)5ULL);
v___x_700_ = lean_usize_shift_right(v_x_659_, v___x_699_);
v___x_701_ = ((size_t)1ULL);
v___x_702_ = lean_usize_add(v_x_660_, v___x_701_);
v___x_703_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(v_node_695_, v___x_700_, v___x_702_, v_x_661_, v_x_662_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_703_);
v___x_705_ = v___x_697_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
v___y_676_ = v___x_705_;
goto v___jp_675_;
}
}
}
default: 
{
lean_object* v___x_708_; 
v___x_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_708_, 0, v_x_661_);
lean_ctor_set(v___x_708_, 1, v_x_662_);
v___y_676_ = v___x_708_;
goto v___jp_675_;
}
}
v___jp_675_:
{
lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_677_ = lean_array_fset(v_xs_x27_674_, v_j_666_, v___y_676_);
lean_dec(v_j_666_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_677_);
v___x_679_ = v___x_670_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
else
{
lean_object* v_ks_711_; lean_object* v_vs_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_730_; 
v_ks_711_ = lean_ctor_get(v_x_658_, 0);
v_vs_712_ = lean_ctor_get(v_x_658_, 1);
v_isSharedCheck_730_ = !lean_is_exclusive(v_x_658_);
if (v_isSharedCheck_730_ == 0)
{
v___x_714_ = v_x_658_;
v_isShared_715_ = v_isSharedCheck_730_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_vs_712_);
lean_inc(v_ks_711_);
lean_dec(v_x_658_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_730_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_ks_711_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_vs_712_);
v___x_717_ = v_reuseFailAlloc_729_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v_newNode_718_; size_t v___x_719_; uint8_t v___x_720_; 
v_newNode_718_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1___redArg(v___x_717_, v_x_661_, v_x_662_);
v___x_719_ = ((size_t)7ULL);
v___x_720_ = lean_usize_dec_le(v___x_719_, v_x_660_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_721_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_718_);
v___x_722_ = lean_unsigned_to_nat(4u);
v___x_723_ = lean_nat_dec_lt(v___x_721_, v___x_722_);
lean_dec(v___x_721_);
if (v___x_723_ == 0)
{
lean_object* v_ks_724_; lean_object* v_vs_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v_ks_724_ = lean_ctor_get(v_newNode_718_, 0);
lean_inc_ref(v_ks_724_);
v_vs_725_ = lean_ctor_get(v_newNode_718_, 1);
lean_inc_ref(v_vs_725_);
lean_dec_ref(v_newNode_718_);
v___x_726_ = lean_unsigned_to_nat(0u);
v___x_727_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___closed__0);
v___x_728_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg(v_x_660_, v_ks_724_, v_vs_725_, v___x_726_, v___x_727_);
lean_dec_ref(v_vs_725_);
lean_dec_ref(v_ks_724_);
return v___x_728_;
}
else
{
return v_newNode_718_;
}
}
else
{
return v_newNode_718_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg(size_t v_depth_731_, lean_object* v_keys_732_, lean_object* v_vals_733_, lean_object* v_i_734_, lean_object* v_entries_735_){
_start:
{
lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_736_ = lean_array_get_size(v_keys_732_);
v___x_737_ = lean_nat_dec_lt(v_i_734_, v___x_736_);
if (v___x_737_ == 0)
{
lean_dec(v_i_734_);
return v_entries_735_;
}
else
{
lean_object* v_k_738_; lean_object* v_v_739_; size_t v___x_740_; size_t v___x_741_; size_t v___x_742_; uint64_t v___x_743_; size_t v_h_744_; size_t v___x_745_; lean_object* v___x_746_; size_t v___x_747_; size_t v___x_748_; size_t v___x_749_; size_t v_h_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v_k_738_ = lean_array_fget_borrowed(v_keys_732_, v_i_734_);
v_v_739_ = lean_array_fget_borrowed(v_vals_733_, v_i_734_);
v___x_740_ = lean_ptr_addr(v_k_738_);
v___x_741_ = ((size_t)3ULL);
v___x_742_ = lean_usize_shift_right(v___x_740_, v___x_741_);
v___x_743_ = lean_usize_to_uint64(v___x_742_);
v_h_744_ = lean_uint64_to_usize(v___x_743_);
v___x_745_ = ((size_t)5ULL);
v___x_746_ = lean_unsigned_to_nat(1u);
v___x_747_ = ((size_t)1ULL);
v___x_748_ = lean_usize_sub(v_depth_731_, v___x_747_);
v___x_749_ = lean_usize_mul(v___x_745_, v___x_748_);
v_h_750_ = lean_usize_shift_right(v_h_744_, v___x_749_);
v___x_751_ = lean_nat_add(v_i_734_, v___x_746_);
lean_dec(v_i_734_);
lean_inc(v_v_739_);
lean_inc(v_k_738_);
v___x_752_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(v_entries_735_, v_h_750_, v_depth_731_, v_k_738_, v_v_739_);
v_i_734_ = v___x_751_;
v_entries_735_ = v___x_752_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_754_, lean_object* v_keys_755_, lean_object* v_vals_756_, lean_object* v_i_757_, lean_object* v_entries_758_){
_start:
{
size_t v_depth_boxed_759_; lean_object* v_res_760_; 
v_depth_boxed_759_ = lean_unbox_usize(v_depth_754_);
lean_dec(v_depth_754_);
v_res_760_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_759_, v_keys_755_, v_vals_756_, v_i_757_, v_entries_758_);
lean_dec_ref(v_vals_756_);
lean_dec_ref(v_keys_755_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___boxed(lean_object* v_x_761_, lean_object* v_x_762_, lean_object* v_x_763_, lean_object* v_x_764_, lean_object* v_x_765_){
_start:
{
size_t v_x_7502__boxed_766_; size_t v_x_7503__boxed_767_; lean_object* v_res_768_; 
v_x_7502__boxed_766_ = lean_unbox_usize(v_x_762_);
lean_dec(v_x_762_);
v_x_7503__boxed_767_ = lean_unbox_usize(v_x_763_);
lean_dec(v_x_763_);
v_res_768_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(v_x_761_, v_x_7502__boxed_766_, v_x_7503__boxed_767_, v_x_764_, v_x_765_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0___redArg(lean_object* v_x_769_, lean_object* v_x_770_, lean_object* v_x_771_){
_start:
{
size_t v___x_772_; size_t v___x_773_; size_t v___x_774_; uint64_t v___x_775_; size_t v___x_776_; size_t v___x_777_; lean_object* v___x_778_; 
v___x_772_ = lean_ptr_addr(v_x_770_);
v___x_773_ = ((size_t)3ULL);
v___x_774_ = lean_usize_shift_right(v___x_772_, v___x_773_);
v___x_775_ = lean_usize_to_uint64(v___x_774_);
v___x_776_ = lean_uint64_to_usize(v___x_775_);
v___x_777_ = ((size_t)1ULL);
v___x_778_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(v_x_769_, v___x_776_, v___x_777_, v_x_770_, v_x_771_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___lam__0(lean_object* v_e_779_, lean_object* v_a_780_, lean_object* v_s_781_){
_start:
{
lean_object* v_rings_782_; lean_object* v_exprToRingId_783_; lean_object* v_semirings_784_; lean_object* v_exprToSemiringId_785_; lean_object* v_ncRings_786_; lean_object* v_exprToNCRingId_787_; lean_object* v_ncSemirings_788_; lean_object* v_exprToNCSemiringId_789_; lean_object* v_steps_790_; uint8_t v_reportedMaxDegreeIssue_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_799_; 
v_rings_782_ = lean_ctor_get(v_s_781_, 0);
v_exprToRingId_783_ = lean_ctor_get(v_s_781_, 1);
v_semirings_784_ = lean_ctor_get(v_s_781_, 2);
v_exprToSemiringId_785_ = lean_ctor_get(v_s_781_, 3);
v_ncRings_786_ = lean_ctor_get(v_s_781_, 4);
v_exprToNCRingId_787_ = lean_ctor_get(v_s_781_, 5);
v_ncSemirings_788_ = lean_ctor_get(v_s_781_, 6);
v_exprToNCSemiringId_789_ = lean_ctor_get(v_s_781_, 7);
v_steps_790_ = lean_ctor_get(v_s_781_, 8);
v_reportedMaxDegreeIssue_791_ = lean_ctor_get_uint8(v_s_781_, sizeof(void*)*9);
v_isSharedCheck_799_ = !lean_is_exclusive(v_s_781_);
if (v_isSharedCheck_799_ == 0)
{
v___x_793_ = v_s_781_;
v_isShared_794_ = v_isSharedCheck_799_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_steps_790_);
lean_inc(v_exprToNCSemiringId_789_);
lean_inc(v_ncSemirings_788_);
lean_inc(v_exprToNCRingId_787_);
lean_inc(v_ncRings_786_);
lean_inc(v_exprToSemiringId_785_);
lean_inc(v_semirings_784_);
lean_inc(v_exprToRingId_783_);
lean_inc(v_rings_782_);
lean_dec(v_s_781_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_799_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v___x_797_; 
lean_inc(v_a_780_);
v___x_795_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0___redArg(v_exprToNCSemiringId_789_, v_e_779_, v_a_780_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 7, v___x_795_);
v___x_797_ = v___x_793_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_rings_782_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_exprToRingId_783_);
lean_ctor_set(v_reuseFailAlloc_798_, 2, v_semirings_784_);
lean_ctor_set(v_reuseFailAlloc_798_, 3, v_exprToSemiringId_785_);
lean_ctor_set(v_reuseFailAlloc_798_, 4, v_ncRings_786_);
lean_ctor_set(v_reuseFailAlloc_798_, 5, v_exprToNCRingId_787_);
lean_ctor_set(v_reuseFailAlloc_798_, 6, v_ncSemirings_788_);
lean_ctor_set(v_reuseFailAlloc_798_, 7, v___x_795_);
lean_ctor_set(v_reuseFailAlloc_798_, 8, v_steps_790_);
lean_ctor_set_uint8(v_reuseFailAlloc_798_, sizeof(void*)*9, v_reportedMaxDegreeIssue_791_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___lam__0___boxed(lean_object* v_e_800_, lean_object* v_a_801_, lean_object* v_s_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___lam__0(v_e_800_, v_a_801_, v_s_802_);
lean_dec(v_a_801_);
return v_res_803_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__1(void){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__0));
v___x_806_ = l_Lean_stringToMessageData(v___x_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(lean_object* v_e_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_){
_start:
{
lean_object* v___f_820_; lean_object* v___x_821_; 
lean_inc(v_a_808_);
lean_inc_ref(v_e_807_);
v___f_820_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_820_, 0, v_e_807_);
lean_closure_set(v___f_820_, 1, v_a_808_);
v___x_821_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg(v_e_807_, v_a_809_, v_a_814_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_a_822_);
lean_dec_ref_known(v___x_821_, 1);
if (lean_obj_tag(v_a_822_) == 1)
{
lean_object* v_val_823_; uint8_t v___x_824_; 
lean_dec_ref(v___f_820_);
v_val_823_ = lean_ctor_get(v_a_822_, 0);
lean_inc(v_val_823_);
lean_dec_ref_known(v_a_822_, 1);
v___x_824_ = lean_nat_dec_eq(v_val_823_, v_a_808_);
lean_dec(v_val_823_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_825_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__1);
v___x_826_ = l_Lean_indentExpr(v_e_807_);
v___x_827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_825_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v___x_828_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_810_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; uint8_t v_verbose_830_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_a_829_);
lean_dec_ref_known(v___x_828_, 1);
v_verbose_830_ = lean_ctor_get_uint8(v_a_829_, 0);
lean_dec(v_a_829_);
if (v_verbose_830_ == 0)
{
lean_dec_ref_known(v___x_827_, 2);
goto v___jp_817_;
}
else
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_Meta_Sym_reportIssue(v___x_827_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_dec_ref_known(v___x_831_, 1);
goto v___jp_817_;
}
else
{
return v___x_831_;
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec_ref_known(v___x_827_, 2);
v_a_832_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_828_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_828_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
else
{
lean_dec_ref(v_e_807_);
goto v___jp_817_;
}
}
else
{
lean_object* v___x_840_; lean_object* v___x_841_; 
lean_dec(v_a_822_);
lean_dec_ref(v_e_807_);
v___x_840_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_841_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_840_, v___f_820_, v_a_809_);
return v___x_841_;
}
}
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec_ref(v___f_820_);
lean_dec_ref(v_e_807_);
v_a_842_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_821_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_821_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
v___jp_817_:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = lean_box(0);
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
return v___x_819_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___boxed(lean_object* v_e_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(v_e_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
lean_dec(v_a_858_);
lean_dec_ref(v_a_857_);
lean_dec(v_a_856_);
lean_dec_ref(v_a_855_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_a_852_);
lean_dec(v_a_851_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId(lean_object* v_e_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(v_e_861_, v_a_862_, v_a_863_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___boxed(lean_object* v_e_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId(v_e_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_);
lean_dec(v_a_886_);
lean_dec_ref(v_a_885_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec(v_a_878_);
lean_dec(v_a_877_);
lean_dec(v_a_876_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0(lean_object* v_00_u03b2_889_, lean_object* v_x_890_, lean_object* v_x_891_, lean_object* v_x_892_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0___redArg(v_x_890_, v_x_891_, v_x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0(lean_object* v_00_u03b2_894_, lean_object* v_x_895_, size_t v_x_896_, size_t v_x_897_, lean_object* v_x_898_, lean_object* v_x_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(v_x_895_, v_x_896_, v_x_897_, v_x_898_, v_x_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_901_, lean_object* v_x_902_, lean_object* v_x_903_, lean_object* v_x_904_, lean_object* v_x_905_, lean_object* v_x_906_){
_start:
{
size_t v_x_7788__boxed_907_; size_t v_x_7789__boxed_908_; lean_object* v_res_909_; 
v_x_7788__boxed_907_ = lean_unbox_usize(v_x_903_);
lean_dec(v_x_903_);
v_x_7789__boxed_908_ = lean_unbox_usize(v_x_904_);
lean_dec(v_x_904_);
v_res_909_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0(v_00_u03b2_901_, v_x_902_, v_x_7788__boxed_907_, v_x_7789__boxed_908_, v_x_905_, v_x_906_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_910_, lean_object* v_n_911_, lean_object* v_k_912_, lean_object* v_v_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1___redArg(v_n_911_, v_k_912_, v_v_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_915_, size_t v_depth_916_, lean_object* v_keys_917_, lean_object* v_vals_918_, lean_object* v_heq_919_, lean_object* v_i_920_, lean_object* v_entries_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_916_, v_keys_917_, v_vals_918_, v_i_920_, v_entries_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_923_, lean_object* v_depth_924_, lean_object* v_keys_925_, lean_object* v_vals_926_, lean_object* v_heq_927_, lean_object* v_i_928_, lean_object* v_entries_929_){
_start:
{
size_t v_depth_boxed_930_; lean_object* v_res_931_; 
v_depth_boxed_930_ = lean_unbox_usize(v_depth_924_);
lean_dec(v_depth_924_);
v_res_931_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2(v_00_u03b2_923_, v_depth_boxed_930_, v_keys_925_, v_vals_926_, v_heq_927_, v_i_928_, v_entries_929_);
lean_dec_ref(v_vals_926_);
lean_dec_ref(v_keys_925_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_932_, lean_object* v_x_933_, lean_object* v_x_934_, lean_object* v_x_935_, lean_object* v_x_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_933_, v_x_934_, v_x_935_, v_x_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___lam__0(lean_object* v_e_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(v_e_938_, v___y_939_, v___y_940_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___lam__0___boxed(lean_object* v_e_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___lam__0(v_e_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec(v___y_954_);
lean_dec(v___y_953_);
return v_res_965_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0___closed__1(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0___closed__0));
v___x_970_ = l_Lean_stringToMessageData(v___x_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0(lean_object* v___x_971_, lean_object* v___x_972_, lean_object* v___f_973_, lean_object* v___x_974_, lean_object* v___f_975_, lean_object* v_e_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_976_, v___y_978_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; uint8_t v___x_991_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref_known(v___x_989_, 1);
v___x_991_ = lean_unbox(v_a_990_);
lean_dec(v_a_990_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_1449__overap_995_; lean_object* v___x_996_; 
v___x_992_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0___closed__1);
lean_inc_ref(v_e_976_);
v___x_993_ = l_Lean_indentExpr(v_e_976_);
v___x_994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
lean_inc_ref(v___x_971_);
v___x_1449__overap_995_ = l_Lean_throwError___redArg(v___x_971_, v___x_972_, v___x_994_);
lean_inc(v___y_987_);
lean_inc_ref(v___y_986_);
lean_inc(v___y_985_);
lean_inc_ref(v___y_984_);
lean_inc(v___y_983_);
lean_inc_ref(v___y_982_);
lean_inc(v___y_981_);
lean_inc_ref(v___y_980_);
lean_inc(v___y_979_);
lean_inc(v___y_978_);
lean_inc(v___y_977_);
v___x_996_ = lean_apply_12(v___x_1449__overap_995_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, lean_box(0));
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v___x_1452__overap_997_; lean_object* v___x_998_; 
lean_dec_ref_known(v___x_996_, 1);
v___x_1452__overap_997_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(v___f_973_, v___x_971_, v___x_974_, v___f_975_, v_e_976_);
lean_inc(v___y_987_);
lean_inc_ref(v___y_986_);
lean_inc(v___y_985_);
lean_inc_ref(v___y_984_);
lean_inc(v___y_983_);
lean_inc_ref(v___y_982_);
lean_inc(v___y_981_);
lean_inc_ref(v___y_980_);
lean_inc(v___y_979_);
lean_inc(v___y_978_);
lean_inc(v___y_977_);
v___x_998_ = lean_apply_12(v___x_1452__overap_997_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, lean_box(0));
return v___x_998_;
}
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
lean_dec_ref(v_e_976_);
lean_dec_ref(v___f_975_);
lean_dec_ref(v___x_974_);
lean_dec(v___f_973_);
lean_dec_ref(v___x_971_);
v_a_999_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_996_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_996_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
else
{
lean_object* v___x_1456__overap_1007_; lean_object* v___x_1008_; 
lean_dec_ref(v___x_972_);
v___x_1456__overap_1007_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(v___f_973_, v___x_971_, v___x_974_, v___f_975_, v_e_976_);
lean_inc(v___y_987_);
lean_inc_ref(v___y_986_);
lean_inc(v___y_985_);
lean_inc_ref(v___y_984_);
lean_inc(v___y_983_);
lean_inc_ref(v___y_982_);
lean_inc(v___y_981_);
lean_inc_ref(v___y_980_);
lean_inc(v___y_979_);
lean_inc(v___y_978_);
lean_inc(v___y_977_);
v___x_1008_ = lean_apply_12(v___x_1456__overap_1007_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, lean_box(0));
return v___x_1008_;
}
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
lean_dec_ref(v_e_976_);
lean_dec_ref(v___f_975_);
lean_dec_ref(v___x_974_);
lean_dec(v___f_973_);
lean_dec_ref(v___x_972_);
lean_dec_ref(v___x_971_);
v_a_1009_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_989_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_989_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0___boxed(lean_object** _args){
lean_object* v___x_1017_ = _args[0];
lean_object* v___x_1018_ = _args[1];
lean_object* v___f_1019_ = _args[2];
lean_object* v___x_1020_ = _args[3];
lean_object* v___f_1021_ = _args[4];
lean_object* v_e_1022_ = _args[5];
lean_object* v___y_1023_ = _args[6];
lean_object* v___y_1024_ = _args[7];
lean_object* v___y_1025_ = _args[8];
lean_object* v___y_1026_ = _args[9];
lean_object* v___y_1027_ = _args[10];
lean_object* v___y_1028_ = _args[11];
lean_object* v___y_1029_ = _args[12];
lean_object* v___y_1030_ = _args[13];
lean_object* v___y_1031_ = _args[14];
lean_object* v___y_1032_ = _args[15];
lean_object* v___y_1033_ = _args[16];
lean_object* v___y_1034_ = _args[17];
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0(v___x_1017_, v___x_1018_, v___f_1019_, v___x_1020_, v___f_1021_, v_e_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec(v___y_1023_);
return v_res_1035_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__0(void){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = l_instMonadEIO___redArg();
return v___x_1036_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__1(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__0);
v___x_1038_ = l_StateRefT_x27_instMonad___redArg(v___x_1037_);
return v___x_1038_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__7(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___f_1045_; 
v___x_1044_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_1045_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1045_, 0, v___x_1044_);
return v___f_1045_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__8(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___f_1047_; 
v___x_1046_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_1047_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1047_, 0, v___x_1046_);
return v___f_1047_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__9(void){
_start:
{
lean_object* v___f_1048_; lean_object* v___f_1049_; lean_object* v___x_1050_; 
v___f_1048_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__8, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__8_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__8);
v___f_1049_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__7, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__7_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__7);
v___x_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___f_1049_);
lean_ctor_set(v___x_1050_, 1, v___f_1048_);
return v___x_1050_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__10(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___f_1052_; 
v___x_1051_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__9, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__9_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__9);
v___f_1052_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1052_, 0, v___x_1051_);
return v___f_1052_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__11(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___f_1054_; 
v___x_1053_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__9, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__9_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__9);
v___f_1054_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1054_, 0, v___x_1053_);
return v___f_1054_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__12(void){
_start:
{
lean_object* v___f_1055_; lean_object* v___f_1056_; lean_object* v___x_1057_; 
v___f_1055_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__11, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__11_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__11);
v___f_1056_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__10, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__10_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__10);
v___x_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___f_1056_);
lean_ctor_set(v___x_1057_, 1, v___f_1055_);
return v___x_1057_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__13(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___f_1059_; 
v___x_1058_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__12);
v___f_1059_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1059_, 0, v___x_1058_);
return v___f_1059_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__14(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___f_1061_; 
v___x_1060_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__12);
v___f_1061_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1061_, 0, v___x_1060_);
return v___f_1061_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__15(void){
_start:
{
lean_object* v___f_1062_; lean_object* v___f_1063_; lean_object* v___x_1064_; 
v___f_1062_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__14, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__14_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__14);
v___f_1063_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__13, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__13_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__13);
v___x_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___f_1063_);
lean_ctor_set(v___x_1064_, 1, v___f_1062_);
return v___x_1064_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__16(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___f_1066_; 
v___x_1065_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__15, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__15_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__15);
v___f_1066_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1066_, 0, v___x_1065_);
return v___f_1066_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__17(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___f_1068_; 
v___x_1067_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__15, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__15_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__15);
v___f_1068_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1068_, 0, v___x_1067_);
return v___f_1068_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__18(void){
_start:
{
lean_object* v___f_1069_; lean_object* v___f_1070_; lean_object* v___x_1071_; 
v___f_1069_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__17, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__17_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__17);
v___f_1070_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__16, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__16_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__16);
v___x_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___f_1070_);
lean_ctor_set(v___x_1071_, 1, v___f_1069_);
return v___x_1071_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__19(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___f_1073_; 
v___x_1072_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__18, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__18_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__18);
v___f_1073_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1073_, 0, v___x_1072_);
return v___f_1073_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__20(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___f_1075_; 
v___x_1074_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__18, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__18_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__18);
v___f_1075_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1075_, 0, v___x_1074_);
return v___f_1075_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__21(void){
_start:
{
lean_object* v___f_1076_; lean_object* v___f_1077_; lean_object* v___x_1078_; 
v___f_1076_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__20, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__20_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__20);
v___f_1077_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__19, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__19_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__19);
v___x_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___f_1077_);
lean_ctor_set(v___x_1078_, 1, v___f_1076_);
return v___x_1078_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__22(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___f_1080_; 
v___x_1079_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__21, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__21_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__21);
v___f_1080_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1080_, 0, v___x_1079_);
return v___f_1080_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__23(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___f_1082_; 
v___x_1081_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__21, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__21_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__21);
v___f_1082_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1082_, 0, v___x_1081_);
return v___f_1082_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__24(void){
_start:
{
lean_object* v___f_1083_; lean_object* v___f_1084_; lean_object* v___x_1085_; 
v___f_1083_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__23, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__23_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__23);
v___f_1084_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__22, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__22_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__22);
v___x_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___f_1084_);
lean_ctor_set(v___x_1085_, 1, v___f_1083_);
return v___x_1085_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__25(void){
_start:
{
lean_object* v___x_1086_; lean_object* v___f_1087_; 
v___x_1086_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__24, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__24_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__24);
v___f_1087_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1087_, 0, v___x_1086_);
return v___f_1087_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__26(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___f_1089_; 
v___x_1088_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__24, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__24_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__24);
v___f_1089_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1089_, 0, v___x_1088_);
return v___f_1089_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__27(void){
_start:
{
lean_object* v___f_1090_; lean_object* v___f_1091_; lean_object* v___x_1092_; 
v___f_1090_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__26, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__26_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__26);
v___f_1091_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__25, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__25_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__25);
v___x_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___f_1091_);
lean_ctor_set(v___x_1092_, 1, v___f_1090_);
return v___x_1092_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__28(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___f_1094_; 
v___x_1093_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__27, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__27_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__27);
v___f_1094_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1094_, 0, v___x_1093_);
return v___f_1094_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__29(void){
_start:
{
lean_object* v___x_1095_; lean_object* v___f_1096_; 
v___x_1095_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__27, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__27_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__27);
v___f_1096_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1096_, 0, v___x_1095_);
return v___f_1096_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__30(void){
_start:
{
lean_object* v___f_1097_; lean_object* v___f_1098_; lean_object* v___x_1099_; 
v___f_1097_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__29, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__29_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__29);
v___f_1098_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__28, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__28_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__28);
v___x_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___f_1098_);
lean_ctor_set(v___x_1099_, 1, v___f_1097_);
return v___x_1099_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__31(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___f_1101_; 
v___x_1100_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__30, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__30_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__30);
v___f_1101_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1101_, 0, v___x_1100_);
return v___f_1101_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__32(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___f_1103_; 
v___x_1102_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__30, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__30_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__30);
v___f_1103_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1103_, 0, v___x_1102_);
return v___f_1103_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__33(void){
_start:
{
lean_object* v___f_1104_; lean_object* v___f_1105_; lean_object* v___x_1106_; 
v___f_1104_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__32, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__32_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__32);
v___f_1105_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__31, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__31_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__31);
v___x_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___f_1105_);
lean_ctor_set(v___x_1106_, 1, v___f_1104_);
return v___x_1106_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__37(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1110_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1111_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__36));
v___x_1112_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__35));
v___x_1113_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1112_, v___x_1111_, v___x_1110_);
return v___x_1113_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__38(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___f_1115_; lean_object* v___f_1116_; lean_object* v___x_1117_; 
v___x_1114_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__37, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__37_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__37);
v___f_1115_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6));
v___f_1116_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__34));
v___x_1117_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1116_, v___f_1115_, v___x_1114_);
return v___x_1117_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__39(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1118_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__38, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__38_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__38);
v___x_1119_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__36));
v___x_1120_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__35));
v___x_1121_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1120_, v___x_1119_, v___x_1118_);
return v___x_1121_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__40(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___f_1123_; lean_object* v___f_1124_; lean_object* v___x_1125_; 
v___x_1122_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__39, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__39_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__39);
v___f_1123_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6));
v___f_1124_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__34));
v___x_1125_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1124_, v___f_1123_, v___x_1122_);
return v___x_1125_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__41(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1126_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__40, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__40_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__40);
v___x_1127_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__36));
v___x_1128_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__35));
v___x_1129_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1128_, v___x_1127_, v___x_1126_);
return v___x_1129_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__42(void){
_start:
{
lean_object* v___x_1130_; lean_object* v___f_1131_; lean_object* v___f_1132_; lean_object* v___x_1133_; 
v___x_1130_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__41, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__41_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__41);
v___f_1131_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6));
v___f_1132_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__34));
v___x_1133_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1132_, v___f_1131_, v___x_1130_);
return v___x_1133_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__43(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___f_1135_; lean_object* v___f_1136_; lean_object* v___x_1137_; 
v___x_1134_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__42, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__42_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__42);
v___f_1135_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6));
v___f_1136_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__34));
v___x_1137_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1136_, v___f_1135_, v___x_1134_);
return v___x_1137_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__44(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1138_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__43, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__43_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__43);
v___x_1139_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__36));
v___x_1140_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__35));
v___x_1141_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1140_, v___x_1139_, v___x_1138_);
return v___x_1141_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__45(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___f_1143_; lean_object* v___f_1144_; lean_object* v___x_1145_; 
v___x_1142_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__44, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__44_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__44);
v___f_1143_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6));
v___f_1144_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__34));
v___x_1145_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1144_, v___f_1143_, v___x_1142_);
return v___x_1145_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__48(void){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___f_1152_; 
v___x_1150_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__36));
v___x_1151_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_1152_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1152_, 0, v___x_1151_);
lean_closure_set(v___f_1152_, 1, v___x_1150_);
return v___f_1152_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__49(void){
_start:
{
lean_object* v___f_1153_; lean_object* v___f_1154_; lean_object* v___f_1155_; 
v___f_1153_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6));
v___f_1154_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__48, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__48_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__48);
v___f_1155_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1155_, 0, v___f_1154_);
lean_closure_set(v___f_1155_, 1, v___f_1153_);
return v___f_1155_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__50(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___f_1157_; lean_object* v___f_1158_; 
v___x_1156_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__36));
v___f_1157_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__49, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__49_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__49);
v___f_1158_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1158_, 0, v___f_1157_);
lean_closure_set(v___f_1158_, 1, v___x_1156_);
return v___f_1158_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__51(void){
_start:
{
lean_object* v___f_1159_; lean_object* v___f_1160_; lean_object* v___f_1161_; 
v___f_1159_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6));
v___f_1160_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__50, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__50_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__50);
v___f_1161_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1161_, 0, v___f_1160_);
lean_closure_set(v___f_1161_, 1, v___f_1159_);
return v___f_1161_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__52(void){
_start:
{
lean_object* v___f_1162_; lean_object* v___f_1163_; lean_object* v___f_1164_; 
v___f_1162_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6));
v___f_1163_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__51, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__51_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__51);
v___f_1164_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1164_, 0, v___f_1163_);
lean_closure_set(v___f_1164_, 1, v___f_1162_);
return v___f_1164_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__53(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___f_1166_; lean_object* v___f_1167_; 
v___x_1165_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__36));
v___f_1166_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__52, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__52_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__52);
v___f_1167_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1167_, 0, v___f_1166_);
lean_closure_set(v___f_1167_, 1, v___x_1165_);
return v___f_1167_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__54(void){
_start:
{
lean_object* v___f_1168_; lean_object* v___f_1169_; lean_object* v___f_1170_; 
v___f_1168_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__6));
v___f_1169_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__53, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__53_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__53);
v___f_1170_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1170_, 0, v___f_1169_);
lean_closure_set(v___f_1170_, 1, v___f_1168_);
return v___f_1170_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM(void){
_start:
{
lean_object* v___x_1171_; lean_object* v_toApplicative_1172_; lean_object* v_toFunctor_1173_; lean_object* v_toSeq_1174_; lean_object* v_toSeqLeft_1175_; lean_object* v_toSeqRight_1176_; lean_object* v___f_1177_; lean_object* v___f_1178_; lean_object* v___f_1179_; lean_object* v___f_1180_; lean_object* v___x_1181_; lean_object* v___f_1182_; lean_object* v___f_1183_; lean_object* v___f_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v_toApplicative_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1232_; 
v___x_1171_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__1);
v_toApplicative_1172_ = lean_ctor_get(v___x_1171_, 0);
v_toFunctor_1173_ = lean_ctor_get(v_toApplicative_1172_, 0);
v_toSeq_1174_ = lean_ctor_get(v_toApplicative_1172_, 2);
v_toSeqLeft_1175_ = lean_ctor_get(v_toApplicative_1172_, 3);
v_toSeqRight_1176_ = lean_ctor_get(v_toApplicative_1172_, 4);
v___f_1177_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__2));
v___f_1178_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__3));
lean_inc_ref_n(v_toFunctor_1173_, 2);
v___f_1179_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1179_, 0, v_toFunctor_1173_);
v___f_1180_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1180_, 0, v_toFunctor_1173_);
v___x_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___f_1179_);
lean_ctor_set(v___x_1181_, 1, v___f_1180_);
lean_inc(v_toSeqRight_1176_);
v___f_1182_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1182_, 0, v_toSeqRight_1176_);
lean_inc(v_toSeqLeft_1175_);
v___f_1183_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1183_, 0, v_toSeqLeft_1175_);
lean_inc(v_toSeq_1174_);
v___f_1184_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1184_, 0, v_toSeq_1174_);
v___x_1185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1181_);
lean_ctor_set(v___x_1185_, 1, v___f_1177_);
lean_ctor_set(v___x_1185_, 2, v___f_1184_);
lean_ctor_set(v___x_1185_, 3, v___f_1183_);
lean_ctor_set(v___x_1185_, 4, v___f_1182_);
v___x_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
lean_ctor_set(v___x_1186_, 1, v___f_1178_);
v___x_1187_ = l_StateRefT_x27_instMonad___redArg(v___x_1186_);
v_toApplicative_1188_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1232_ == 0)
{
lean_object* v_unused_1233_; 
v_unused_1233_ = lean_ctor_get(v___x_1187_, 1);
lean_dec(v_unused_1233_);
v___x_1190_ = v___x_1187_;
v_isShared_1191_ = v_isSharedCheck_1232_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_toApplicative_1188_);
lean_dec(v___x_1187_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1232_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v_toFunctor_1192_; lean_object* v_toSeq_1193_; lean_object* v_toSeqLeft_1194_; lean_object* v_toSeqRight_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1230_; 
v_toFunctor_1192_ = lean_ctor_get(v_toApplicative_1188_, 0);
v_toSeq_1193_ = lean_ctor_get(v_toApplicative_1188_, 2);
v_toSeqLeft_1194_ = lean_ctor_get(v_toApplicative_1188_, 3);
v_toSeqRight_1195_ = lean_ctor_get(v_toApplicative_1188_, 4);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_toApplicative_1188_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; 
v_unused_1231_ = lean_ctor_get(v_toApplicative_1188_, 1);
lean_dec(v_unused_1231_);
v___x_1197_ = v_toApplicative_1188_;
v_isShared_1198_ = v_isSharedCheck_1230_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_toSeqRight_1195_);
lean_inc(v_toSeqLeft_1194_);
lean_inc(v_toSeq_1193_);
lean_inc(v_toFunctor_1192_);
lean_dec(v_toApplicative_1188_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1230_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___f_1199_; lean_object* v___f_1200_; lean_object* v___f_1201_; lean_object* v___f_1202_; lean_object* v___x_1203_; lean_object* v___f_1204_; lean_object* v___f_1205_; lean_object* v___f_1206_; lean_object* v___x_1208_; 
v___f_1199_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__4));
v___f_1200_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__5));
lean_inc_ref(v_toFunctor_1192_);
v___f_1201_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1201_, 0, v_toFunctor_1192_);
v___f_1202_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1202_, 0, v_toFunctor_1192_);
v___x_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___f_1201_);
lean_ctor_set(v___x_1203_, 1, v___f_1202_);
v___f_1204_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1204_, 0, v_toSeqRight_1195_);
v___f_1205_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1205_, 0, v_toSeqLeft_1194_);
v___f_1206_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1206_, 0, v_toSeq_1193_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 4, v___f_1204_);
lean_ctor_set(v___x_1197_, 3, v___f_1205_);
lean_ctor_set(v___x_1197_, 2, v___f_1206_);
lean_ctor_set(v___x_1197_, 1, v___f_1199_);
lean_ctor_set(v___x_1197_, 0, v___x_1203_);
v___x_1208_ = v___x_1197_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v___f_1199_);
lean_ctor_set(v_reuseFailAlloc_1229_, 2, v___f_1206_);
lean_ctor_set(v_reuseFailAlloc_1229_, 3, v___f_1205_);
lean_ctor_set(v_reuseFailAlloc_1229_, 4, v___f_1204_);
v___x_1208_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1210_; 
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 1, v___f_1200_);
lean_ctor_set(v___x_1190_, 0, v___x_1208_);
v___x_1210_ = v___x_1190_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1208_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v___f_1200_);
v___x_1210_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v_toMonadRef_1221_; lean_object* v___f_1222_; lean_object* v___f_1223_; lean_object* v___f_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___f_1227_; 
v___x_1211_ = l_StateRefT_x27_instMonad___redArg(v___x_1210_);
v___x_1212_ = l_ReaderT_instMonad___redArg(v___x_1211_);
v___x_1213_ = l_StateRefT_x27_instMonad___redArg(v___x_1212_);
v___x_1214_ = l_ReaderT_instMonad___redArg(v___x_1213_);
v___x_1215_ = l_ReaderT_instMonad___redArg(v___x_1214_);
v___x_1216_ = l_StateRefT_x27_instMonad___redArg(v___x_1215_);
v___x_1217_ = l_ReaderT_instMonad___redArg(v___x_1216_);
v___x_1218_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateNonCommSemiringM;
v___x_1219_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__33, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__33_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__33);
v___x_1220_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__45, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__45_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__45);
v_toMonadRef_1221_ = lean_ctor_get(v___x_1220_, 0);
v___f_1222_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__47));
v___f_1223_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___closed__0));
v___f_1224_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__54, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__54_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___closed__54);
lean_inc_ref(v___x_1217_);
v___x_1225_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1224_, v___x_1217_);
lean_inc_ref(v_toMonadRef_1221_);
v___x_1226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1219_);
lean_ctor_set(v___x_1226_, 1, v_toMonadRef_1221_);
lean_ctor_set(v___x_1226_, 2, v___x_1225_);
v___f_1227_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommSemiringM___lam__0___boxed), 18, 5);
lean_closure_set(v___f_1227_, 0, v___x_1217_);
lean_closure_set(v___f_1227_, 1, v___x_1226_);
lean_closure_set(v___f_1227_, 2, v___f_1222_);
lean_closure_set(v___f_1227_, 3, v___x_1218_);
lean_closure_set(v___f_1227_, 4, v___f_1223_);
return v___f_1227_;
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
