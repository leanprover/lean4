// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.NonCommRingM
// Imports: public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
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
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default;
lean_object* l_Array_rightpad___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getNCRing(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getArithState___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Sym_Arith_arithExt;
lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__1___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__1_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "`grind` internal error, invalid ringId"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "expression in two different rings"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "`grind` internal error, ring term has not been internalized"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0___boxed(lean_object**);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__1;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__3_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__4_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__5_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__7;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__8;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__9;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__10;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__11;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__12;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__13;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__14;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__15;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__16;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__17;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__18;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__19;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__20;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__21;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__22;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__23;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__24;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__25;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__26;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__27;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__28;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__29;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__30;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__31;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__32;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__33;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__34 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__34_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__35 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__35_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__36 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__36_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__37;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__38;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__39;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__40;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__41;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__42;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__43;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__44;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__45;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__46 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__46_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__46_value),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__6_value)} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__47 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__47_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__48;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__49;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__50;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__51;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__52;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__53;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__54;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM;
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___redArg(lean_object* v_ringId_1_, lean_object* v_x_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
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
v___x_14_ = lean_apply_12(v_x_2_, v_ringId_1_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, lean_box(0));
return v___x_14_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ringId_1_ = stack[0].m_obj;
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
v_res_15_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___redArg(v_ringId_1_, v_x_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
stack->m_obj
 = v_res_15_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___redArg___boxed(lean_object* v_ringId_16_, lean_object* v_x_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___redArg(v_ringId_16_, v_x_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_, v_a_27_);
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
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run(lean_object* v_00_u03b1_30_, lean_object* v_ringId_31_, lean_object* v_x_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_){
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
v___x_44_ = lean_apply_12(v_x_32_, v_ringId_31_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, lean_box(0));
return v___x_44_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_ringId_31_ = stack[1].m_obj;
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
v_res_45_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run(lean_box(0), v_ringId_31_, v_x_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___boxed(lean_object* v_00_u03b1_46_, lean_object* v_ringId_47_, lean_object* v_x_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run(v_00_u03b1_46_, v_ringId_47_, v_x_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_);
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
lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__0(lean_object* v_e_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
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
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__0_0interp(lean_interpreter_value* stack)
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
v_res_77_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__0(v_e_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_);
stack->m_obj
 = v_res_77_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__0___boxed(lean_object* v_e_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__0(v_e_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
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
lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__1(lean_object* v_e_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_e_92_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
return v___x_105_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__1_0interp(lean_interpreter_value* stack)
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
v_res_106_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__1(v_e_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
stack->m_obj
 = v_res_106_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__1___boxed(lean_object* v_e_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__1(v_e_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_);
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
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0_spec__0(lean_object* v_msgData_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
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
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_127_ = stack[0].m_obj;
lean_object* v___y_128_ = stack[1].m_obj;
lean_object* v___y_129_ = stack[2].m_obj;
lean_object* v___y_130_ = stack[3].m_obj;
lean_object* v___y_131_ = stack[4].m_obj;
lean_object* v_res_145_;
v_res_145_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0_spec__0(v_msgData_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_);
stack->m_obj
 = v_res_145_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0_spec__0___boxed(lean_object* v_msgData_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0_spec__0(v_msgData_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
return v_res_152_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg(lean_object* v_msg_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_ref_159_; lean_object* v___x_160_; lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_169_; 
v_ref_159_ = lean_ctor_get(v___y_156_, 2);
v___x_160_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0_spec__0(v_msg_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
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
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_153_ = stack[0].m_obj;
lean_object* v___y_154_ = stack[1].m_obj;
lean_object* v___y_155_ = stack[2].m_obj;
lean_object* v___y_156_ = stack[3].m_obj;
lean_object* v___y_157_ = stack[4].m_obj;
lean_object* v_res_170_;
v_res_170_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg(v_msg_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
stack->m_obj
 = v_res_170_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg___boxed(lean_object* v_msg_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg(v_msg_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
return v_res_177_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__1(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__0));
v___x_180_ = l_Lean_stringToMessageData(v___x_179_);
return v___x_180_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_){
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
lean_object* v_ncRings_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v_ncRings_198_ = lean_ctor_get(v_a_194_, 3);
lean_inc_ref(v_ncRings_198_);
lean_dec(v_a_194_);
v___x_199_ = lean_array_get_size(v_ncRings_198_);
v___x_200_ = lean_nat_dec_lt(v_a_181_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_dec_ref(v_ncRings_198_);
lean_del_object(v___x_196_);
v___x_201_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__1);
v___x_202_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg(v___x_201_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
return v___x_202_;
}
else
{
lean_object* v___x_203_; lean_object* v___x_205_; 
v___x_203_ = lean_array_fget(v_ncRings_198_, v_a_181_);
lean_dec_ref(v_ncRings_198_);
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
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_0interp(lean_interpreter_value* stack)
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
v_res_216_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
stack->m_obj
 = v_res_216_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___boxed(lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_);
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
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0(lean_object* v_00_u03b1_230_, lean_object* v_msg_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg(v_msg_231_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
return v___x_244_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0_0interp(lean_interpreter_value* stack)
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
v_res_245_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0(lean_box(0), v_msg_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
stack->m_obj
 = v_res_245_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___boxed(lean_object* v_00_u03b1_246_, lean_object* v_msg_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0(v_00_u03b1_246_, v_msg_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___lam__0(lean_object* v_a_261_, lean_object* v_f_262_, lean_object* v_s_263_){
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
v___x_272_ = lean_array_get_size(v_ncRings_267_);
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
v_v_277_ = lean_array_fget(v_ncRings_267_, v_a_261_);
v___x_278_ = lean_box(0);
v_xs_x27_279_ = lean_array_fset(v_ncRings_267_, v_a_261_, v___x_278_);
v___x_280_ = lean_apply_1(v_f_262_, v_v_277_);
v___x_281_ = lean_array_fset(v_xs_x27_279_, v_a_261_, v___x_280_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 3, v___x_281_);
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
lean_ctor_set(v_reuseFailAlloc_284_, 3, v___x_281_);
lean_ctor_set(v_reuseFailAlloc_284_, 4, v_ncSemirings_268_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___lam__0___boxed(lean_object* v_a_294_, lean_object* v_f_295_, lean_object* v_s_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___lam__0(v_a_294_, v_f_295_, v_s_296_);
lean_dec(v_a_294_);
return v_res_297_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(lean_object* v_f_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v___f_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
lean_inc(v_a_299_);
v___f_302_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_302_, 0, v_a_299_);
lean_closure_set(v___f_302_, 1, v_f_298_);
v___x_303_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_304_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_303_, v___f_302_, v_a_300_);
return v___x_304_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_298_ = stack[0].m_obj;
lean_object* v_a_299_ = stack[1].m_obj;
lean_object* v_a_300_ = stack[2].m_obj;
lean_object* v_res_305_;
v_res_305_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(v_f_298_, v_a_299_, v_a_300_);
stack->m_obj
 = v_res_305_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___boxed(lean_object* v_f_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(v_f_306_, v_a_307_, v_a_308_);
lean_dec(v_a_308_);
lean_dec(v_a_307_);
return v_res_310_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing(lean_object* v_f_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(v_f_311_, v_a_312_, v_a_318_);
return v___x_324_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing_0interp(lean_interpreter_value* stack)
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
v_res_325_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing(v_f_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
stack->m_obj
 = v_res_325_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___boxed(lean_object* v_f_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing(v_f_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
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
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__0));
v___x_342_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___boxed), 12, 0);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___x_341_);
return v___x_343_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM(void){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1);
return v___x_344_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___redArg(lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_){
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
v___x_354_ = l_Lean_Meta_Grind_Arith_CommRing_State_getNCRing(v_a_350_, v_a_345_);
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
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_345_ = stack[0].m_obj;
lean_object* v_a_346_ = stack[1].m_obj;
lean_object* v_a_347_ = stack[2].m_obj;
lean_object* v_res_367_;
v_res_367_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___redArg(v_a_345_, v_a_346_, v_a_347_);
stack->m_obj
 = v_res_367_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___redArg___boxed(lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___redArg(v_a_368_, v_a_369_, v_a_370_);
lean_dec_ref(v_a_370_);
lean_dec(v_a_369_);
lean_dec(v_a_368_);
return v_res_372_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState(lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___redArg(v_a_373_, v_a_374_, v_a_382_);
return v___x_385_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState_0interp(lean_interpreter_value* stack)
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
v_res_386_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState(v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_);
stack->m_obj
 = v_res_386_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___boxed(lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState(v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg___lam__0(lean_object* v_a_400_, lean_object* v_f_401_, lean_object* v_s_402_){
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
v___x_418_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default;
v___x_419_ = l_Array_rightpad___redArg(v___x_417_, v___x_418_, v_ncRings_407_);
lean_dec(v___x_417_);
v___x_420_ = lean_array_get_size(v___x_419_);
v___x_421_ = lean_nat_dec_lt(v_a_400_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_423_; 
lean_dec_ref(v_f_401_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 4, v___x_419_);
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
lean_ctor_set(v_reuseFailAlloc_424_, 4, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_424_, 5, v_exprToNCRingId_408_);
lean_ctor_set(v_reuseFailAlloc_424_, 6, v_ncSemirings_409_);
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
lean_ctor_set(v___x_414_, 4, v___x_429_);
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
lean_ctor_set(v_reuseFailAlloc_432_, 4, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_432_, 5, v_exprToNCRingId_408_);
lean_ctor_set(v_reuseFailAlloc_432_, 6, v_ncSemirings_409_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg___lam__0___boxed(lean_object* v_a_434_, lean_object* v_f_435_, lean_object* v_s_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg___lam__0(v_a_434_, v_f_435_, v_s_436_);
lean_dec(v_a_434_);
return v_res_437_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg(lean_object* v_f_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
lean_object* v___f_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
lean_inc(v_a_439_);
v___f_442_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_442_, 0, v_a_439_);
lean_closure_set(v___f_442_, 1, v_f_438_);
v___x_443_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_444_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_443_, v___f_442_, v_a_440_);
return v___x_444_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_438_ = stack[0].m_obj;
lean_object* v_a_439_ = stack[1].m_obj;
lean_object* v_a_440_ = stack[2].m_obj;
lean_object* v_res_445_;
v_res_445_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg(v_f_438_, v_a_439_, v_a_440_);
stack->m_obj
 = v_res_445_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg___boxed(lean_object* v_f_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg(v_f_446_, v_a_447_, v_a_448_);
lean_dec(v_a_448_);
lean_dec(v_a_447_);
return v_res_450_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState(lean_object* v_f_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg(v_f_451_, v_a_452_, v_a_453_);
return v___x_464_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState_0interp(lean_interpreter_value* stack)
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
v_res_465_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState(v_f_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
stack->m_obj
 = v_res_465_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___boxed(lean_object* v_f_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState(v_f_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
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
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM___closed__1(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_481_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM___closed__0));
v___x_482_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___boxed), 12, 0);
v___x_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set(v___x_483_, 1, v___x_481_);
return v___x_483_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM(void){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM___closed__1);
return v___x_484_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___lam__0(lean_object* v___x_485_, lean_object* v_x_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___redArg(v___y_487_, v___y_488_, v___y_496_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_515_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_515_ == 0)
{
v___x_502_ = v___x_499_;
v_isShared_503_ = v_isSharedCheck_515_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_515_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v_vars_504_; lean_object* v_size_505_; uint8_t v___x_506_; 
v_vars_504_ = lean_ctor_get(v_a_500_, 0);
lean_inc_ref(v_vars_504_);
lean_dec(v_a_500_);
v_size_505_ = lean_ctor_get(v_vars_504_, 2);
v___x_506_ = lean_nat_dec_lt(v_x_486_, v_size_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_509_; 
lean_dec_ref(v_vars_504_);
v___x_507_ = l_outOfBounds___redArg(v___x_485_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_507_);
v___x_509_ = v___x_502_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_507_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
else
{
lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_511_ = l_Lean_PersistentArray_get_x21___redArg(v___x_485_, v_vars_504_, v_x_486_);
lean_dec_ref(v_vars_504_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_511_);
v___x_513_ = v___x_502_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
else
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
v_a_516_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_499_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_499_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_485_ = stack[0].m_obj;
lean_object* v_x_486_ = stack[1].m_obj;
lean_object* v___y_487_ = stack[2].m_obj;
lean_object* v___y_488_ = stack[3].m_obj;
lean_object* v___y_489_ = stack[4].m_obj;
lean_object* v___y_490_ = stack[5].m_obj;
lean_object* v___y_491_ = stack[6].m_obj;
lean_object* v___y_492_ = stack[7].m_obj;
lean_object* v___y_493_ = stack[8].m_obj;
lean_object* v___y_494_ = stack[9].m_obj;
lean_object* v___y_495_ = stack[10].m_obj;
lean_object* v___y_496_ = stack[11].m_obj;
lean_object* v___y_497_ = stack[12].m_obj;
lean_object* v_res_524_;
v_res_524_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___lam__0(v___x_485_, v_x_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
stack->m_obj
 = v_res_524_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___lam__0___boxed(lean_object* v___x_525_, lean_object* v_x_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___lam__0(v___x_525_, v_x_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec(v___y_528_);
lean_dec(v___y_527_);
lean_dec(v_x_526_);
lean_dec_ref(v___x_525_);
return v_res_539_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___closed__0(void){
_start:
{
lean_object* v___x_540_; lean_object* v___f_541_; 
v___x_540_ = l_Lean_instInhabitedExpr;
v___f_541_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___lam__0___boxed), 14, 1);
lean_closure_set(v___f_541_, 0, v___x_540_);
return v___f_541_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM(void){
_start:
{
lean_object* v___f_542_; 
v___f_542_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___closed__0);
return v___f_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_543_, lean_object* v_vals_544_, lean_object* v_i_545_, lean_object* v_k_546_){
_start:
{
lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_547_ = lean_array_get_size(v_keys_543_);
v___x_548_ = lean_nat_dec_lt(v_i_545_, v___x_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; 
lean_dec(v_i_545_);
v___x_549_ = lean_box(0);
return v___x_549_;
}
else
{
lean_object* v_k_x27_550_; size_t v___x_551_; size_t v___x_552_; uint8_t v___x_553_; 
v_k_x27_550_ = lean_array_fget_borrowed(v_keys_543_, v_i_545_);
v___x_551_ = lean_ptr_addr(v_k_546_);
v___x_552_ = lean_ptr_addr(v_k_x27_550_);
v___x_553_ = lean_usize_dec_eq(v___x_551_, v___x_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = lean_unsigned_to_nat(1u);
v___x_555_ = lean_nat_add(v_i_545_, v___x_554_);
lean_dec(v_i_545_);
v_i_545_ = v___x_555_;
goto _start;
}
else
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_array_fget_borrowed(v_vals_544_, v_i_545_);
lean_dec(v_i_545_);
lean_inc(v___x_557_);
v___x_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_559_, lean_object* v_vals_560_, lean_object* v_i_561_, lean_object* v_k_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_559_, v_vals_560_, v_i_561_, v_k_562_);
lean_dec_ref(v_k_562_);
lean_dec_ref(v_vals_560_);
lean_dec_ref(v_keys_559_);
return v_res_563_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg(lean_object* v_x_564_, size_t v_x_565_, lean_object* v_x_566_){
_start:
{
if (lean_obj_tag(v_x_564_) == 0)
{
lean_object* v_es_567_; lean_object* v___x_568_; size_t v___x_569_; size_t v___x_570_; lean_object* v_j_571_; lean_object* v___x_572_; 
v_es_567_ = lean_ctor_get(v_x_564_, 0);
v___x_568_ = lean_box(2);
v___x_569_ = ((size_t)31ULL);
v___x_570_ = lean_usize_land(v_x_565_, v___x_569_);
v_j_571_ = lean_usize_to_nat(v___x_570_);
v___x_572_ = lean_array_get_borrowed(v___x_568_, v_es_567_, v_j_571_);
lean_dec(v_j_571_);
switch(lean_obj_tag(v___x_572_))
{
case 0:
{
lean_object* v_key_573_; lean_object* v_val_574_; size_t v___x_575_; size_t v___x_576_; uint8_t v___x_577_; 
v_key_573_ = lean_ctor_get(v___x_572_, 0);
v_val_574_ = lean_ctor_get(v___x_572_, 1);
v___x_575_ = lean_ptr_addr(v_x_566_);
v___x_576_ = lean_ptr_addr(v_key_573_);
v___x_577_ = lean_usize_dec_eq(v___x_575_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; 
v___x_578_ = lean_box(0);
return v___x_578_;
}
else
{
lean_object* v___x_579_; 
lean_inc(v_val_574_);
v___x_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_579_, 0, v_val_574_);
return v___x_579_;
}
}
case 1:
{
lean_object* v_node_580_; size_t v___x_581_; size_t v___x_582_; 
v_node_580_ = lean_ctor_get(v___x_572_, 0);
v___x_581_ = ((size_t)5ULL);
v___x_582_ = lean_usize_shift_right(v_x_565_, v___x_581_);
v_x_564_ = v_node_580_;
v_x_565_ = v___x_582_;
goto _start;
}
default: 
{
lean_object* v___x_584_; 
v___x_584_ = lean_box(0);
return v___x_584_;
}
}
}
else
{
lean_object* v_ks_585_; lean_object* v_vs_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v_ks_585_ = lean_ctor_get(v_x_564_, 0);
v_vs_586_ = lean_ctor_get(v_x_564_, 1);
v___x_587_ = lean_unsigned_to_nat(0u);
v___x_588_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_585_, v_vs_586_, v___x_587_, v_x_566_);
return v___x_588_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_564_ = stack[0].m_obj;
size_t v_x_565_ = stack[1].m_num;
lean_object* v_x_566_ = stack[2].m_obj;
lean_object* v_res_589_;
v_res_589_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg(v_x_564_, v_x_565_, v_x_566_);
stack->m_obj
 = v_res_589_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_590_, lean_object* v_x_591_, lean_object* v_x_592_){
_start:
{
size_t v_x_916__boxed_593_; lean_object* v_res_594_; 
v_x_916__boxed_593_ = lean_unbox_usize(v_x_591_);
lean_dec(v_x_591_);
v_res_594_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg(v_x_590_, v_x_916__boxed_593_, v_x_592_);
lean_dec_ref(v_x_592_);
lean_dec_ref(v_x_590_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg(lean_object* v_x_595_, lean_object* v_x_596_){
_start:
{
size_t v___x_597_; size_t v___x_598_; size_t v___x_599_; uint64_t v___x_600_; size_t v___x_601_; lean_object* v___x_602_; 
v___x_597_ = lean_ptr_addr(v_x_596_);
v___x_598_ = ((size_t)3ULL);
v___x_599_ = lean_usize_shift_right(v___x_597_, v___x_598_);
v___x_600_ = lean_usize_to_uint64(v___x_599_);
v___x_601_ = lean_uint64_to_usize(v___x_600_);
v___x_602_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg(v_x_595_, v___x_601_, v_x_596_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg___boxed(lean_object* v_x_603_, lean_object* v_x_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg(v_x_603_, v_x_604_);
lean_dec_ref(v_x_604_);
lean_dec_ref(v_x_603_);
return v_res_605_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg(lean_object* v_e_606_, lean_object* v_a_607_, lean_object* v_a_608_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_607_, v_a_608_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_620_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_620_ == 0)
{
v___x_613_ = v___x_610_;
v_isShared_614_ = v_isSharedCheck_620_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_610_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_620_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v_exprToNCRingId_615_; lean_object* v___x_616_; lean_object* v___x_618_; 
v_exprToNCRingId_615_ = lean_ctor_get(v_a_611_, 5);
lean_inc_ref(v_exprToNCRingId_615_);
lean_dec(v_a_611_);
v___x_616_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg(v_exprToNCRingId_615_, v_e_606_);
lean_dec_ref(v_exprToNCRingId_615_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_616_);
v___x_618_ = v___x_613_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_616_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
v_a_621_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_610_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_610_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_606_ = stack[0].m_obj;
lean_object* v_a_607_ = stack[1].m_obj;
lean_object* v_a_608_ = stack[2].m_obj;
lean_object* v_res_629_;
v_res_629_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg(v_e_606_, v_a_607_, v_a_608_);
stack->m_obj
 = v_res_629_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg___boxed(lean_object* v_e_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg(v_e_630_, v_a_631_, v_a_632_);
lean_dec_ref(v_a_632_);
lean_dec(v_a_631_);
lean_dec_ref(v_e_630_);
return v_res_634_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f(lean_object* v_e_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg(v_e_635_, v_a_636_, v_a_644_);
return v___x_647_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_635_ = stack[0].m_obj;
lean_object* v_a_636_ = stack[1].m_obj;
lean_object* v_a_637_ = stack[2].m_obj;
lean_object* v_a_638_ = stack[3].m_obj;
lean_object* v_a_639_ = stack[4].m_obj;
lean_object* v_a_640_ = stack[5].m_obj;
lean_object* v_a_641_ = stack[6].m_obj;
lean_object* v_a_642_ = stack[7].m_obj;
lean_object* v_a_643_ = stack[8].m_obj;
lean_object* v_a_644_ = stack[9].m_obj;
lean_object* v_a_645_ = stack[10].m_obj;
lean_object* v_res_648_;
v_res_648_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f(v_e_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
stack->m_obj
 = v_res_648_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___boxed(lean_object* v_e_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f(v_e_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
lean_dec(v_a_659_);
lean_dec_ref(v_a_658_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
lean_dec(v_a_651_);
lean_dec(v_a_650_);
lean_dec_ref(v_e_649_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0(lean_object* v_00_u03b2_662_, lean_object* v_x_663_, lean_object* v_x_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg(v_x_663_, v_x_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___boxed(lean_object* v_00_u03b2_666_, lean_object* v_x_667_, lean_object* v_x_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0(v_00_u03b2_666_, v_x_667_, v_x_668_);
lean_dec_ref(v_x_668_);
lean_dec_ref(v_x_667_);
return v_res_669_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_670_, lean_object* v_x_671_, size_t v_x_672_, lean_object* v_x_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg(v_x_671_, v_x_672_, v_x_673_);
return v___x_674_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_671_ = stack[1].m_obj;
size_t v_x_672_ = stack[2].m_num;
lean_object* v_x_673_ = stack[3].m_obj;
lean_object* v_res_675_;
v_res_675_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0(lean_box(0), v_x_671_, v_x_672_, v_x_673_);
stack->m_obj
 = v_res_675_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_676_, lean_object* v_x_677_, lean_object* v_x_678_, lean_object* v_x_679_){
_start:
{
size_t v_x_1102__boxed_680_; lean_object* v_res_681_; 
v_x_1102__boxed_680_ = lean_unbox_usize(v_x_678_);
lean_dec(v_x_678_);
v_res_681_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0(v_00_u03b2_676_, v_x_677_, v_x_1102__boxed_680_, v_x_679_);
lean_dec_ref(v_x_679_);
lean_dec_ref(v_x_677_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_682_, lean_object* v_keys_683_, lean_object* v_vals_684_, lean_object* v_heq_685_, lean_object* v_i_686_, lean_object* v_k_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_683_, v_vals_684_, v_i_686_, v_k_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_689_, lean_object* v_keys_690_, lean_object* v_vals_691_, lean_object* v_heq_692_, lean_object* v_i_693_, lean_object* v_k_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_689_, v_keys_690_, v_vals_691_, v_heq_692_, v_i_693_, v_k_694_);
lean_dec_ref(v_k_694_);
lean_dec_ref(v_vals_691_);
lean_dec_ref(v_keys_690_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_696_, lean_object* v_x_697_, lean_object* v_x_698_, lean_object* v_x_699_){
_start:
{
lean_object* v_ks_700_; lean_object* v_vs_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_727_; 
v_ks_700_ = lean_ctor_get(v_x_696_, 0);
v_vs_701_ = lean_ctor_get(v_x_696_, 1);
v_isSharedCheck_727_ = !lean_is_exclusive(v_x_696_);
if (v_isSharedCheck_727_ == 0)
{
v___x_703_ = v_x_696_;
v_isShared_704_ = v_isSharedCheck_727_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_vs_701_);
lean_inc(v_ks_700_);
lean_dec(v_x_696_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_727_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_705_ = lean_array_get_size(v_ks_700_);
v___x_706_ = lean_nat_dec_lt(v_x_697_, v___x_705_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_710_; 
lean_dec(v_x_697_);
v___x_707_ = lean_array_push(v_ks_700_, v_x_698_);
v___x_708_ = lean_array_push(v_vs_701_, v_x_699_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 1, v___x_708_);
lean_ctor_set(v___x_703_, 0, v___x_707_);
v___x_710_ = v___x_703_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v___x_708_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
else
{
lean_object* v_k_x27_712_; size_t v___x_713_; size_t v___x_714_; uint8_t v___x_715_; 
v_k_x27_712_ = lean_array_fget_borrowed(v_ks_700_, v_x_697_);
v___x_713_ = lean_ptr_addr(v_x_698_);
v___x_714_ = lean_ptr_addr(v_k_x27_712_);
v___x_715_ = lean_usize_dec_eq(v___x_713_, v___x_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_717_; 
if (v_isShared_704_ == 0)
{
v___x_717_ = v___x_703_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_ks_700_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_vs_701_);
v___x_717_ = v_reuseFailAlloc_721_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_unsigned_to_nat(1u);
v___x_719_ = lean_nat_add(v_x_697_, v___x_718_);
lean_dec(v_x_697_);
v_x_696_ = v___x_717_;
v_x_697_ = v___x_719_;
goto _start;
}
}
else
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_725_; 
v___x_722_ = lean_array_fset(v_ks_700_, v_x_697_, v_x_698_);
v___x_723_ = lean_array_fset(v_vs_701_, v_x_697_, v_x_699_);
lean_dec(v_x_697_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 1, v___x_723_);
lean_ctor_set(v___x_703_, 0, v___x_722_);
v___x_725_ = v___x_703_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_728_, lean_object* v_k_729_, lean_object* v_v_730_){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = lean_unsigned_to_nat(0u);
v___x_732_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_728_, v___x_731_, v_k_729_, v_v_730_);
return v___x_732_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_733_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(lean_object* v_x_734_, size_t v_x_735_, size_t v_x_736_, lean_object* v_x_737_, lean_object* v_x_738_){
_start:
{
if (lean_obj_tag(v_x_734_) == 0)
{
lean_object* v_es_739_; size_t v___x_740_; size_t v___x_741_; lean_object* v_j_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v_es_739_ = lean_ctor_get(v_x_734_, 0);
v___x_740_ = ((size_t)31ULL);
v___x_741_ = lean_usize_land(v_x_735_, v___x_740_);
v_j_742_ = lean_usize_to_nat(v___x_741_);
v___x_743_ = lean_array_get_size(v_es_739_);
v___x_744_ = lean_nat_dec_lt(v_j_742_, v___x_743_);
if (v___x_744_ == 0)
{
lean_dec(v_j_742_);
lean_dec(v_x_738_);
lean_dec_ref(v_x_737_);
return v_x_734_;
}
else
{
lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_785_; 
lean_inc_ref(v_es_739_);
v_isSharedCheck_785_ = !lean_is_exclusive(v_x_734_);
if (v_isSharedCheck_785_ == 0)
{
lean_object* v_unused_786_; 
v_unused_786_ = lean_ctor_get(v_x_734_, 0);
lean_dec(v_unused_786_);
v___x_746_ = v_x_734_;
v_isShared_747_ = v_isSharedCheck_785_;
goto v_resetjp_745_;
}
else
{
lean_dec(v_x_734_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_785_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v_v_748_; lean_object* v___x_749_; lean_object* v_xs_x27_750_; lean_object* v___y_752_; 
v_v_748_ = lean_array_fget(v_es_739_, v_j_742_);
v___x_749_ = lean_box(0);
v_xs_x27_750_ = lean_array_fset(v_es_739_, v_j_742_, v___x_749_);
switch(lean_obj_tag(v_v_748_))
{
case 0:
{
lean_object* v_key_757_; lean_object* v_val_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_770_; 
v_key_757_ = lean_ctor_get(v_v_748_, 0);
v_val_758_ = lean_ctor_get(v_v_748_, 1);
v_isSharedCheck_770_ = !lean_is_exclusive(v_v_748_);
if (v_isSharedCheck_770_ == 0)
{
v___x_760_ = v_v_748_;
v_isShared_761_ = v_isSharedCheck_770_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_val_758_);
lean_inc(v_key_757_);
lean_dec(v_v_748_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_770_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
size_t v___x_762_; size_t v___x_763_; uint8_t v___x_764_; 
v___x_762_ = lean_ptr_addr(v_x_737_);
v___x_763_ = lean_ptr_addr(v_key_757_);
v___x_764_ = lean_usize_dec_eq(v___x_762_, v___x_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; lean_object* v___x_766_; 
lean_del_object(v___x_760_);
v___x_765_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_757_, v_val_758_, v_x_737_, v_x_738_);
v___x_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
v___y_752_ = v___x_766_;
goto v___jp_751_;
}
else
{
lean_object* v___x_768_; 
lean_dec(v_val_758_);
lean_dec(v_key_757_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 1, v_x_738_);
lean_ctor_set(v___x_760_, 0, v_x_737_);
v___x_768_ = v___x_760_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_x_737_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_x_738_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
v___y_752_ = v___x_768_;
goto v___jp_751_;
}
}
}
}
case 1:
{
lean_object* v_node_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_783_; 
v_node_771_ = lean_ctor_get(v_v_748_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v_v_748_);
if (v_isSharedCheck_783_ == 0)
{
v___x_773_ = v_v_748_;
v_isShared_774_ = v_isSharedCheck_783_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_node_771_);
lean_dec(v_v_748_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_783_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
size_t v___x_775_; size_t v___x_776_; size_t v___x_777_; size_t v___x_778_; lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_775_ = ((size_t)5ULL);
v___x_776_ = lean_usize_shift_right(v_x_735_, v___x_775_);
v___x_777_ = ((size_t)1ULL);
v___x_778_ = lean_usize_add(v_x_736_, v___x_777_);
v___x_779_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_node_771_, v___x_776_, v___x_778_, v_x_737_, v_x_738_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_779_);
v___x_781_ = v___x_773_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
v___y_752_ = v___x_781_;
goto v___jp_751_;
}
}
}
default: 
{
lean_object* v___x_784_; 
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v_x_737_);
lean_ctor_set(v___x_784_, 1, v_x_738_);
v___y_752_ = v___x_784_;
goto v___jp_751_;
}
}
v___jp_751_:
{
lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_753_ = lean_array_fset(v_xs_x27_750_, v_j_742_, v___y_752_);
lean_dec(v_j_742_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v___x_753_);
v___x_755_ = v___x_746_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
else
{
lean_object* v_ks_787_; lean_object* v_vs_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_806_; 
v_ks_787_ = lean_ctor_get(v_x_734_, 0);
v_vs_788_ = lean_ctor_get(v_x_734_, 1);
v_isSharedCheck_806_ = !lean_is_exclusive(v_x_734_);
if (v_isSharedCheck_806_ == 0)
{
v___x_790_ = v_x_734_;
v_isShared_791_ = v_isSharedCheck_806_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_vs_788_);
lean_inc(v_ks_787_);
lean_dec(v_x_734_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_806_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_ks_787_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_vs_788_);
v___x_793_ = v_reuseFailAlloc_805_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v_newNode_794_; size_t v___x_795_; uint8_t v___x_796_; 
v_newNode_794_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1___redArg(v___x_793_, v_x_737_, v_x_738_);
v___x_795_ = ((size_t)7ULL);
v___x_796_ = lean_usize_dec_le(v___x_795_, v_x_736_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_797_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_794_);
v___x_798_ = lean_unsigned_to_nat(4u);
v___x_799_ = lean_nat_dec_lt(v___x_797_, v___x_798_);
lean_dec(v___x_797_);
if (v___x_799_ == 0)
{
lean_object* v_ks_800_; lean_object* v_vs_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v_ks_800_ = lean_ctor_get(v_newNode_794_, 0);
lean_inc_ref(v_ks_800_);
v_vs_801_ = lean_ctor_get(v_newNode_794_, 1);
lean_inc_ref(v_vs_801_);
lean_dec_ref(v_newNode_794_);
v___x_802_ = lean_unsigned_to_nat(0u);
v___x_803_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___closed__0);
v___x_804_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg(v_x_736_, v_ks_800_, v_vs_801_, v___x_802_, v___x_803_);
lean_dec_ref(v_vs_801_);
lean_dec_ref(v_ks_800_);
return v___x_804_;
}
else
{
return v_newNode_794_;
}
}
else
{
return v_newNode_794_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_734_ = stack[0].m_obj;
size_t v_x_735_ = stack[1].m_num;
size_t v_x_736_ = stack[2].m_num;
lean_object* v_x_737_ = stack[3].m_obj;
lean_object* v_x_738_ = stack[4].m_obj;
lean_object* v_res_807_;
v_res_807_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_x_734_, v_x_735_, v_x_736_, v_x_737_, v_x_738_);
stack->m_obj
 = v_res_807_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg(size_t v_depth_808_, lean_object* v_keys_809_, lean_object* v_vals_810_, lean_object* v_i_811_, lean_object* v_entries_812_){
_start:
{
lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_813_ = lean_array_get_size(v_keys_809_);
v___x_814_ = lean_nat_dec_lt(v_i_811_, v___x_813_);
if (v___x_814_ == 0)
{
lean_dec(v_i_811_);
return v_entries_812_;
}
else
{
lean_object* v_k_815_; lean_object* v_v_816_; size_t v___x_817_; size_t v___x_818_; size_t v___x_819_; uint64_t v___x_820_; size_t v_h_821_; size_t v___x_822_; lean_object* v___x_823_; size_t v___x_824_; size_t v___x_825_; size_t v___x_826_; size_t v_h_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v_k_815_ = lean_array_fget_borrowed(v_keys_809_, v_i_811_);
v_v_816_ = lean_array_fget_borrowed(v_vals_810_, v_i_811_);
v___x_817_ = lean_ptr_addr(v_k_815_);
v___x_818_ = ((size_t)3ULL);
v___x_819_ = lean_usize_shift_right(v___x_817_, v___x_818_);
v___x_820_ = lean_usize_to_uint64(v___x_819_);
v_h_821_ = lean_uint64_to_usize(v___x_820_);
v___x_822_ = ((size_t)5ULL);
v___x_823_ = lean_unsigned_to_nat(1u);
v___x_824_ = ((size_t)1ULL);
v___x_825_ = lean_usize_sub(v_depth_808_, v___x_824_);
v___x_826_ = lean_usize_mul(v___x_822_, v___x_825_);
v_h_827_ = lean_usize_shift_right(v_h_821_, v___x_826_);
v___x_828_ = lean_nat_add(v_i_811_, v___x_823_);
lean_dec(v_i_811_);
lean_inc(v_v_816_);
lean_inc(v_k_815_);
v___x_829_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_entries_812_, v_h_827_, v_depth_808_, v_k_815_, v_v_816_);
v_i_811_ = v___x_828_;
v_entries_812_ = v___x_829_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_808_ = stack[0].m_num;
lean_object* v_keys_809_ = stack[1].m_obj;
lean_object* v_vals_810_ = stack[2].m_obj;
lean_object* v_i_811_ = stack[3].m_obj;
lean_object* v_entries_812_ = stack[4].m_obj;
lean_object* v_res_831_;
v_res_831_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg(v_depth_808_, v_keys_809_, v_vals_810_, v_i_811_, v_entries_812_);
stack->m_obj
 = v_res_831_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_832_, lean_object* v_keys_833_, lean_object* v_vals_834_, lean_object* v_i_835_, lean_object* v_entries_836_){
_start:
{
size_t v_depth_boxed_837_; lean_object* v_res_838_; 
v_depth_boxed_837_ = lean_unbox_usize(v_depth_832_);
lean_dec(v_depth_832_);
v_res_838_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_837_, v_keys_833_, v_vals_834_, v_i_835_, v_entries_836_);
lean_dec_ref(v_vals_834_);
lean_dec_ref(v_keys_833_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___boxed(lean_object* v_x_839_, lean_object* v_x_840_, lean_object* v_x_841_, lean_object* v_x_842_, lean_object* v_x_843_){
_start:
{
size_t v_x_7535__boxed_844_; size_t v_x_7536__boxed_845_; lean_object* v_res_846_; 
v_x_7535__boxed_844_ = lean_unbox_usize(v_x_840_);
lean_dec(v_x_840_);
v_x_7536__boxed_845_ = lean_unbox_usize(v_x_841_);
lean_dec(v_x_841_);
v_res_846_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_x_839_, v_x_7535__boxed_844_, v_x_7536__boxed_845_, v_x_842_, v_x_843_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0___redArg(lean_object* v_x_847_, lean_object* v_x_848_, lean_object* v_x_849_){
_start:
{
size_t v___x_850_; size_t v___x_851_; size_t v___x_852_; uint64_t v___x_853_; size_t v___x_854_; size_t v___x_855_; lean_object* v___x_856_; 
v___x_850_ = lean_ptr_addr(v_x_848_);
v___x_851_ = ((size_t)3ULL);
v___x_852_ = lean_usize_shift_right(v___x_850_, v___x_851_);
v___x_853_ = lean_usize_to_uint64(v___x_852_);
v___x_854_ = lean_uint64_to_usize(v___x_853_);
v___x_855_ = ((size_t)1ULL);
v___x_856_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_x_847_, v___x_854_, v___x_855_, v_x_848_, v_x_849_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___lam__0(lean_object* v_e_857_, lean_object* v_a_858_, lean_object* v_s_859_){
_start:
{
lean_object* v_rings_860_; lean_object* v_exprToRingId_861_; lean_object* v_semirings_862_; lean_object* v_exprToSemiringId_863_; lean_object* v_ncRings_864_; lean_object* v_exprToNCRingId_865_; lean_object* v_ncSemirings_866_; lean_object* v_exprToNCSemiringId_867_; lean_object* v_steps_868_; uint8_t v_reportedMaxDegreeIssue_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_877_; 
v_rings_860_ = lean_ctor_get(v_s_859_, 0);
v_exprToRingId_861_ = lean_ctor_get(v_s_859_, 1);
v_semirings_862_ = lean_ctor_get(v_s_859_, 2);
v_exprToSemiringId_863_ = lean_ctor_get(v_s_859_, 3);
v_ncRings_864_ = lean_ctor_get(v_s_859_, 4);
v_exprToNCRingId_865_ = lean_ctor_get(v_s_859_, 5);
v_ncSemirings_866_ = lean_ctor_get(v_s_859_, 6);
v_exprToNCSemiringId_867_ = lean_ctor_get(v_s_859_, 7);
v_steps_868_ = lean_ctor_get(v_s_859_, 8);
v_reportedMaxDegreeIssue_869_ = lean_ctor_get_uint8(v_s_859_, sizeof(void*)*9);
v_isSharedCheck_877_ = !lean_is_exclusive(v_s_859_);
if (v_isSharedCheck_877_ == 0)
{
v___x_871_ = v_s_859_;
v_isShared_872_ = v_isSharedCheck_877_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_steps_868_);
lean_inc(v_exprToNCSemiringId_867_);
lean_inc(v_ncSemirings_866_);
lean_inc(v_exprToNCRingId_865_);
lean_inc(v_ncRings_864_);
lean_inc(v_exprToSemiringId_863_);
lean_inc(v_semirings_862_);
lean_inc(v_exprToRingId_861_);
lean_inc(v_rings_860_);
lean_dec(v_s_859_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_877_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; lean_object* v___x_875_; 
lean_inc(v_a_858_);
v___x_873_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0___redArg(v_exprToNCRingId_865_, v_e_857_, v_a_858_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 5, v___x_873_);
v___x_875_ = v___x_871_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_rings_860_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_exprToRingId_861_);
lean_ctor_set(v_reuseFailAlloc_876_, 2, v_semirings_862_);
lean_ctor_set(v_reuseFailAlloc_876_, 3, v_exprToSemiringId_863_);
lean_ctor_set(v_reuseFailAlloc_876_, 4, v_ncRings_864_);
lean_ctor_set(v_reuseFailAlloc_876_, 5, v___x_873_);
lean_ctor_set(v_reuseFailAlloc_876_, 6, v_ncSemirings_866_);
lean_ctor_set(v_reuseFailAlloc_876_, 7, v_exprToNCSemiringId_867_);
lean_ctor_set(v_reuseFailAlloc_876_, 8, v_steps_868_);
lean_ctor_set_uint8(v_reuseFailAlloc_876_, sizeof(void*)*9, v_reportedMaxDegreeIssue_869_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___lam__0___boxed(lean_object* v_e_878_, lean_object* v_a_879_, lean_object* v_s_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___lam__0(v_e_878_, v_a_879_, v_s_880_);
lean_dec(v_a_879_);
return v_res_881_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__1(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__0));
v___x_884_ = l_Lean_stringToMessageData(v___x_883_);
return v___x_884_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(lean_object* v_e_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
lean_object* v___f_898_; lean_object* v___x_899_; 
lean_inc(v_a_886_);
lean_inc_ref(v_e_885_);
v___f_898_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_898_, 0, v_e_885_);
lean_closure_set(v___f_898_, 1, v_a_886_);
v___x_899_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg(v_e_885_, v_a_887_, v_a_892_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref_known(v___x_899_, 1);
if (lean_obj_tag(v_a_900_) == 1)
{
lean_object* v_val_901_; uint8_t v___x_902_; 
lean_dec_ref(v___f_898_);
v_val_901_ = lean_ctor_get(v_a_900_, 0);
lean_inc(v_val_901_);
lean_dec_ref_known(v_a_900_, 1);
v___x_902_ = lean_nat_dec_eq(v_val_901_, v_a_886_);
lean_dec(v_val_901_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_903_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__1);
v___x_904_ = l_Lean_indentExpr(v_e_885_);
v___x_905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_903_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_888_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; uint8_t v_verbose_908_; 
v_a_907_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_a_907_);
lean_dec_ref_known(v___x_906_, 1);
v_verbose_908_ = lean_ctor_get_uint8(v_a_907_, 0);
lean_dec(v_a_907_);
if (v_verbose_908_ == 0)
{
lean_dec_ref_known(v___x_905_, 2);
goto v___jp_895_;
}
else
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_Meta_Sym_reportIssue(v___x_905_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_dec_ref_known(v___x_909_, 1);
goto v___jp_895_;
}
else
{
return v___x_909_;
}
}
}
else
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
lean_dec_ref_known(v___x_905_, 2);
v_a_910_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_906_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_906_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
else
{
lean_dec_ref(v_e_885_);
goto v___jp_895_;
}
}
else
{
lean_object* v___x_918_; lean_object* v___x_919_; 
lean_dec(v_a_900_);
lean_dec_ref(v_e_885_);
v___x_918_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_919_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_918_, v___f_898_, v_a_887_);
return v___x_919_;
}
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
lean_dec_ref(v___f_898_);
lean_dec_ref(v_e_885_);
v_a_920_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_899_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_899_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
v___jp_895_:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = lean_box(0);
v___x_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
return v___x_897_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_885_ = stack[0].m_obj;
lean_object* v_a_886_ = stack[1].m_obj;
lean_object* v_a_887_ = stack[2].m_obj;
lean_object* v_a_888_ = stack[3].m_obj;
lean_object* v_a_889_ = stack[4].m_obj;
lean_object* v_a_890_ = stack[5].m_obj;
lean_object* v_a_891_ = stack[6].m_obj;
lean_object* v_a_892_ = stack[7].m_obj;
lean_object* v_a_893_ = stack[8].m_obj;
lean_object* v_res_928_;
v_res_928_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(v_e_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_);
stack->m_obj
 = v_res_928_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___boxed(lean_object* v_e_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(v_e_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_);
lean_dec(v_a_937_);
lean_dec_ref(v_a_936_);
lean_dec(v_a_935_);
lean_dec_ref(v_a_934_);
lean_dec(v_a_933_);
lean_dec_ref(v_a_932_);
lean_dec(v_a_931_);
lean_dec(v_a_930_);
return v_res_939_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId(lean_object* v_e_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(v_e_940_, v_a_941_, v_a_942_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_);
return v___x_953_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_940_ = stack[0].m_obj;
lean_object* v_a_941_ = stack[1].m_obj;
lean_object* v_a_942_ = stack[2].m_obj;
lean_object* v_a_943_ = stack[3].m_obj;
lean_object* v_a_944_ = stack[4].m_obj;
lean_object* v_a_945_ = stack[5].m_obj;
lean_object* v_a_946_ = stack[6].m_obj;
lean_object* v_a_947_ = stack[7].m_obj;
lean_object* v_a_948_ = stack[8].m_obj;
lean_object* v_a_949_ = stack[9].m_obj;
lean_object* v_a_950_ = stack[10].m_obj;
lean_object* v_a_951_ = stack[11].m_obj;
lean_object* v_res_954_;
v_res_954_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId(v_e_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_);
stack->m_obj
 = v_res_954_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___boxed(lean_object* v_e_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId(v_e_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_);
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
lean_dec(v_a_956_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0(lean_object* v_00_u03b2_969_, lean_object* v_x_970_, lean_object* v_x_971_, lean_object* v_x_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0___redArg(v_x_970_, v_x_971_, v_x_972_);
return v___x_973_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0(lean_object* v_00_u03b2_974_, lean_object* v_x_975_, size_t v_x_976_, size_t v_x_977_, lean_object* v_x_978_, lean_object* v_x_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_x_975_, v_x_976_, v_x_977_, v_x_978_, v_x_979_);
return v___x_980_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_975_ = stack[1].m_obj;
size_t v_x_976_ = stack[2].m_num;
size_t v_x_977_ = stack[3].m_num;
lean_object* v_x_978_ = stack[4].m_obj;
lean_object* v_x_979_ = stack[5].m_obj;
lean_object* v_res_981_;
v_res_981_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0(lean_box(0), v_x_975_, v_x_976_, v_x_977_, v_x_978_, v_x_979_);
stack->m_obj
 = v_res_981_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_982_, lean_object* v_x_983_, lean_object* v_x_984_, lean_object* v_x_985_, lean_object* v_x_986_, lean_object* v_x_987_){
_start:
{
size_t v_x_7972__boxed_988_; size_t v_x_7973__boxed_989_; lean_object* v_res_990_; 
v_x_7972__boxed_988_ = lean_unbox_usize(v_x_984_);
lean_dec(v_x_984_);
v_x_7973__boxed_989_ = lean_unbox_usize(v_x_985_);
lean_dec(v_x_985_);
v_res_990_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0(v_00_u03b2_982_, v_x_983_, v_x_7972__boxed_988_, v_x_7973__boxed_989_, v_x_986_, v_x_987_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_991_, lean_object* v_n_992_, lean_object* v_k_993_, lean_object* v_v_994_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1___redArg(v_n_992_, v_k_993_, v_v_994_);
return v___x_995_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_996_, size_t v_depth_997_, lean_object* v_keys_998_, lean_object* v_vals_999_, lean_object* v_heq_1000_, lean_object* v_i_1001_, lean_object* v_entries_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg(v_depth_997_, v_keys_998_, v_vals_999_, v_i_1001_, v_entries_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_depth_997_ = stack[1].m_num;
lean_object* v_keys_998_ = stack[2].m_obj;
lean_object* v_vals_999_ = stack[3].m_obj;
lean_object* v_i_1001_ = stack[5].m_obj;
lean_object* v_entries_1002_ = stack[6].m_obj;
lean_object* v_res_1004_;
v_res_1004_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2(lean_box(0), v_depth_997_, v_keys_998_, v_vals_999_, lean_box(0), v_i_1001_, v_entries_1002_);
stack->m_obj
 = v_res_1004_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1005_, lean_object* v_depth_1006_, lean_object* v_keys_1007_, lean_object* v_vals_1008_, lean_object* v_heq_1009_, lean_object* v_i_1010_, lean_object* v_entries_1011_){
_start:
{
size_t v_depth_boxed_1012_; lean_object* v_res_1013_; 
v_depth_boxed_1012_ = lean_unbox_usize(v_depth_1006_);
lean_dec(v_depth_1006_);
v_res_1013_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2(v_00_u03b2_1005_, v_depth_boxed_1012_, v_keys_1007_, v_vals_1008_, v_heq_1009_, v_i_1010_, v_entries_1011_);
lean_dec_ref(v_vals_1008_);
lean_dec_ref(v_keys_1007_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1014_, lean_object* v_x_1015_, lean_object* v_x_1016_, lean_object* v_x_1017_, lean_object* v_x_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1015_, v_x_1016_, v_x_1017_, v_x_1018_);
return v___x_1019_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___lam__0(lean_object* v_e_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(v_e_1020_, v___y_1021_, v___y_1022_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
return v___x_1033_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1020_ = stack[0].m_obj;
lean_object* v___y_1021_ = stack[1].m_obj;
lean_object* v___y_1022_ = stack[2].m_obj;
lean_object* v___y_1023_ = stack[3].m_obj;
lean_object* v___y_1024_ = stack[4].m_obj;
lean_object* v___y_1025_ = stack[5].m_obj;
lean_object* v___y_1026_ = stack[6].m_obj;
lean_object* v___y_1027_ = stack[7].m_obj;
lean_object* v___y_1028_ = stack[8].m_obj;
lean_object* v___y_1029_ = stack[9].m_obj;
lean_object* v___y_1030_ = stack[10].m_obj;
lean_object* v___y_1031_ = stack[11].m_obj;
lean_object* v_res_1034_;
v_res_1034_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___lam__0(v_e_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
stack->m_obj
 = v_res_1034_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___lam__0___boxed(lean_object* v_e_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___lam__0(v_e_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec(v___y_1036_);
return v_res_1048_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0___closed__0));
v___x_1053_ = l_Lean_stringToMessageData(v___x_1052_);
return v___x_1053_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0(lean_object* v___x_1054_, lean_object* v___x_1055_, lean_object* v___f_1056_, lean_object* v___x_1057_, lean_object* v___f_1058_, lean_object* v_e_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_1059_, v___y_1061_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; uint8_t v___x_1074_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1073_);
lean_dec_ref_known(v___x_1072_, 1);
v___x_1074_ = lean_unbox(v_a_1073_);
lean_dec(v_a_1073_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1449__overap_1078_; lean_object* v___x_1079_; 
v___x_1075_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0___closed__1);
lean_inc_ref(v_e_1059_);
v___x_1076_ = l_Lean_indentExpr(v_e_1059_);
v___x_1077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1075_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
lean_inc_ref(v___x_1054_);
v___x_1449__overap_1078_ = l_Lean_throwError___redArg(v___x_1054_, v___x_1055_, v___x_1077_);
lean_inc(v___y_1070_);
lean_inc_ref(v___y_1069_);
lean_inc(v___y_1068_);
lean_inc_ref(v___y_1067_);
lean_inc(v___y_1066_);
lean_inc_ref(v___y_1065_);
lean_inc(v___y_1064_);
lean_inc_ref(v___y_1063_);
lean_inc(v___y_1062_);
lean_inc(v___y_1061_);
lean_inc(v___y_1060_);
v___x_1079_ = lean_apply_12(v___x_1449__overap_1078_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, lean_box(0));
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v___x_1452__overap_1080_; lean_object* v___x_1081_; 
lean_dec_ref_known(v___x_1079_, 1);
v___x_1452__overap_1080_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v___f_1056_, v___x_1054_, v___x_1057_, v___f_1058_, v_e_1059_);
lean_inc(v___y_1070_);
lean_inc_ref(v___y_1069_);
lean_inc(v___y_1068_);
lean_inc_ref(v___y_1067_);
lean_inc(v___y_1066_);
lean_inc_ref(v___y_1065_);
lean_inc(v___y_1064_);
lean_inc_ref(v___y_1063_);
lean_inc(v___y_1062_);
lean_inc(v___y_1061_);
lean_inc(v___y_1060_);
v___x_1081_ = lean_apply_12(v___x_1452__overap_1080_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, lean_box(0));
return v___x_1081_;
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec_ref(v_e_1059_);
lean_dec_ref(v___f_1058_);
lean_dec_ref(v___x_1057_);
lean_dec(v___f_1056_);
lean_dec_ref(v___x_1054_);
v_a_1082_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1079_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1079_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
else
{
lean_object* v___x_1456__overap_1090_; lean_object* v___x_1091_; 
lean_dec_ref(v___x_1055_);
v___x_1456__overap_1090_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v___f_1056_, v___x_1054_, v___x_1057_, v___f_1058_, v_e_1059_);
lean_inc(v___y_1070_);
lean_inc_ref(v___y_1069_);
lean_inc(v___y_1068_);
lean_inc_ref(v___y_1067_);
lean_inc(v___y_1066_);
lean_inc_ref(v___y_1065_);
lean_inc(v___y_1064_);
lean_inc_ref(v___y_1063_);
lean_inc(v___y_1062_);
lean_inc(v___y_1061_);
lean_inc(v___y_1060_);
v___x_1091_ = lean_apply_12(v___x_1456__overap_1090_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, lean_box(0));
return v___x_1091_;
}
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
lean_dec_ref(v_e_1059_);
lean_dec_ref(v___f_1058_);
lean_dec_ref(v___x_1057_);
lean_dec(v___f_1056_);
lean_dec_ref(v___x_1055_);
lean_dec_ref(v___x_1054_);
v_a_1092_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1072_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1072_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1054_ = stack[0].m_obj;
lean_object* v___x_1055_ = stack[1].m_obj;
lean_object* v___f_1056_ = stack[2].m_obj;
lean_object* v___x_1057_ = stack[3].m_obj;
lean_object* v___f_1058_ = stack[4].m_obj;
lean_object* v_e_1059_ = stack[5].m_obj;
lean_object* v___y_1060_ = stack[6].m_obj;
lean_object* v___y_1061_ = stack[7].m_obj;
lean_object* v___y_1062_ = stack[8].m_obj;
lean_object* v___y_1063_ = stack[9].m_obj;
lean_object* v___y_1064_ = stack[10].m_obj;
lean_object* v___y_1065_ = stack[11].m_obj;
lean_object* v___y_1066_ = stack[12].m_obj;
lean_object* v___y_1067_ = stack[13].m_obj;
lean_object* v___y_1068_ = stack[14].m_obj;
lean_object* v___y_1069_ = stack[15].m_obj;
lean_object* v___y_1070_ = stack[16].m_obj;
lean_object* v_res_1100_;
v_res_1100_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0(v___x_1054_, v___x_1055_, v___f_1056_, v___x_1057_, v___f_1058_, v_e_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
stack->m_obj
 = v_res_1100_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0___boxed(lean_object** _args){
lean_object* v___x_1101_ = _args[0];
lean_object* v___x_1102_ = _args[1];
lean_object* v___f_1103_ = _args[2];
lean_object* v___x_1104_ = _args[3];
lean_object* v___f_1105_ = _args[4];
lean_object* v_e_1106_ = _args[5];
lean_object* v___y_1107_ = _args[6];
lean_object* v___y_1108_ = _args[7];
lean_object* v___y_1109_ = _args[8];
lean_object* v___y_1110_ = _args[9];
lean_object* v___y_1111_ = _args[10];
lean_object* v___y_1112_ = _args[11];
lean_object* v___y_1113_ = _args[12];
lean_object* v___y_1114_ = _args[13];
lean_object* v___y_1115_ = _args[14];
lean_object* v___y_1116_ = _args[15];
lean_object* v___y_1117_ = _args[16];
lean_object* v___y_1118_ = _args[17];
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0(v___x_1101_, v___x_1102_, v___f_1103_, v___x_1104_, v___f_1105_, v_e_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec(v___y_1107_);
return v_res_1119_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__0(void){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = l_instMonadEIO___redArg();
return v___x_1120_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__1(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__0);
v___x_1122_ = l_StateRefT_x27_instMonad___redArg(v___x_1121_);
return v___x_1122_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__7(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___f_1129_; 
v___x_1128_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_1129_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1129_, 0, v___x_1128_);
return v___f_1129_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__8(void){
_start:
{
lean_object* v___x_1130_; lean_object* v___f_1131_; 
v___x_1130_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_1131_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1131_, 0, v___x_1130_);
return v___f_1131_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__9(void){
_start:
{
lean_object* v___f_1132_; lean_object* v___f_1133_; lean_object* v___x_1134_; 
v___f_1132_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__8, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__8_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__8);
v___f_1133_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__7, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__7_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__7);
v___x_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___f_1133_);
lean_ctor_set(v___x_1134_, 1, v___f_1132_);
return v___x_1134_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__10(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___f_1136_; 
v___x_1135_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__9, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__9_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__9);
v___f_1136_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1136_, 0, v___x_1135_);
return v___f_1136_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__11(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___f_1138_; 
v___x_1137_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__9, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__9_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__9);
v___f_1138_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1138_, 0, v___x_1137_);
return v___f_1138_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__12(void){
_start:
{
lean_object* v___f_1139_; lean_object* v___f_1140_; lean_object* v___x_1141_; 
v___f_1139_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__11, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__11_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__11);
v___f_1140_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__10, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__10_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__10);
v___x_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___f_1140_);
lean_ctor_set(v___x_1141_, 1, v___f_1139_);
return v___x_1141_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__13(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___f_1143_; 
v___x_1142_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__12);
v___f_1143_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1143_, 0, v___x_1142_);
return v___f_1143_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__14(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___f_1145_; 
v___x_1144_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__12);
v___f_1145_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1145_, 0, v___x_1144_);
return v___f_1145_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__15(void){
_start:
{
lean_object* v___f_1146_; lean_object* v___f_1147_; lean_object* v___x_1148_; 
v___f_1146_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__14, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__14_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__14);
v___f_1147_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__13, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__13_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__13);
v___x_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___f_1147_);
lean_ctor_set(v___x_1148_, 1, v___f_1146_);
return v___x_1148_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__16(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___f_1150_; 
v___x_1149_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__15, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__15_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__15);
v___f_1150_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1150_, 0, v___x_1149_);
return v___f_1150_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__17(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___f_1152_; 
v___x_1151_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__15, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__15_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__15);
v___f_1152_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1152_, 0, v___x_1151_);
return v___f_1152_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__18(void){
_start:
{
lean_object* v___f_1153_; lean_object* v___f_1154_; lean_object* v___x_1155_; 
v___f_1153_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__17, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__17_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__17);
v___f_1154_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__16, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__16_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__16);
v___x_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___f_1154_);
lean_ctor_set(v___x_1155_, 1, v___f_1153_);
return v___x_1155_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__19(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___f_1157_; 
v___x_1156_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__18, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__18_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__18);
v___f_1157_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1157_, 0, v___x_1156_);
return v___f_1157_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__20(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___f_1159_; 
v___x_1158_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__18, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__18_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__18);
v___f_1159_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1159_, 0, v___x_1158_);
return v___f_1159_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__21(void){
_start:
{
lean_object* v___f_1160_; lean_object* v___f_1161_; lean_object* v___x_1162_; 
v___f_1160_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__20, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__20_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__20);
v___f_1161_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__19, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__19_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__19);
v___x_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___f_1161_);
lean_ctor_set(v___x_1162_, 1, v___f_1160_);
return v___x_1162_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__22(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___f_1164_; 
v___x_1163_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__21, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__21_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__21);
v___f_1164_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1164_, 0, v___x_1163_);
return v___f_1164_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__23(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___f_1166_; 
v___x_1165_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__21, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__21_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__21);
v___f_1166_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1166_, 0, v___x_1165_);
return v___f_1166_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__24(void){
_start:
{
lean_object* v___f_1167_; lean_object* v___f_1168_; lean_object* v___x_1169_; 
v___f_1167_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__23, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__23_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__23);
v___f_1168_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__22, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__22_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__22);
v___x_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___f_1168_);
lean_ctor_set(v___x_1169_, 1, v___f_1167_);
return v___x_1169_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__25(void){
_start:
{
lean_object* v___x_1170_; lean_object* v___f_1171_; 
v___x_1170_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__24, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__24_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__24);
v___f_1171_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1171_, 0, v___x_1170_);
return v___f_1171_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__26(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___f_1173_; 
v___x_1172_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__24, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__24_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__24);
v___f_1173_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1173_, 0, v___x_1172_);
return v___f_1173_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__27(void){
_start:
{
lean_object* v___f_1174_; lean_object* v___f_1175_; lean_object* v___x_1176_; 
v___f_1174_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__26, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__26_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__26);
v___f_1175_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__25, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__25_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__25);
v___x_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___f_1175_);
lean_ctor_set(v___x_1176_, 1, v___f_1174_);
return v___x_1176_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__28(void){
_start:
{
lean_object* v___x_1177_; lean_object* v___f_1178_; 
v___x_1177_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__27, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__27_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__27);
v___f_1178_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1178_, 0, v___x_1177_);
return v___f_1178_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__29(void){
_start:
{
lean_object* v___x_1179_; lean_object* v___f_1180_; 
v___x_1179_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__27, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__27_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__27);
v___f_1180_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1180_, 0, v___x_1179_);
return v___f_1180_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__30(void){
_start:
{
lean_object* v___f_1181_; lean_object* v___f_1182_; lean_object* v___x_1183_; 
v___f_1181_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__29, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__29_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__29);
v___f_1182_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__28, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__28_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__28);
v___x_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___f_1182_);
lean_ctor_set(v___x_1183_, 1, v___f_1181_);
return v___x_1183_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__31(void){
_start:
{
lean_object* v___x_1184_; lean_object* v___f_1185_; 
v___x_1184_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__30, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__30_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__30);
v___f_1185_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1185_, 0, v___x_1184_);
return v___f_1185_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__32(void){
_start:
{
lean_object* v___x_1186_; lean_object* v___f_1187_; 
v___x_1186_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__30, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__30_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__30);
v___f_1187_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1187_, 0, v___x_1186_);
return v___f_1187_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__33(void){
_start:
{
lean_object* v___f_1188_; lean_object* v___f_1189_; lean_object* v___x_1190_; 
v___f_1188_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__32, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__32_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__32);
v___f_1189_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__31, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__31_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__31);
v___x_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___f_1189_);
lean_ctor_set(v___x_1190_, 1, v___f_1188_);
return v___x_1190_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__37(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1194_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1195_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__36));
v___x_1196_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__35));
v___x_1197_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1196_, v___x_1195_, v___x_1194_);
return v___x_1197_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__38(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___f_1199_; lean_object* v___f_1200_; lean_object* v___x_1201_; 
v___x_1198_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__37, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__37_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__37);
v___f_1199_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__6));
v___f_1200_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__34));
v___x_1201_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1200_, v___f_1199_, v___x_1198_);
return v___x_1201_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__39(void){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1202_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__38, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__38_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__38);
v___x_1203_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__36));
v___x_1204_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__35));
v___x_1205_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1204_, v___x_1203_, v___x_1202_);
return v___x_1205_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__40(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___f_1207_; lean_object* v___f_1208_; lean_object* v___x_1209_; 
v___x_1206_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__39, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__39_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__39);
v___f_1207_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__6));
v___f_1208_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__34));
v___x_1209_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1208_, v___f_1207_, v___x_1206_);
return v___x_1209_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__41(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1210_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__40, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__40_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__40);
v___x_1211_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__36));
v___x_1212_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__35));
v___x_1213_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1212_, v___x_1211_, v___x_1210_);
return v___x_1213_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__42(void){
_start:
{
lean_object* v___x_1214_; lean_object* v___f_1215_; lean_object* v___f_1216_; lean_object* v___x_1217_; 
v___x_1214_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__41, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__41_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__41);
v___f_1215_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__6));
v___f_1216_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__34));
v___x_1217_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1216_, v___f_1215_, v___x_1214_);
return v___x_1217_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__43(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___f_1219_; lean_object* v___f_1220_; lean_object* v___x_1221_; 
v___x_1218_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__42, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__42_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__42);
v___f_1219_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__6));
v___f_1220_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__34));
v___x_1221_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1220_, v___f_1219_, v___x_1218_);
return v___x_1221_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__44(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1222_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__43, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__43_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__43);
v___x_1223_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__36));
v___x_1224_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__35));
v___x_1225_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1224_, v___x_1223_, v___x_1222_);
return v___x_1225_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__45(void){
_start:
{
lean_object* v___x_1226_; lean_object* v___f_1227_; lean_object* v___f_1228_; lean_object* v___x_1229_; 
v___x_1226_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__44, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__44_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__44);
v___f_1227_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__6));
v___f_1228_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__34));
v___x_1229_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1228_, v___f_1227_, v___x_1226_);
return v___x_1229_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__48(void){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___f_1236_; 
v___x_1234_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__36));
v___x_1235_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_1236_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1236_, 0, v___x_1235_);
lean_closure_set(v___f_1236_, 1, v___x_1234_);
return v___f_1236_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__49(void){
_start:
{
lean_object* v___f_1237_; lean_object* v___f_1238_; lean_object* v___f_1239_; 
v___f_1237_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__6));
v___f_1238_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__48, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__48_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__48);
v___f_1239_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1239_, 0, v___f_1238_);
lean_closure_set(v___f_1239_, 1, v___f_1237_);
return v___f_1239_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__50(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___f_1241_; lean_object* v___f_1242_; 
v___x_1240_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__36));
v___f_1241_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__49, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__49_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__49);
v___f_1242_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1242_, 0, v___f_1241_);
lean_closure_set(v___f_1242_, 1, v___x_1240_);
return v___f_1242_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__51(void){
_start:
{
lean_object* v___f_1243_; lean_object* v___f_1244_; lean_object* v___f_1245_; 
v___f_1243_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__6));
v___f_1244_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__50, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__50_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__50);
v___f_1245_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1245_, 0, v___f_1244_);
lean_closure_set(v___f_1245_, 1, v___f_1243_);
return v___f_1245_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__52(void){
_start:
{
lean_object* v___f_1246_; lean_object* v___f_1247_; lean_object* v___f_1248_; 
v___f_1246_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__6));
v___f_1247_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__51, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__51_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__51);
v___f_1248_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1248_, 0, v___f_1247_);
lean_closure_set(v___f_1248_, 1, v___f_1246_);
return v___f_1248_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__53(void){
_start:
{
lean_object* v___x_1249_; lean_object* v___f_1250_; lean_object* v___f_1251_; 
v___x_1249_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__36));
v___f_1250_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__52, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__52_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__52);
v___f_1251_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1251_, 0, v___f_1250_);
lean_closure_set(v___f_1251_, 1, v___x_1249_);
return v___f_1251_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__54(void){
_start:
{
lean_object* v___f_1252_; lean_object* v___f_1253_; lean_object* v___f_1254_; 
v___f_1252_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__6));
v___f_1253_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__53, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__53_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__53);
v___f_1254_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1254_, 0, v___f_1253_);
lean_closure_set(v___f_1254_, 1, v___f_1252_);
return v___f_1254_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM(void){
_start:
{
lean_object* v___x_1255_; lean_object* v_toApplicative_1256_; lean_object* v_toFunctor_1257_; lean_object* v_toSeq_1258_; lean_object* v_toSeqLeft_1259_; lean_object* v_toSeqRight_1260_; lean_object* v___f_1261_; lean_object* v___f_1262_; lean_object* v___f_1263_; lean_object* v___f_1264_; lean_object* v___x_1265_; lean_object* v___f_1266_; lean_object* v___f_1267_; lean_object* v___f_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v_toApplicative_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1316_; 
v___x_1255_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__1);
v_toApplicative_1256_ = lean_ctor_get(v___x_1255_, 0);
v_toFunctor_1257_ = lean_ctor_get(v_toApplicative_1256_, 0);
v_toSeq_1258_ = lean_ctor_get(v_toApplicative_1256_, 2);
v_toSeqLeft_1259_ = lean_ctor_get(v_toApplicative_1256_, 3);
v_toSeqRight_1260_ = lean_ctor_get(v_toApplicative_1256_, 4);
v___f_1261_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__2));
v___f_1262_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__3));
lean_inc_ref_n(v_toFunctor_1257_, 2);
v___f_1263_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1263_, 0, v_toFunctor_1257_);
v___f_1264_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1264_, 0, v_toFunctor_1257_);
v___x_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___f_1263_);
lean_ctor_set(v___x_1265_, 1, v___f_1264_);
lean_inc(v_toSeqRight_1260_);
v___f_1266_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1266_, 0, v_toSeqRight_1260_);
lean_inc(v_toSeqLeft_1259_);
v___f_1267_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1267_, 0, v_toSeqLeft_1259_);
lean_inc(v_toSeq_1258_);
v___f_1268_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1268_, 0, v_toSeq_1258_);
v___x_1269_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1265_);
lean_ctor_set(v___x_1269_, 1, v___f_1261_);
lean_ctor_set(v___x_1269_, 2, v___f_1268_);
lean_ctor_set(v___x_1269_, 3, v___f_1267_);
lean_ctor_set(v___x_1269_, 4, v___f_1266_);
v___x_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
lean_ctor_set(v___x_1270_, 1, v___f_1262_);
v___x_1271_ = l_StateRefT_x27_instMonad___redArg(v___x_1270_);
v_toApplicative_1272_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1316_ == 0)
{
lean_object* v_unused_1317_; 
v_unused_1317_ = lean_ctor_get(v___x_1271_, 1);
lean_dec(v_unused_1317_);
v___x_1274_ = v___x_1271_;
v_isShared_1275_ = v_isSharedCheck_1316_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_toApplicative_1272_);
lean_dec(v___x_1271_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1316_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v_toFunctor_1276_; lean_object* v_toSeq_1277_; lean_object* v_toSeqLeft_1278_; lean_object* v_toSeqRight_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1314_; 
v_toFunctor_1276_ = lean_ctor_get(v_toApplicative_1272_, 0);
v_toSeq_1277_ = lean_ctor_get(v_toApplicative_1272_, 2);
v_toSeqLeft_1278_ = lean_ctor_get(v_toApplicative_1272_, 3);
v_toSeqRight_1279_ = lean_ctor_get(v_toApplicative_1272_, 4);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_toApplicative_1272_);
if (v_isSharedCheck_1314_ == 0)
{
lean_object* v_unused_1315_; 
v_unused_1315_ = lean_ctor_get(v_toApplicative_1272_, 1);
lean_dec(v_unused_1315_);
v___x_1281_ = v_toApplicative_1272_;
v_isShared_1282_ = v_isSharedCheck_1314_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_toSeqRight_1279_);
lean_inc(v_toSeqLeft_1278_);
lean_inc(v_toSeq_1277_);
lean_inc(v_toFunctor_1276_);
lean_dec(v_toApplicative_1272_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1314_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___f_1283_; lean_object* v___f_1284_; lean_object* v___f_1285_; lean_object* v___f_1286_; lean_object* v___x_1287_; lean_object* v___f_1288_; lean_object* v___f_1289_; lean_object* v___f_1290_; lean_object* v___x_1292_; 
v___f_1283_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__4));
v___f_1284_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__5));
lean_inc_ref(v_toFunctor_1276_);
v___f_1285_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1285_, 0, v_toFunctor_1276_);
v___f_1286_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1286_, 0, v_toFunctor_1276_);
v___x_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___f_1285_);
lean_ctor_set(v___x_1287_, 1, v___f_1286_);
v___f_1288_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1288_, 0, v_toSeqRight_1279_);
v___f_1289_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1289_, 0, v_toSeqLeft_1278_);
v___f_1290_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1290_, 0, v_toSeq_1277_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 4, v___f_1288_);
lean_ctor_set(v___x_1281_, 3, v___f_1289_);
lean_ctor_set(v___x_1281_, 2, v___f_1290_);
lean_ctor_set(v___x_1281_, 1, v___f_1283_);
lean_ctor_set(v___x_1281_, 0, v___x_1287_);
v___x_1292_ = v___x_1281_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1287_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v___f_1283_);
lean_ctor_set(v_reuseFailAlloc_1313_, 2, v___f_1290_);
lean_ctor_set(v_reuseFailAlloc_1313_, 3, v___f_1289_);
lean_ctor_set(v_reuseFailAlloc_1313_, 4, v___f_1288_);
v___x_1292_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_object* v___x_1294_; 
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 1, v___f_1284_);
lean_ctor_set(v___x_1274_, 0, v___x_1292_);
v___x_1294_ = v___x_1274_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1292_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v___f_1284_);
v___x_1294_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v_toMonadRef_1305_; lean_object* v___f_1306_; lean_object* v___f_1307_; lean_object* v___f_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___f_1311_; 
v___x_1295_ = l_StateRefT_x27_instMonad___redArg(v___x_1294_);
v___x_1296_ = l_ReaderT_instMonad___redArg(v___x_1295_);
v___x_1297_ = l_StateRefT_x27_instMonad___redArg(v___x_1296_);
v___x_1298_ = l_ReaderT_instMonad___redArg(v___x_1297_);
v___x_1299_ = l_ReaderT_instMonad___redArg(v___x_1298_);
v___x_1300_ = l_StateRefT_x27_instMonad___redArg(v___x_1299_);
v___x_1301_ = l_ReaderT_instMonad___redArg(v___x_1300_);
v___x_1302_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM;
v___x_1303_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__33, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__33_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__33);
v___x_1304_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__45, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__45_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__45);
v_toMonadRef_1305_ = lean_ctor_get(v___x_1304_, 0);
v___f_1306_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__47));
v___f_1307_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___closed__0));
v___f_1308_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__54, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__54_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__54);
lean_inc_ref(v___x_1301_);
v___x_1309_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1308_, v___x_1301_);
lean_inc_ref(v_toMonadRef_1305_);
v___x_1310_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1303_);
lean_ctor_set(v___x_1310_, 1, v_toMonadRef_1305_);
lean_ctor_set(v___x_1310_, 2, v___x_1309_);
v___f_1311_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0___boxed), 18, 5);
lean_closure_set(v___f_1311_, 0, v___x_1301_);
lean_closure_set(v___f_1311_, 1, v___x_1310_);
lean_closure_set(v___f_1311_, 2, v___f_1306_);
lean_closure_set(v___f_1311_, 3, v___x_1302_);
lean_closure_set(v___f_1311_, 4, v___f_1307_);
return v___f_1311_;
}
}
}
}
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM = _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM);
l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM = _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM);
l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM = _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM);
l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM = _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(builtin);
}
#ifdef __cplusplus
}
#endif
