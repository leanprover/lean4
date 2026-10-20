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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___redArg(lean_object* v_ringId_1_, lean_object* v_x_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___redArg___boxed(lean_object* v_ringId_15_, lean_object* v_x_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___redArg(v_ringId_15_, v_x_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run(lean_object* v_00_u03b1_29_, lean_object* v_ringId_30_, lean_object* v_x_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_){
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
v___x_43_ = lean_apply_12(v_x_31_, v_ringId_30_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, lean_box(0));
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___boxed(lean_object* v_00_u03b1_44_, lean_object* v_ringId_45_, lean_object* v_x_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run(v_00_u03b1_44_, v_ringId_45_, v_x_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__0(lean_object* v_e_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__0___boxed(lean_object* v_e_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__0(v_e_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__1(lean_object* v_e_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_e_89_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__1___boxed(lean_object* v_e_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__1(v_e_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0_spec__0(lean_object* v_msgData_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0_spec__0___boxed(lean_object* v_msgData_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0_spec__0(v_msgData_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg(lean_object* v_msg_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v_ref_154_; lean_object* v___x_155_; lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_164_; 
v_ref_154_ = lean_ctor_get(v___y_151_, 2);
v___x_155_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0_spec__0(v_msg_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg___boxed(lean_object* v_msg_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg(v_msg_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
return v_res_171_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__1(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__0));
v___x_174_ = l_Lean_stringToMessageData(v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_){
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
lean_object* v_ncRings_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v_ncRings_192_ = lean_ctor_get(v_a_188_, 3);
lean_inc_ref(v_ncRings_192_);
lean_dec(v_a_188_);
v___x_193_ = lean_array_get_size(v_ncRings_192_);
v___x_194_ = lean_nat_dec_lt(v_a_175_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; 
lean_dec_ref(v_ncRings_192_);
lean_del_object(v___x_190_);
v___x_195_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__1);
v___x_196_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg(v___x_195_, v_a_182_, v_a_183_, v_a_184_, v_a_185_);
return v___x_196_;
}
else
{
lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_197_ = lean_array_fget(v_ncRings_192_, v_a_175_);
lean_dec_ref(v_ncRings_192_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___boxed(lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0(lean_object* v_00_u03b1_223_, lean_object* v_msg_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg(v_msg_224_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___boxed(lean_object* v_00_u03b1_238_, lean_object* v_msg_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0(v_00_u03b1_238_, v_msg_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___lam__0(lean_object* v_a_253_, lean_object* v_f_254_, lean_object* v_s_255_){
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
v___x_264_ = lean_array_get_size(v_ncRings_259_);
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
v_v_269_ = lean_array_fget(v_ncRings_259_, v_a_253_);
v___x_270_ = lean_box(0);
v_xs_x27_271_ = lean_array_fset(v_ncRings_259_, v_a_253_, v___x_270_);
v___x_272_ = lean_apply_1(v_f_254_, v_v_269_);
v___x_273_ = lean_array_fset(v_xs_x27_271_, v_a_253_, v___x_272_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 3, v___x_273_);
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
lean_ctor_set(v_reuseFailAlloc_276_, 3, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_276_, 4, v_ncSemirings_260_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___lam__0___boxed(lean_object* v_a_286_, lean_object* v_f_287_, lean_object* v_s_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___lam__0(v_a_286_, v_f_287_, v_s_288_);
lean_dec(v_a_286_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(lean_object* v_f_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v___f_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
lean_inc(v_a_291_);
v___f_294_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_294_, 0, v_a_291_);
lean_closure_set(v___f_294_, 1, v_f_290_);
v___x_295_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_296_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_295_, v___f_294_, v_a_292_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___boxed(lean_object* v_f_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(v_f_297_, v_a_298_, v_a_299_);
lean_dec(v_a_299_);
lean_dec(v_a_298_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing(lean_object* v_f_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(v_f_302_, v_a_303_, v_a_309_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___boxed(lean_object* v_f_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing(v_f_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
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
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__0));
v___x_332_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___boxed), 12, 0);
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v___x_331_);
return v___x_333_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM(void){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___redArg(lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
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
v___x_344_ = l_Lean_Meta_Grind_Arith_CommRing_State_getNCRing(v_a_340_, v_a_335_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___redArg___boxed(lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___redArg(v_a_357_, v_a_358_, v_a_359_);
lean_dec_ref(v_a_359_);
lean_dec(v_a_358_);
lean_dec(v_a_357_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState(lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___redArg(v_a_362_, v_a_363_, v_a_371_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___boxed(lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState(v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg___lam__0(lean_object* v_a_388_, lean_object* v_f_389_, lean_object* v_s_390_){
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
v___x_406_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default;
v___x_407_ = l_Array_rightpad___redArg(v___x_405_, v___x_406_, v_ncRings_395_);
lean_dec(v___x_405_);
v___x_408_ = lean_array_get_size(v___x_407_);
v___x_409_ = lean_nat_dec_lt(v_a_388_, v___x_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_411_; 
lean_dec_ref(v_f_389_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 4, v___x_407_);
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
lean_ctor_set(v_reuseFailAlloc_412_, 4, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_412_, 5, v_exprToNCRingId_396_);
lean_ctor_set(v_reuseFailAlloc_412_, 6, v_ncSemirings_397_);
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
lean_ctor_set(v___x_402_, 4, v___x_417_);
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
lean_ctor_set(v_reuseFailAlloc_420_, 4, v___x_417_);
lean_ctor_set(v_reuseFailAlloc_420_, 5, v_exprToNCRingId_396_);
lean_ctor_set(v_reuseFailAlloc_420_, 6, v_ncSemirings_397_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg___lam__0___boxed(lean_object* v_a_422_, lean_object* v_f_423_, lean_object* v_s_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg___lam__0(v_a_422_, v_f_423_, v_s_424_);
lean_dec(v_a_422_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg(lean_object* v_f_426_, lean_object* v_a_427_, lean_object* v_a_428_){
_start:
{
lean_object* v___f_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
lean_inc(v_a_427_);
v___f_430_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_430_, 0, v_a_427_);
lean_closure_set(v___f_430_, 1, v_f_426_);
v___x_431_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_432_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_431_, v___f_430_, v_a_428_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg___boxed(lean_object* v_f_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg(v_f_433_, v_a_434_, v_a_435_);
lean_dec(v_a_435_);
lean_dec(v_a_434_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState(lean_object* v_f_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg(v_f_438_, v_a_439_, v_a_440_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___boxed(lean_object* v_f_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState(v_f_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_);
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
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM___closed__1(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_467_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM___closed__0));
v___x_468_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___boxed), 12, 0);
v___x_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
lean_ctor_set(v___x_469_, 1, v___x_467_);
return v___x_469_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM(void){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM___closed__1);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___lam__0(lean_object* v___x_471_, lean_object* v_x_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___redArg(v___y_473_, v___y_474_, v___y_482_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_501_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_501_ == 0)
{
v___x_488_ = v___x_485_;
v_isShared_489_ = v_isSharedCheck_501_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_485_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_501_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v_vars_490_; lean_object* v_size_491_; uint8_t v___x_492_; 
v_vars_490_ = lean_ctor_get(v_a_486_, 0);
lean_inc_ref(v_vars_490_);
lean_dec(v_a_486_);
v_size_491_ = lean_ctor_get(v_vars_490_, 2);
v___x_492_ = lean_nat_dec_lt(v_x_472_, v_size_491_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; lean_object* v___x_495_; 
lean_dec_ref(v_vars_490_);
v___x_493_ = l_outOfBounds___redArg(v___x_471_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 0, v___x_493_);
v___x_495_ = v___x_488_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
else
{
lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_497_ = l_Lean_PersistentArray_get_x21___redArg(v___x_471_, v_vars_490_, v_x_472_);
lean_dec_ref(v_vars_490_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 0, v___x_497_);
v___x_499_ = v___x_488_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_497_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
else
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
v_a_502_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_485_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_485_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___lam__0___boxed(lean_object* v___x_510_, lean_object* v_x_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___lam__0(v___x_510_, v_x_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec(v___y_513_);
lean_dec(v___y_512_);
lean_dec(v_x_511_);
lean_dec_ref(v___x_510_);
return v_res_524_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___closed__0(void){
_start:
{
lean_object* v___x_525_; lean_object* v___f_526_; 
v___x_525_ = l_Lean_instInhabitedExpr;
v___f_526_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___lam__0___boxed), 14, 1);
lean_closure_set(v___f_526_, 0, v___x_525_);
return v___f_526_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM(void){
_start:
{
lean_object* v___f_527_; 
v___f_527_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___closed__0);
return v___f_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_528_, lean_object* v_vals_529_, lean_object* v_i_530_, lean_object* v_k_531_){
_start:
{
lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_532_ = lean_array_get_size(v_keys_528_);
v___x_533_ = lean_nat_dec_lt(v_i_530_, v___x_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; 
lean_dec(v_i_530_);
v___x_534_ = lean_box(0);
return v___x_534_;
}
else
{
lean_object* v_k_x27_535_; size_t v___x_536_; size_t v___x_537_; uint8_t v___x_538_; 
v_k_x27_535_ = lean_array_fget_borrowed(v_keys_528_, v_i_530_);
v___x_536_ = lean_ptr_addr(v_k_531_);
v___x_537_ = lean_ptr_addr(v_k_x27_535_);
v___x_538_ = lean_usize_dec_eq(v___x_536_, v___x_537_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_unsigned_to_nat(1u);
v___x_540_ = lean_nat_add(v_i_530_, v___x_539_);
lean_dec(v_i_530_);
v_i_530_ = v___x_540_;
goto _start;
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_array_fget_borrowed(v_vals_529_, v_i_530_);
lean_dec(v_i_530_);
lean_inc(v___x_542_);
v___x_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
return v___x_543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_544_, lean_object* v_vals_545_, lean_object* v_i_546_, lean_object* v_k_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_544_, v_vals_545_, v_i_546_, v_k_547_);
lean_dec_ref(v_k_547_);
lean_dec_ref(v_vals_545_);
lean_dec_ref(v_keys_544_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg(lean_object* v_x_549_, size_t v_x_550_, lean_object* v_x_551_){
_start:
{
if (lean_obj_tag(v_x_549_) == 0)
{
lean_object* v_es_552_; lean_object* v___x_553_; size_t v___x_554_; size_t v___x_555_; lean_object* v_j_556_; lean_object* v___x_557_; 
v_es_552_ = lean_ctor_get(v_x_549_, 0);
v___x_553_ = lean_box(2);
v___x_554_ = ((size_t)31ULL);
v___x_555_ = lean_usize_land(v_x_550_, v___x_554_);
v_j_556_ = lean_usize_to_nat(v___x_555_);
v___x_557_ = lean_array_get_borrowed(v___x_553_, v_es_552_, v_j_556_);
lean_dec(v_j_556_);
switch(lean_obj_tag(v___x_557_))
{
case 0:
{
lean_object* v_key_558_; lean_object* v_val_559_; size_t v___x_560_; size_t v___x_561_; uint8_t v___x_562_; 
v_key_558_ = lean_ctor_get(v___x_557_, 0);
v_val_559_ = lean_ctor_get(v___x_557_, 1);
v___x_560_ = lean_ptr_addr(v_x_551_);
v___x_561_ = lean_ptr_addr(v_key_558_);
v___x_562_ = lean_usize_dec_eq(v___x_560_, v___x_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; 
v___x_563_ = lean_box(0);
return v___x_563_;
}
else
{
lean_object* v___x_564_; 
lean_inc(v_val_559_);
v___x_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_564_, 0, v_val_559_);
return v___x_564_;
}
}
case 1:
{
lean_object* v_node_565_; size_t v___x_566_; size_t v___x_567_; 
v_node_565_ = lean_ctor_get(v___x_557_, 0);
v___x_566_ = ((size_t)5ULL);
v___x_567_ = lean_usize_shift_right(v_x_550_, v___x_566_);
v_x_549_ = v_node_565_;
v_x_550_ = v___x_567_;
goto _start;
}
default: 
{
lean_object* v___x_569_; 
v___x_569_ = lean_box(0);
return v___x_569_;
}
}
}
else
{
lean_object* v_ks_570_; lean_object* v_vs_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v_ks_570_ = lean_ctor_get(v_x_549_, 0);
v_vs_571_ = lean_ctor_get(v_x_549_, 1);
v___x_572_ = lean_unsigned_to_nat(0u);
v___x_573_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_570_, v_vs_571_, v___x_572_, v_x_551_);
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_574_, lean_object* v_x_575_, lean_object* v_x_576_){
_start:
{
size_t v_x_905__boxed_577_; lean_object* v_res_578_; 
v_x_905__boxed_577_ = lean_unbox_usize(v_x_575_);
lean_dec(v_x_575_);
v_res_578_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg(v_x_574_, v_x_905__boxed_577_, v_x_576_);
lean_dec_ref(v_x_576_);
lean_dec_ref(v_x_574_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg(lean_object* v_x_579_, lean_object* v_x_580_){
_start:
{
size_t v___x_581_; size_t v___x_582_; size_t v___x_583_; uint64_t v___x_584_; size_t v___x_585_; lean_object* v___x_586_; 
v___x_581_ = lean_ptr_addr(v_x_580_);
v___x_582_ = ((size_t)3ULL);
v___x_583_ = lean_usize_shift_right(v___x_581_, v___x_582_);
v___x_584_ = lean_usize_to_uint64(v___x_583_);
v___x_585_ = lean_uint64_to_usize(v___x_584_);
v___x_586_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg(v_x_579_, v___x_585_, v_x_580_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg___boxed(lean_object* v_x_587_, lean_object* v_x_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg(v_x_587_, v_x_588_);
lean_dec_ref(v_x_588_);
lean_dec_ref(v_x_587_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg(lean_object* v_e_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_591_, v_a_592_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_604_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_604_ == 0)
{
v___x_597_ = v___x_594_;
v_isShared_598_ = v_isSharedCheck_604_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_604_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v_exprToNCRingId_599_; lean_object* v___x_600_; lean_object* v___x_602_; 
v_exprToNCRingId_599_ = lean_ctor_get(v_a_595_, 5);
lean_inc_ref(v_exprToNCRingId_599_);
lean_dec(v_a_595_);
v___x_600_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg(v_exprToNCRingId_599_, v_e_590_);
lean_dec_ref(v_exprToNCRingId_599_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_600_);
v___x_602_ = v___x_597_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
v_a_605_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___x_594_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_594_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg___boxed(lean_object* v_e_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg(v_e_613_, v_a_614_, v_a_615_);
lean_dec_ref(v_a_615_);
lean_dec(v_a_614_);
lean_dec_ref(v_e_613_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f(lean_object* v_e_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg(v_e_618_, v_a_619_, v_a_627_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___boxed(lean_object* v_e_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f(v_e_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
lean_dec(v_a_633_);
lean_dec(v_a_632_);
lean_dec_ref(v_e_631_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0(lean_object* v_00_u03b2_644_, lean_object* v_x_645_, lean_object* v_x_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg(v_x_645_, v_x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___boxed(lean_object* v_00_u03b2_648_, lean_object* v_x_649_, lean_object* v_x_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0(v_00_u03b2_648_, v_x_649_, v_x_650_);
lean_dec_ref(v_x_650_);
lean_dec_ref(v_x_649_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_652_, lean_object* v_x_653_, size_t v_x_654_, lean_object* v_x_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg(v_x_653_, v_x_654_, v_x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_657_, lean_object* v_x_658_, lean_object* v_x_659_, lean_object* v_x_660_){
_start:
{
size_t v_x_1026__boxed_661_; lean_object* v_res_662_; 
v_x_1026__boxed_661_ = lean_unbox_usize(v_x_659_);
lean_dec(v_x_659_);
v_res_662_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0(v_00_u03b2_657_, v_x_658_, v_x_1026__boxed_661_, v_x_660_);
lean_dec_ref(v_x_660_);
lean_dec_ref(v_x_658_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_663_, lean_object* v_keys_664_, lean_object* v_vals_665_, lean_object* v_heq_666_, lean_object* v_i_667_, lean_object* v_k_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_664_, v_vals_665_, v_i_667_, v_k_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_670_, lean_object* v_keys_671_, lean_object* v_vals_672_, lean_object* v_heq_673_, lean_object* v_i_674_, lean_object* v_k_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_670_, v_keys_671_, v_vals_672_, v_heq_673_, v_i_674_, v_k_675_);
lean_dec_ref(v_k_675_);
lean_dec_ref(v_vals_672_);
lean_dec_ref(v_keys_671_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_677_, lean_object* v_x_678_, lean_object* v_x_679_, lean_object* v_x_680_){
_start:
{
lean_object* v_ks_681_; lean_object* v_vs_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_708_; 
v_ks_681_ = lean_ctor_get(v_x_677_, 0);
v_vs_682_ = lean_ctor_get(v_x_677_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v_x_677_);
if (v_isSharedCheck_708_ == 0)
{
v___x_684_ = v_x_677_;
v_isShared_685_ = v_isSharedCheck_708_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_vs_682_);
lean_inc(v_ks_681_);
lean_dec(v_x_677_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_708_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_686_ = lean_array_get_size(v_ks_681_);
v___x_687_ = lean_nat_dec_lt(v_x_678_, v___x_686_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_691_; 
lean_dec(v_x_678_);
v___x_688_ = lean_array_push(v_ks_681_, v_x_679_);
v___x_689_ = lean_array_push(v_vs_682_, v_x_680_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v___x_689_);
lean_ctor_set(v___x_684_, 0, v___x_688_);
v___x_691_ = v___x_684_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_688_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
else
{
lean_object* v_k_x27_693_; size_t v___x_694_; size_t v___x_695_; uint8_t v___x_696_; 
v_k_x27_693_ = lean_array_fget_borrowed(v_ks_681_, v_x_678_);
v___x_694_ = lean_ptr_addr(v_x_679_);
v___x_695_ = lean_ptr_addr(v_k_x27_693_);
v___x_696_ = lean_usize_dec_eq(v___x_694_, v___x_695_);
if (v___x_696_ == 0)
{
lean_object* v___x_698_; 
if (v_isShared_685_ == 0)
{
v___x_698_ = v___x_684_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_ks_681_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_vs_682_);
v___x_698_ = v_reuseFailAlloc_702_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_unsigned_to_nat(1u);
v___x_700_ = lean_nat_add(v_x_678_, v___x_699_);
lean_dec(v_x_678_);
v_x_677_ = v___x_698_;
v_x_678_ = v___x_700_;
goto _start;
}
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_703_ = lean_array_fset(v_ks_681_, v_x_678_, v_x_679_);
v___x_704_ = lean_array_fset(v_vs_682_, v_x_678_, v_x_680_);
lean_dec(v_x_678_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v___x_704_);
lean_ctor_set(v___x_684_, 0, v___x_703_);
v___x_706_ = v___x_684_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v___x_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_709_, lean_object* v_k_710_, lean_object* v_v_711_){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = lean_unsigned_to_nat(0u);
v___x_713_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_709_, v___x_712_, v_k_710_, v_v_711_);
return v___x_713_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(lean_object* v_x_715_, size_t v_x_716_, size_t v_x_717_, lean_object* v_x_718_, lean_object* v_x_719_){
_start:
{
if (lean_obj_tag(v_x_715_) == 0)
{
lean_object* v_es_720_; size_t v___x_721_; size_t v___x_722_; lean_object* v_j_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v_es_720_ = lean_ctor_get(v_x_715_, 0);
v___x_721_ = ((size_t)31ULL);
v___x_722_ = lean_usize_land(v_x_716_, v___x_721_);
v_j_723_ = lean_usize_to_nat(v___x_722_);
v___x_724_ = lean_array_get_size(v_es_720_);
v___x_725_ = lean_nat_dec_lt(v_j_723_, v___x_724_);
if (v___x_725_ == 0)
{
lean_dec(v_j_723_);
lean_dec(v_x_719_);
lean_dec_ref(v_x_718_);
return v_x_715_;
}
else
{
lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_766_; 
lean_inc_ref(v_es_720_);
v_isSharedCheck_766_ = !lean_is_exclusive(v_x_715_);
if (v_isSharedCheck_766_ == 0)
{
lean_object* v_unused_767_; 
v_unused_767_ = lean_ctor_get(v_x_715_, 0);
lean_dec(v_unused_767_);
v___x_727_ = v_x_715_;
v_isShared_728_ = v_isSharedCheck_766_;
goto v_resetjp_726_;
}
else
{
lean_dec(v_x_715_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_766_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v_v_729_; lean_object* v___x_730_; lean_object* v_xs_x27_731_; lean_object* v___y_733_; 
v_v_729_ = lean_array_fget(v_es_720_, v_j_723_);
v___x_730_ = lean_box(0);
v_xs_x27_731_ = lean_array_fset(v_es_720_, v_j_723_, v___x_730_);
switch(lean_obj_tag(v_v_729_))
{
case 0:
{
lean_object* v_key_738_; lean_object* v_val_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_751_; 
v_key_738_ = lean_ctor_get(v_v_729_, 0);
v_val_739_ = lean_ctor_get(v_v_729_, 1);
v_isSharedCheck_751_ = !lean_is_exclusive(v_v_729_);
if (v_isSharedCheck_751_ == 0)
{
v___x_741_ = v_v_729_;
v_isShared_742_ = v_isSharedCheck_751_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_val_739_);
lean_inc(v_key_738_);
lean_dec(v_v_729_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_751_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
size_t v___x_743_; size_t v___x_744_; uint8_t v___x_745_; 
v___x_743_ = lean_ptr_addr(v_x_718_);
v___x_744_ = lean_ptr_addr(v_key_738_);
v___x_745_ = lean_usize_dec_eq(v___x_743_, v___x_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; 
lean_del_object(v___x_741_);
v___x_746_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_738_, v_val_739_, v_x_718_, v_x_719_);
v___x_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
v___y_733_ = v___x_747_;
goto v___jp_732_;
}
else
{
lean_object* v___x_749_; 
lean_dec(v_val_739_);
lean_dec(v_key_738_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 1, v_x_719_);
lean_ctor_set(v___x_741_, 0, v_x_718_);
v___x_749_ = v___x_741_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_x_718_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_x_719_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
v___y_733_ = v___x_749_;
goto v___jp_732_;
}
}
}
}
case 1:
{
lean_object* v_node_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_764_; 
v_node_752_ = lean_ctor_get(v_v_729_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v_v_729_);
if (v_isSharedCheck_764_ == 0)
{
v___x_754_ = v_v_729_;
v_isShared_755_ = v_isSharedCheck_764_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_node_752_);
lean_dec(v_v_729_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_764_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
size_t v___x_756_; size_t v___x_757_; size_t v___x_758_; size_t v___x_759_; lean_object* v___x_760_; lean_object* v___x_762_; 
v___x_756_ = ((size_t)5ULL);
v___x_757_ = lean_usize_shift_right(v_x_716_, v___x_756_);
v___x_758_ = ((size_t)1ULL);
v___x_759_ = lean_usize_add(v_x_717_, v___x_758_);
v___x_760_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_node_752_, v___x_757_, v___x_759_, v_x_718_, v_x_719_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v___x_760_);
v___x_762_ = v___x_754_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
v___y_733_ = v___x_762_;
goto v___jp_732_;
}
}
}
default: 
{
lean_object* v___x_765_; 
v___x_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_765_, 0, v_x_718_);
lean_ctor_set(v___x_765_, 1, v_x_719_);
v___y_733_ = v___x_765_;
goto v___jp_732_;
}
}
v___jp_732_:
{
lean_object* v___x_734_; lean_object* v___x_736_; 
v___x_734_ = lean_array_fset(v_xs_x27_731_, v_j_723_, v___y_733_);
lean_dec(v_j_723_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v___x_734_);
v___x_736_ = v___x_727_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_734_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
}
else
{
lean_object* v_ks_768_; lean_object* v_vs_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_787_; 
v_ks_768_ = lean_ctor_get(v_x_715_, 0);
v_vs_769_ = lean_ctor_get(v_x_715_, 1);
v_isSharedCheck_787_ = !lean_is_exclusive(v_x_715_);
if (v_isSharedCheck_787_ == 0)
{
v___x_771_ = v_x_715_;
v_isShared_772_ = v_isSharedCheck_787_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_vs_769_);
lean_inc(v_ks_768_);
lean_dec(v_x_715_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_787_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_ks_768_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_vs_769_);
v___x_774_ = v_reuseFailAlloc_786_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v_newNode_775_; size_t v___x_776_; uint8_t v___x_777_; 
v_newNode_775_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1___redArg(v___x_774_, v_x_718_, v_x_719_);
v___x_776_ = ((size_t)7ULL);
v___x_777_ = lean_usize_dec_le(v___x_776_, v_x_717_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_778_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_775_);
v___x_779_ = lean_unsigned_to_nat(4u);
v___x_780_ = lean_nat_dec_lt(v___x_778_, v___x_779_);
lean_dec(v___x_778_);
if (v___x_780_ == 0)
{
lean_object* v_ks_781_; lean_object* v_vs_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v_ks_781_ = lean_ctor_get(v_newNode_775_, 0);
lean_inc_ref(v_ks_781_);
v_vs_782_ = lean_ctor_get(v_newNode_775_, 1);
lean_inc_ref(v_vs_782_);
lean_dec_ref(v_newNode_775_);
v___x_783_ = lean_unsigned_to_nat(0u);
v___x_784_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___closed__0);
v___x_785_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg(v_x_717_, v_ks_781_, v_vs_782_, v___x_783_, v___x_784_);
lean_dec_ref(v_vs_782_);
lean_dec_ref(v_ks_781_);
return v___x_785_;
}
else
{
return v_newNode_775_;
}
}
else
{
return v_newNode_775_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg(size_t v_depth_788_, lean_object* v_keys_789_, lean_object* v_vals_790_, lean_object* v_i_791_, lean_object* v_entries_792_){
_start:
{
lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_793_ = lean_array_get_size(v_keys_789_);
v___x_794_ = lean_nat_dec_lt(v_i_791_, v___x_793_);
if (v___x_794_ == 0)
{
lean_dec(v_i_791_);
return v_entries_792_;
}
else
{
lean_object* v_k_795_; lean_object* v_v_796_; size_t v___x_797_; size_t v___x_798_; size_t v___x_799_; uint64_t v___x_800_; size_t v_h_801_; size_t v___x_802_; lean_object* v___x_803_; size_t v___x_804_; size_t v___x_805_; size_t v___x_806_; size_t v_h_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v_k_795_ = lean_array_fget_borrowed(v_keys_789_, v_i_791_);
v_v_796_ = lean_array_fget_borrowed(v_vals_790_, v_i_791_);
v___x_797_ = lean_ptr_addr(v_k_795_);
v___x_798_ = ((size_t)3ULL);
v___x_799_ = lean_usize_shift_right(v___x_797_, v___x_798_);
v___x_800_ = lean_usize_to_uint64(v___x_799_);
v_h_801_ = lean_uint64_to_usize(v___x_800_);
v___x_802_ = ((size_t)5ULL);
v___x_803_ = lean_unsigned_to_nat(1u);
v___x_804_ = ((size_t)1ULL);
v___x_805_ = lean_usize_sub(v_depth_788_, v___x_804_);
v___x_806_ = lean_usize_mul(v___x_802_, v___x_805_);
v_h_807_ = lean_usize_shift_right(v_h_801_, v___x_806_);
v___x_808_ = lean_nat_add(v_i_791_, v___x_803_);
lean_dec(v_i_791_);
lean_inc(v_v_796_);
lean_inc(v_k_795_);
v___x_809_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_entries_792_, v_h_807_, v_depth_788_, v_k_795_, v_v_796_);
v_i_791_ = v___x_808_;
v_entries_792_ = v___x_809_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_811_, lean_object* v_keys_812_, lean_object* v_vals_813_, lean_object* v_i_814_, lean_object* v_entries_815_){
_start:
{
size_t v_depth_boxed_816_; lean_object* v_res_817_; 
v_depth_boxed_816_ = lean_unbox_usize(v_depth_811_);
lean_dec(v_depth_811_);
v_res_817_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_816_, v_keys_812_, v_vals_813_, v_i_814_, v_entries_815_);
lean_dec_ref(v_vals_813_);
lean_dec_ref(v_keys_812_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___boxed(lean_object* v_x_818_, lean_object* v_x_819_, lean_object* v_x_820_, lean_object* v_x_821_, lean_object* v_x_822_){
_start:
{
size_t v_x_7502__boxed_823_; size_t v_x_7503__boxed_824_; lean_object* v_res_825_; 
v_x_7502__boxed_823_ = lean_unbox_usize(v_x_819_);
lean_dec(v_x_819_);
v_x_7503__boxed_824_ = lean_unbox_usize(v_x_820_);
lean_dec(v_x_820_);
v_res_825_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_x_818_, v_x_7502__boxed_823_, v_x_7503__boxed_824_, v_x_821_, v_x_822_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0___redArg(lean_object* v_x_826_, lean_object* v_x_827_, lean_object* v_x_828_){
_start:
{
size_t v___x_829_; size_t v___x_830_; size_t v___x_831_; uint64_t v___x_832_; size_t v___x_833_; size_t v___x_834_; lean_object* v___x_835_; 
v___x_829_ = lean_ptr_addr(v_x_827_);
v___x_830_ = ((size_t)3ULL);
v___x_831_ = lean_usize_shift_right(v___x_829_, v___x_830_);
v___x_832_ = lean_usize_to_uint64(v___x_831_);
v___x_833_ = lean_uint64_to_usize(v___x_832_);
v___x_834_ = ((size_t)1ULL);
v___x_835_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_x_826_, v___x_833_, v___x_834_, v_x_827_, v_x_828_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___lam__0(lean_object* v_e_836_, lean_object* v_a_837_, lean_object* v_s_838_){
_start:
{
lean_object* v_rings_839_; lean_object* v_exprToRingId_840_; lean_object* v_semirings_841_; lean_object* v_exprToSemiringId_842_; lean_object* v_ncRings_843_; lean_object* v_exprToNCRingId_844_; lean_object* v_ncSemirings_845_; lean_object* v_exprToNCSemiringId_846_; lean_object* v_steps_847_; uint8_t v_reportedMaxDegreeIssue_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_856_; 
v_rings_839_ = lean_ctor_get(v_s_838_, 0);
v_exprToRingId_840_ = lean_ctor_get(v_s_838_, 1);
v_semirings_841_ = lean_ctor_get(v_s_838_, 2);
v_exprToSemiringId_842_ = lean_ctor_get(v_s_838_, 3);
v_ncRings_843_ = lean_ctor_get(v_s_838_, 4);
v_exprToNCRingId_844_ = lean_ctor_get(v_s_838_, 5);
v_ncSemirings_845_ = lean_ctor_get(v_s_838_, 6);
v_exprToNCSemiringId_846_ = lean_ctor_get(v_s_838_, 7);
v_steps_847_ = lean_ctor_get(v_s_838_, 8);
v_reportedMaxDegreeIssue_848_ = lean_ctor_get_uint8(v_s_838_, sizeof(void*)*9);
v_isSharedCheck_856_ = !lean_is_exclusive(v_s_838_);
if (v_isSharedCheck_856_ == 0)
{
v___x_850_ = v_s_838_;
v_isShared_851_ = v_isSharedCheck_856_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_steps_847_);
lean_inc(v_exprToNCSemiringId_846_);
lean_inc(v_ncSemirings_845_);
lean_inc(v_exprToNCRingId_844_);
lean_inc(v_ncRings_843_);
lean_inc(v_exprToSemiringId_842_);
lean_inc(v_semirings_841_);
lean_inc(v_exprToRingId_840_);
lean_inc(v_rings_839_);
lean_dec(v_s_838_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_856_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_852_; lean_object* v___x_854_; 
lean_inc(v_a_837_);
v___x_852_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0___redArg(v_exprToNCRingId_844_, v_e_836_, v_a_837_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 5, v___x_852_);
v___x_854_ = v___x_850_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_rings_839_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_exprToRingId_840_);
lean_ctor_set(v_reuseFailAlloc_855_, 2, v_semirings_841_);
lean_ctor_set(v_reuseFailAlloc_855_, 3, v_exprToSemiringId_842_);
lean_ctor_set(v_reuseFailAlloc_855_, 4, v_ncRings_843_);
lean_ctor_set(v_reuseFailAlloc_855_, 5, v___x_852_);
lean_ctor_set(v_reuseFailAlloc_855_, 6, v_ncSemirings_845_);
lean_ctor_set(v_reuseFailAlloc_855_, 7, v_exprToNCSemiringId_846_);
lean_ctor_set(v_reuseFailAlloc_855_, 8, v_steps_847_);
lean_ctor_set_uint8(v_reuseFailAlloc_855_, sizeof(void*)*9, v_reportedMaxDegreeIssue_848_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___lam__0___boxed(lean_object* v_e_857_, lean_object* v_a_858_, lean_object* v_s_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___lam__0(v_e_857_, v_a_858_, v_s_859_);
lean_dec(v_a_858_);
return v_res_860_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__1(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__0));
v___x_863_ = l_Lean_stringToMessageData(v___x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(lean_object* v_e_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v___f_877_; lean_object* v___x_878_; 
lean_inc(v_a_865_);
lean_inc_ref(v_e_864_);
v___f_877_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_877_, 0, v_e_864_);
lean_closure_set(v___f_877_, 1, v_a_865_);
v___x_878_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg(v_e_864_, v_a_866_, v_a_871_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_a_879_);
lean_dec_ref_known(v___x_878_, 1);
if (lean_obj_tag(v_a_879_) == 1)
{
lean_object* v_val_880_; uint8_t v___x_881_; 
lean_dec_ref(v___f_877_);
v_val_880_ = lean_ctor_get(v_a_879_, 0);
lean_inc(v_val_880_);
lean_dec_ref_known(v_a_879_, 1);
v___x_881_ = lean_nat_dec_eq(v_val_880_, v_a_865_);
lean_dec(v_val_880_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_882_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__1);
v___x_883_ = l_Lean_indentExpr(v_e_864_);
v___x_884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_882_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
v___x_885_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_867_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; uint8_t v_verbose_887_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_885_, 1);
v_verbose_887_ = lean_ctor_get_uint8(v_a_886_, 0);
lean_dec(v_a_886_);
if (v_verbose_887_ == 0)
{
lean_dec_ref_known(v___x_884_, 2);
goto v___jp_874_;
}
else
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_Meta_Sym_reportIssue(v___x_884_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_dec_ref_known(v___x_888_, 1);
goto v___jp_874_;
}
else
{
return v___x_888_;
}
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_dec_ref_known(v___x_884_, 2);
v_a_889_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_885_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_885_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
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
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
else
{
lean_dec_ref(v_e_864_);
goto v___jp_874_;
}
}
else
{
lean_object* v___x_897_; lean_object* v___x_898_; 
lean_dec(v_a_879_);
lean_dec_ref(v_e_864_);
v___x_897_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_898_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_897_, v___f_877_, v_a_866_);
return v___x_898_;
}
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
lean_dec_ref(v___f_877_);
lean_dec_ref(v_e_864_);
v_a_899_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_878_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_878_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
v___jp_874_:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_box(0);
v___x_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
return v___x_876_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___boxed(lean_object* v_e_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(v_e_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec(v_a_908_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId(lean_object* v_e_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(v_e_918_, v_a_919_, v_a_920_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___boxed(lean_object* v_e_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId(v_e_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
lean_dec(v_a_937_);
lean_dec_ref(v_a_936_);
lean_dec(v_a_935_);
lean_dec(v_a_934_);
lean_dec(v_a_933_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0(lean_object* v_00_u03b2_946_, lean_object* v_x_947_, lean_object* v_x_948_, lean_object* v_x_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0___redArg(v_x_947_, v_x_948_, v_x_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0(lean_object* v_00_u03b2_951_, lean_object* v_x_952_, size_t v_x_953_, size_t v_x_954_, lean_object* v_x_955_, lean_object* v_x_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_x_952_, v_x_953_, v_x_954_, v_x_955_, v_x_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_958_, lean_object* v_x_959_, lean_object* v_x_960_, lean_object* v_x_961_, lean_object* v_x_962_, lean_object* v_x_963_){
_start:
{
size_t v_x_7788__boxed_964_; size_t v_x_7789__boxed_965_; lean_object* v_res_966_; 
v_x_7788__boxed_964_ = lean_unbox_usize(v_x_960_);
lean_dec(v_x_960_);
v_x_7789__boxed_965_ = lean_unbox_usize(v_x_961_);
lean_dec(v_x_961_);
v_res_966_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0(v_00_u03b2_958_, v_x_959_, v_x_7788__boxed_964_, v_x_7789__boxed_965_, v_x_962_, v_x_963_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_967_, lean_object* v_n_968_, lean_object* v_k_969_, lean_object* v_v_970_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1___redArg(v_n_968_, v_k_969_, v_v_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_972_, size_t v_depth_973_, lean_object* v_keys_974_, lean_object* v_vals_975_, lean_object* v_heq_976_, lean_object* v_i_977_, lean_object* v_entries_978_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg(v_depth_973_, v_keys_974_, v_vals_975_, v_i_977_, v_entries_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_980_, lean_object* v_depth_981_, lean_object* v_keys_982_, lean_object* v_vals_983_, lean_object* v_heq_984_, lean_object* v_i_985_, lean_object* v_entries_986_){
_start:
{
size_t v_depth_boxed_987_; lean_object* v_res_988_; 
v_depth_boxed_987_ = lean_unbox_usize(v_depth_981_);
lean_dec(v_depth_981_);
v_res_988_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2(v_00_u03b2_980_, v_depth_boxed_987_, v_keys_982_, v_vals_983_, v_heq_984_, v_i_985_, v_entries_986_);
lean_dec_ref(v_vals_983_);
lean_dec_ref(v_keys_982_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_989_, lean_object* v_x_990_, lean_object* v_x_991_, lean_object* v_x_992_, lean_object* v_x_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_990_, v_x_991_, v_x_992_, v_x_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___lam__0(lean_object* v_e_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(v_e_995_, v___y_996_, v___y_997_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___lam__0___boxed(lean_object* v_e_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___lam__0(v_e_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec(v___y_1010_);
return v_res_1022_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0___closed__0));
v___x_1027_ = l_Lean_stringToMessageData(v___x_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0(lean_object* v___x_1028_, lean_object* v___x_1029_, lean_object* v___f_1030_, lean_object* v___x_1031_, lean_object* v___f_1032_, lean_object* v_e_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_1033_, v___y_1035_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; uint8_t v___x_1048_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_a_1047_);
lean_dec_ref_known(v___x_1046_, 1);
v___x_1048_ = lean_unbox(v_a_1047_);
lean_dec(v_a_1047_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1449__overap_1052_; lean_object* v___x_1053_; 
v___x_1049_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0___closed__1);
lean_inc_ref(v_e_1033_);
v___x_1050_ = l_Lean_indentExpr(v_e_1033_);
v___x_1051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1049_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
lean_inc_ref(v___x_1028_);
v___x_1449__overap_1052_ = l_Lean_throwError___redArg(v___x_1028_, v___x_1029_, v___x_1051_);
lean_inc(v___y_1044_);
lean_inc_ref(v___y_1043_);
lean_inc(v___y_1042_);
lean_inc_ref(v___y_1041_);
lean_inc(v___y_1040_);
lean_inc_ref(v___y_1039_);
lean_inc(v___y_1038_);
lean_inc_ref(v___y_1037_);
lean_inc(v___y_1036_);
lean_inc(v___y_1035_);
lean_inc(v___y_1034_);
v___x_1053_ = lean_apply_12(v___x_1449__overap_1052_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, lean_box(0));
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v___x_1452__overap_1054_; lean_object* v___x_1055_; 
lean_dec_ref_known(v___x_1053_, 1);
v___x_1452__overap_1054_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v___f_1030_, v___x_1028_, v___x_1031_, v___f_1032_, v_e_1033_);
lean_inc(v___y_1044_);
lean_inc_ref(v___y_1043_);
lean_inc(v___y_1042_);
lean_inc_ref(v___y_1041_);
lean_inc(v___y_1040_);
lean_inc_ref(v___y_1039_);
lean_inc(v___y_1038_);
lean_inc_ref(v___y_1037_);
lean_inc(v___y_1036_);
lean_inc(v___y_1035_);
lean_inc(v___y_1034_);
v___x_1055_ = lean_apply_12(v___x_1452__overap_1054_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, lean_box(0));
return v___x_1055_;
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec_ref(v_e_1033_);
lean_dec_ref(v___f_1032_);
lean_dec_ref(v___x_1031_);
lean_dec(v___f_1030_);
lean_dec_ref(v___x_1028_);
v_a_1056_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1053_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1053_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
else
{
lean_object* v___x_1456__overap_1064_; lean_object* v___x_1065_; 
lean_dec_ref(v___x_1029_);
v___x_1456__overap_1064_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v___f_1030_, v___x_1028_, v___x_1031_, v___f_1032_, v_e_1033_);
lean_inc(v___y_1044_);
lean_inc_ref(v___y_1043_);
lean_inc(v___y_1042_);
lean_inc_ref(v___y_1041_);
lean_inc(v___y_1040_);
lean_inc_ref(v___y_1039_);
lean_inc(v___y_1038_);
lean_inc_ref(v___y_1037_);
lean_inc(v___y_1036_);
lean_inc(v___y_1035_);
lean_inc(v___y_1034_);
v___x_1065_ = lean_apply_12(v___x_1456__overap_1064_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, lean_box(0));
return v___x_1065_;
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_dec_ref(v_e_1033_);
lean_dec_ref(v___f_1032_);
lean_dec_ref(v___x_1031_);
lean_dec(v___f_1030_);
lean_dec_ref(v___x_1029_);
lean_dec_ref(v___x_1028_);
v_a_1066_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1046_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1046_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0___boxed(lean_object** _args){
lean_object* v___x_1074_ = _args[0];
lean_object* v___x_1075_ = _args[1];
lean_object* v___f_1076_ = _args[2];
lean_object* v___x_1077_ = _args[3];
lean_object* v___f_1078_ = _args[4];
lean_object* v_e_1079_ = _args[5];
lean_object* v___y_1080_ = _args[6];
lean_object* v___y_1081_ = _args[7];
lean_object* v___y_1082_ = _args[8];
lean_object* v___y_1083_ = _args[9];
lean_object* v___y_1084_ = _args[10];
lean_object* v___y_1085_ = _args[11];
lean_object* v___y_1086_ = _args[12];
lean_object* v___y_1087_ = _args[13];
lean_object* v___y_1088_ = _args[14];
lean_object* v___y_1089_ = _args[15];
lean_object* v___y_1090_ = _args[16];
lean_object* v___y_1091_ = _args[17];
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0(v___x_1074_, v___x_1075_, v___f_1076_, v___x_1077_, v___f_1078_, v_e_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec(v___y_1080_);
return v_res_1092_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__0(void){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_instMonadEIO___redArg();
return v___x_1093_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__1(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__0);
v___x_1095_ = l_StateRefT_x27_instMonad___redArg(v___x_1094_);
return v___x_1095_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__7(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___f_1102_; 
v___x_1101_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_1102_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1102_, 0, v___x_1101_);
return v___f_1102_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__8(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___f_1104_; 
v___x_1103_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_1104_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1104_, 0, v___x_1103_);
return v___f_1104_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__9(void){
_start:
{
lean_object* v___f_1105_; lean_object* v___f_1106_; lean_object* v___x_1107_; 
v___f_1105_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__8, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__8_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__8);
v___f_1106_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__7, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__7_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__7);
v___x_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___f_1106_);
lean_ctor_set(v___x_1107_, 1, v___f_1105_);
return v___x_1107_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__10(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___f_1109_; 
v___x_1108_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__9, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__9_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__9);
v___f_1109_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1109_, 0, v___x_1108_);
return v___f_1109_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__11(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___f_1111_; 
v___x_1110_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__9, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__9_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__9);
v___f_1111_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1111_, 0, v___x_1110_);
return v___f_1111_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__12(void){
_start:
{
lean_object* v___f_1112_; lean_object* v___f_1113_; lean_object* v___x_1114_; 
v___f_1112_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__11, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__11_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__11);
v___f_1113_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__10, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__10_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__10);
v___x_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___f_1113_);
lean_ctor_set(v___x_1114_, 1, v___f_1112_);
return v___x_1114_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__13(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___f_1116_; 
v___x_1115_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__12);
v___f_1116_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1116_, 0, v___x_1115_);
return v___f_1116_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__14(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___f_1118_; 
v___x_1117_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__12);
v___f_1118_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1118_, 0, v___x_1117_);
return v___f_1118_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__15(void){
_start:
{
lean_object* v___f_1119_; lean_object* v___f_1120_; lean_object* v___x_1121_; 
v___f_1119_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__14, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__14_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__14);
v___f_1120_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__13, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__13_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__13);
v___x_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___f_1120_);
lean_ctor_set(v___x_1121_, 1, v___f_1119_);
return v___x_1121_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__16(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___f_1123_; 
v___x_1122_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__15, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__15_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__15);
v___f_1123_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1123_, 0, v___x_1122_);
return v___f_1123_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__17(void){
_start:
{
lean_object* v___x_1124_; lean_object* v___f_1125_; 
v___x_1124_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__15, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__15_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__15);
v___f_1125_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1125_, 0, v___x_1124_);
return v___f_1125_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__18(void){
_start:
{
lean_object* v___f_1126_; lean_object* v___f_1127_; lean_object* v___x_1128_; 
v___f_1126_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__17, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__17_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__17);
v___f_1127_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__16, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__16_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__16);
v___x_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___f_1127_);
lean_ctor_set(v___x_1128_, 1, v___f_1126_);
return v___x_1128_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__19(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___f_1130_; 
v___x_1129_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__18, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__18_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__18);
v___f_1130_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1130_, 0, v___x_1129_);
return v___f_1130_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__20(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___f_1132_; 
v___x_1131_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__18, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__18_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__18);
v___f_1132_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1132_, 0, v___x_1131_);
return v___f_1132_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__21(void){
_start:
{
lean_object* v___f_1133_; lean_object* v___f_1134_; lean_object* v___x_1135_; 
v___f_1133_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__20, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__20_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__20);
v___f_1134_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__19, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__19_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__19);
v___x_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___f_1134_);
lean_ctor_set(v___x_1135_, 1, v___f_1133_);
return v___x_1135_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__22(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___f_1137_; 
v___x_1136_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__21, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__21_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__21);
v___f_1137_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1137_, 0, v___x_1136_);
return v___f_1137_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__23(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___f_1139_; 
v___x_1138_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__21, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__21_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__21);
v___f_1139_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1139_, 0, v___x_1138_);
return v___f_1139_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__24(void){
_start:
{
lean_object* v___f_1140_; lean_object* v___f_1141_; lean_object* v___x_1142_; 
v___f_1140_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__23, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__23_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__23);
v___f_1141_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__22, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__22_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__22);
v___x_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___f_1141_);
lean_ctor_set(v___x_1142_, 1, v___f_1140_);
return v___x_1142_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__25(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___f_1144_; 
v___x_1143_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__24, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__24_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__24);
v___f_1144_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1144_, 0, v___x_1143_);
return v___f_1144_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__26(void){
_start:
{
lean_object* v___x_1145_; lean_object* v___f_1146_; 
v___x_1145_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__24, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__24_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__24);
v___f_1146_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1146_, 0, v___x_1145_);
return v___f_1146_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__27(void){
_start:
{
lean_object* v___f_1147_; lean_object* v___f_1148_; lean_object* v___x_1149_; 
v___f_1147_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__26, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__26_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__26);
v___f_1148_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__25, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__25_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__25);
v___x_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___f_1148_);
lean_ctor_set(v___x_1149_, 1, v___f_1147_);
return v___x_1149_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__28(void){
_start:
{
lean_object* v___x_1150_; lean_object* v___f_1151_; 
v___x_1150_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__27, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__27_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__27);
v___f_1151_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1151_, 0, v___x_1150_);
return v___f_1151_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__29(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___f_1153_; 
v___x_1152_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__27, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__27_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__27);
v___f_1153_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1153_, 0, v___x_1152_);
return v___f_1153_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__30(void){
_start:
{
lean_object* v___f_1154_; lean_object* v___f_1155_; lean_object* v___x_1156_; 
v___f_1154_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__29, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__29_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__29);
v___f_1155_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__28, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__28_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__28);
v___x_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___f_1155_);
lean_ctor_set(v___x_1156_, 1, v___f_1154_);
return v___x_1156_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__31(void){
_start:
{
lean_object* v___x_1157_; lean_object* v___f_1158_; 
v___x_1157_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__30, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__30_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__30);
v___f_1158_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1158_, 0, v___x_1157_);
return v___f_1158_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__32(void){
_start:
{
lean_object* v___x_1159_; lean_object* v___f_1160_; 
v___x_1159_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__30, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__30_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__30);
v___f_1160_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1160_, 0, v___x_1159_);
return v___f_1160_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__33(void){
_start:
{
lean_object* v___f_1161_; lean_object* v___f_1162_; lean_object* v___x_1163_; 
v___f_1161_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__32, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__32_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__32);
v___f_1162_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__31, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__31_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__31);
v___x_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___f_1162_);
lean_ctor_set(v___x_1163_, 1, v___f_1161_);
return v___x_1163_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__37(void){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1167_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1168_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__36));
v___x_1169_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__35));
v___x_1170_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1169_, v___x_1168_, v___x_1167_);
return v___x_1170_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__38(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___f_1172_; lean_object* v___f_1173_; lean_object* v___x_1174_; 
v___x_1171_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__37, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__37_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__37);
v___f_1172_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__6));
v___f_1173_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__34));
v___x_1174_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1173_, v___f_1172_, v___x_1171_);
return v___x_1174_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__39(void){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1175_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__38, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__38_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__38);
v___x_1176_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__36));
v___x_1177_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__35));
v___x_1178_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1177_, v___x_1176_, v___x_1175_);
return v___x_1178_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__40(void){
_start:
{
lean_object* v___x_1179_; lean_object* v___f_1180_; lean_object* v___f_1181_; lean_object* v___x_1182_; 
v___x_1179_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__39, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__39_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__39);
v___f_1180_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__6));
v___f_1181_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__34));
v___x_1182_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1181_, v___f_1180_, v___x_1179_);
return v___x_1182_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__41(void){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1183_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__40, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__40_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__40);
v___x_1184_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__36));
v___x_1185_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__35));
v___x_1186_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1185_, v___x_1184_, v___x_1183_);
return v___x_1186_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__42(void){
_start:
{
lean_object* v___x_1187_; lean_object* v___f_1188_; lean_object* v___f_1189_; lean_object* v___x_1190_; 
v___x_1187_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__41, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__41_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__41);
v___f_1188_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__6));
v___f_1189_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__34));
v___x_1190_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1189_, v___f_1188_, v___x_1187_);
return v___x_1190_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__43(void){
_start:
{
lean_object* v___x_1191_; lean_object* v___f_1192_; lean_object* v___f_1193_; lean_object* v___x_1194_; 
v___x_1191_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__42, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__42_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__42);
v___f_1192_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__6));
v___f_1193_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__34));
v___x_1194_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1193_, v___f_1192_, v___x_1191_);
return v___x_1194_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__44(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1195_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__43, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__43_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__43);
v___x_1196_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__36));
v___x_1197_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__35));
v___x_1198_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1197_, v___x_1196_, v___x_1195_);
return v___x_1198_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__45(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___f_1200_; lean_object* v___f_1201_; lean_object* v___x_1202_; 
v___x_1199_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__44, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__44_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__44);
v___f_1200_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__6));
v___f_1201_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__34));
v___x_1202_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1201_, v___f_1200_, v___x_1199_);
return v___x_1202_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__48(void){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___f_1209_; 
v___x_1207_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__36));
v___x_1208_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_1209_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1209_, 0, v___x_1208_);
lean_closure_set(v___f_1209_, 1, v___x_1207_);
return v___f_1209_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__49(void){
_start:
{
lean_object* v___f_1210_; lean_object* v___f_1211_; lean_object* v___f_1212_; 
v___f_1210_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__6));
v___f_1211_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__48, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__48_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__48);
v___f_1212_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1212_, 0, v___f_1211_);
lean_closure_set(v___f_1212_, 1, v___f_1210_);
return v___f_1212_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__50(void){
_start:
{
lean_object* v___x_1213_; lean_object* v___f_1214_; lean_object* v___f_1215_; 
v___x_1213_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__36));
v___f_1214_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__49, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__49_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__49);
v___f_1215_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1215_, 0, v___f_1214_);
lean_closure_set(v___f_1215_, 1, v___x_1213_);
return v___f_1215_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__51(void){
_start:
{
lean_object* v___f_1216_; lean_object* v___f_1217_; lean_object* v___f_1218_; 
v___f_1216_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__6));
v___f_1217_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__50, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__50_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__50);
v___f_1218_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1218_, 0, v___f_1217_);
lean_closure_set(v___f_1218_, 1, v___f_1216_);
return v___f_1218_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__52(void){
_start:
{
lean_object* v___f_1219_; lean_object* v___f_1220_; lean_object* v___f_1221_; 
v___f_1219_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__6));
v___f_1220_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__51, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__51_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__51);
v___f_1221_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1221_, 0, v___f_1220_);
lean_closure_set(v___f_1221_, 1, v___f_1219_);
return v___f_1221_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__53(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___f_1223_; lean_object* v___f_1224_; 
v___x_1222_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__36));
v___f_1223_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__52, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__52_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__52);
v___f_1224_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1224_, 0, v___f_1223_);
lean_closure_set(v___f_1224_, 1, v___x_1222_);
return v___f_1224_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__54(void){
_start:
{
lean_object* v___f_1225_; lean_object* v___f_1226_; lean_object* v___f_1227_; 
v___f_1225_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__6));
v___f_1226_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__53, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__53_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__53);
v___f_1227_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1227_, 0, v___f_1226_);
lean_closure_set(v___f_1227_, 1, v___f_1225_);
return v___f_1227_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM(void){
_start:
{
lean_object* v___x_1228_; lean_object* v_toApplicative_1229_; lean_object* v_toFunctor_1230_; lean_object* v_toSeq_1231_; lean_object* v_toSeqLeft_1232_; lean_object* v_toSeqRight_1233_; lean_object* v___f_1234_; lean_object* v___f_1235_; lean_object* v___f_1236_; lean_object* v___f_1237_; lean_object* v___x_1238_; lean_object* v___f_1239_; lean_object* v___f_1240_; lean_object* v___f_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v_toApplicative_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1289_; 
v___x_1228_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__1);
v_toApplicative_1229_ = lean_ctor_get(v___x_1228_, 0);
v_toFunctor_1230_ = lean_ctor_get(v_toApplicative_1229_, 0);
v_toSeq_1231_ = lean_ctor_get(v_toApplicative_1229_, 2);
v_toSeqLeft_1232_ = lean_ctor_get(v_toApplicative_1229_, 3);
v_toSeqRight_1233_ = lean_ctor_get(v_toApplicative_1229_, 4);
v___f_1234_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__2));
v___f_1235_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__3));
lean_inc_ref_n(v_toFunctor_1230_, 2);
v___f_1236_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1236_, 0, v_toFunctor_1230_);
v___f_1237_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1237_, 0, v_toFunctor_1230_);
v___x_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___f_1236_);
lean_ctor_set(v___x_1238_, 1, v___f_1237_);
lean_inc(v_toSeqRight_1233_);
v___f_1239_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1239_, 0, v_toSeqRight_1233_);
lean_inc(v_toSeqLeft_1232_);
v___f_1240_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1240_, 0, v_toSeqLeft_1232_);
lean_inc(v_toSeq_1231_);
v___f_1241_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1241_, 0, v_toSeq_1231_);
v___x_1242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1238_);
lean_ctor_set(v___x_1242_, 1, v___f_1234_);
lean_ctor_set(v___x_1242_, 2, v___f_1241_);
lean_ctor_set(v___x_1242_, 3, v___f_1240_);
lean_ctor_set(v___x_1242_, 4, v___f_1239_);
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
lean_ctor_set(v___x_1243_, 1, v___f_1235_);
v___x_1244_ = l_StateRefT_x27_instMonad___redArg(v___x_1243_);
v_toApplicative_1245_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1289_ == 0)
{
lean_object* v_unused_1290_; 
v_unused_1290_ = lean_ctor_get(v___x_1244_, 1);
lean_dec(v_unused_1290_);
v___x_1247_ = v___x_1244_;
v_isShared_1248_ = v_isSharedCheck_1289_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_toApplicative_1245_);
lean_dec(v___x_1244_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1289_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v_toFunctor_1249_; lean_object* v_toSeq_1250_; lean_object* v_toSeqLeft_1251_; lean_object* v_toSeqRight_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1287_; 
v_toFunctor_1249_ = lean_ctor_get(v_toApplicative_1245_, 0);
v_toSeq_1250_ = lean_ctor_get(v_toApplicative_1245_, 2);
v_toSeqLeft_1251_ = lean_ctor_get(v_toApplicative_1245_, 3);
v_toSeqRight_1252_ = lean_ctor_get(v_toApplicative_1245_, 4);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_toApplicative_1245_);
if (v_isSharedCheck_1287_ == 0)
{
lean_object* v_unused_1288_; 
v_unused_1288_ = lean_ctor_get(v_toApplicative_1245_, 1);
lean_dec(v_unused_1288_);
v___x_1254_ = v_toApplicative_1245_;
v_isShared_1255_ = v_isSharedCheck_1287_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_toSeqRight_1252_);
lean_inc(v_toSeqLeft_1251_);
lean_inc(v_toSeq_1250_);
lean_inc(v_toFunctor_1249_);
lean_dec(v_toApplicative_1245_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1287_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___f_1256_; lean_object* v___f_1257_; lean_object* v___f_1258_; lean_object* v___f_1259_; lean_object* v___x_1260_; lean_object* v___f_1261_; lean_object* v___f_1262_; lean_object* v___f_1263_; lean_object* v___x_1265_; 
v___f_1256_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__4));
v___f_1257_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__5));
lean_inc_ref(v_toFunctor_1249_);
v___f_1258_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1258_, 0, v_toFunctor_1249_);
v___f_1259_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1259_, 0, v_toFunctor_1249_);
v___x_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___f_1258_);
lean_ctor_set(v___x_1260_, 1, v___f_1259_);
v___f_1261_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1261_, 0, v_toSeqRight_1252_);
v___f_1262_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1262_, 0, v_toSeqLeft_1251_);
v___f_1263_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1263_, 0, v_toSeq_1250_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 4, v___f_1261_);
lean_ctor_set(v___x_1254_, 3, v___f_1262_);
lean_ctor_set(v___x_1254_, 2, v___f_1263_);
lean_ctor_set(v___x_1254_, 1, v___f_1256_);
lean_ctor_set(v___x_1254_, 0, v___x_1260_);
v___x_1265_ = v___x_1254_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1260_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v___f_1256_);
lean_ctor_set(v_reuseFailAlloc_1286_, 2, v___f_1263_);
lean_ctor_set(v_reuseFailAlloc_1286_, 3, v___f_1262_);
lean_ctor_set(v_reuseFailAlloc_1286_, 4, v___f_1261_);
v___x_1265_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
lean_object* v___x_1267_; 
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 1, v___f_1257_);
lean_ctor_set(v___x_1247_, 0, v___x_1265_);
v___x_1267_ = v___x_1247_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1265_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v___f_1257_);
v___x_1267_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v_toMonadRef_1278_; lean_object* v___f_1279_; lean_object* v___f_1280_; lean_object* v___f_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___f_1284_; 
v___x_1268_ = l_StateRefT_x27_instMonad___redArg(v___x_1267_);
v___x_1269_ = l_ReaderT_instMonad___redArg(v___x_1268_);
v___x_1270_ = l_StateRefT_x27_instMonad___redArg(v___x_1269_);
v___x_1271_ = l_ReaderT_instMonad___redArg(v___x_1270_);
v___x_1272_ = l_ReaderT_instMonad___redArg(v___x_1271_);
v___x_1273_ = l_StateRefT_x27_instMonad___redArg(v___x_1272_);
v___x_1274_ = l_ReaderT_instMonad___redArg(v___x_1273_);
v___x_1275_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM;
v___x_1276_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__33, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__33_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__33);
v___x_1277_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__45, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__45_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__45);
v_toMonadRef_1278_ = lean_ctor_get(v___x_1277_, 0);
v___f_1279_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__47));
v___f_1280_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___closed__0));
v___f_1281_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__54, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__54_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__54);
lean_inc_ref(v___x_1274_);
v___x_1282_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1281_, v___x_1274_);
lean_inc_ref(v_toMonadRef_1278_);
v___x_1283_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1276_);
lean_ctor_set(v___x_1283_, 1, v_toMonadRef_1278_);
lean_ctor_set(v___x_1283_, 2, v___x_1282_);
v___f_1284_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0___boxed), 18, 5);
lean_closure_set(v___f_1284_, 0, v___x_1274_);
lean_closure_set(v___f_1284_, 1, v___x_1283_);
lean_closure_set(v___f_1284_, 2, v___f_1279_);
lean_closure_set(v___f_1284_, 3, v___x_1275_);
lean_closure_set(v___f_1284_, 4, v___f_1280_);
return v___f_1284_;
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
