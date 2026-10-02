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
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___redArg___lam__0___boxed(lean_object*, lean_object*);
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
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__7_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__7_value),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__6_value)} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___redArg(lean_object* v_ringId_1_, lean_object* v_x_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_14_ = lean_unsigned_to_nat(0u);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_ringId_1_);
lean_ctor_set(v___x_15_, 1, v___x_14_);
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
v___x_16_ = lean_apply_12(v_x_2_, v___x_15_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, lean_box(0));
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___redArg___boxed(lean_object* v_ringId_17_, lean_object* v_x_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___redArg(v_ringId_17_, v_x_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_, v_a_27_, v_a_28_);
lean_dec(v_a_28_);
lean_dec_ref(v_a_27_);
lean_dec(v_a_26_);
lean_dec_ref(v_a_25_);
lean_dec(v_a_24_);
lean_dec_ref(v_a_23_);
lean_dec(v_a_22_);
lean_dec_ref(v_a_21_);
lean_dec(v_a_20_);
lean_dec(v_a_19_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run(lean_object* v_00_u03b1_31_, lean_object* v_ringId_32_, lean_object* v_x_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_46_, 0, v_ringId_32_);
lean_ctor_set(v___x_46_, 1, v___x_45_);
lean_inc(v_a_43_);
lean_inc_ref(v_a_42_);
lean_inc(v_a_41_);
lean_inc_ref(v_a_40_);
lean_inc(v_a_39_);
lean_inc_ref(v_a_38_);
lean_inc(v_a_37_);
lean_inc_ref(v_a_36_);
lean_inc(v_a_35_);
lean_inc(v_a_34_);
v___x_47_ = lean_apply_12(v_x_33_, v___x_46_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, lean_box(0));
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___boxed(lean_object* v_00_u03b1_48_, lean_object* v_ringId_49_, lean_object* v_x_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run(v_00_u03b1_48_, v_ringId_49_, v_x_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
lean_dec(v_a_58_);
lean_dec_ref(v_a_57_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
lean_dec(v_a_54_);
lean_dec_ref(v_a_53_);
lean_dec(v_a_52_);
lean_dec(v_a_51_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__0(lean_object* v_e_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_Meta_Sym_canon(v_e_63_, v___y_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_a_77_; lean_object* v___x_78_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc(v_a_77_);
lean_dec_ref_known(v___x_76_, 1);
v___x_78_ = l_Lean_Meta_Sym_shareCommon(v_a_77_, v___y_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_);
return v___x_78_;
}
else
{
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__0___boxed(lean_object* v_e_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__0(v_e_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__1(lean_object* v_e_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_e_93_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
return v___x_106_;
}
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
lean_dec_ref(v___y_108_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0_spec__0(lean_object* v_msgData_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v___x_133_; lean_object* v_env_134_; lean_object* v___x_135_; lean_object* v_toCold_136_; lean_object* v_mctx_137_; lean_object* v_lctx_138_; lean_object* v_options_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_133_ = lean_st_ref_get(v___y_131_);
v_env_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc_ref(v_env_134_);
lean_dec(v___x_133_);
v___x_135_ = lean_st_ref_get(v___y_129_);
v_toCold_136_ = lean_ctor_get(v___y_130_, 0);
v_mctx_137_ = lean_ctor_get(v___x_135_, 0);
lean_inc_ref(v_mctx_137_);
lean_dec(v___x_135_);
v_lctx_138_ = lean_ctor_get(v___y_128_, 2);
v_options_139_ = lean_ctor_get(v_toCold_136_, 2);
lean_inc_ref(v_options_139_);
lean_inc_ref(v_lctx_138_);
v___x_140_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_140_, 0, v_env_134_);
lean_ctor_set(v___x_140_, 1, v_mctx_137_);
lean_ctor_set(v___x_140_, 2, v_lctx_138_);
lean_ctor_set(v___x_140_, 3, v_options_139_);
v___x_141_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v_msgData_127_);
v___x_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0_spec__0___boxed(lean_object* v_msgData_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0_spec__0(v_msgData_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg(lean_object* v_msg_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v_ref_156_; lean_object* v___x_157_; lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_166_; 
v_ref_156_ = lean_ctor_get(v___y_153_, 2);
v___x_157_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0_spec__0(v_msg_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
v_a_158_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_166_ == 0)
{
v___x_160_ = v___x_157_;
v_isShared_161_ = v_isSharedCheck_166_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_a_158_);
lean_dec(v___x_157_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_166_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v___x_164_; 
lean_inc(v_ref_156_);
v___x_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_162_, 0, v_ref_156_);
lean_ctor_set(v___x_162_, 1, v_a_158_);
if (v_isShared_161_ == 0)
{
lean_ctor_set_tag(v___x_160_, 1);
lean_ctor_set(v___x_160_, 0, v___x_162_);
v___x_164_ = v___x_160_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg___boxed(lean_object* v_msg_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg(v_msg_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
return v_res_173_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__1(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__0));
v___x_176_ = l_Lean_stringToMessageData(v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_183_, v_a_186_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_204_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_204_ == 0)
{
v___x_192_ = v___x_189_;
v_isShared_193_ = v_isSharedCheck_204_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_189_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_204_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v_ringId_194_; lean_object* v_ncRings_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v_ringId_194_ = lean_ctor_get(v_a_177_, 0);
v_ncRings_195_ = lean_ctor_get(v_a_190_, 3);
lean_inc_ref(v_ncRings_195_);
lean_dec(v_a_190_);
v___x_196_ = lean_array_get_size(v_ncRings_195_);
v___x_197_ = lean_nat_dec_lt(v_ringId_194_, v___x_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; lean_object* v___x_199_; 
lean_dec_ref(v_ncRings_195_);
lean_del_object(v___x_192_);
v___x_198_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__1);
v___x_199_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg(v___x_198_, v_a_184_, v_a_185_, v_a_186_, v_a_187_);
return v___x_199_;
}
else
{
lean_object* v___x_200_; lean_object* v___x_202_; 
v___x_200_ = lean_array_fget(v_ncRings_195_, v_ringId_194_);
lean_dec_ref(v_ncRings_195_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 0, v___x_200_);
v___x_202_ = v___x_192_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_200_);
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
else
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_212_; 
v_a_205_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_212_ == 0)
{
v___x_207_ = v___x_189_;
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_189_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_a_205_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___boxed(lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0(lean_object* v_00_u03b1_226_, lean_object* v_msg_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg(v_msg_227_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___boxed(lean_object* v_00_u03b1_241_, lean_object* v_msg_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0(v_00_u03b1_241_, v_msg_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v___y_245_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___lam__0(lean_object* v_ringId_256_, lean_object* v_f_257_, lean_object* v_s_258_){
_start:
{
lean_object* v_exp_259_; lean_object* v_rings_260_; lean_object* v_semirings_261_; lean_object* v_ncRings_262_; lean_object* v_ncSemirings_263_; lean_object* v_typeClassify_264_; lean_object* v_orders_265_; lean_object* v_typeOrderClassify_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v_exp_259_ = lean_ctor_get(v_s_258_, 0);
v_rings_260_ = lean_ctor_get(v_s_258_, 1);
v_semirings_261_ = lean_ctor_get(v_s_258_, 2);
v_ncRings_262_ = lean_ctor_get(v_s_258_, 3);
v_ncSemirings_263_ = lean_ctor_get(v_s_258_, 4);
v_typeClassify_264_ = lean_ctor_get(v_s_258_, 5);
v_orders_265_ = lean_ctor_get(v_s_258_, 6);
v_typeOrderClassify_266_ = lean_ctor_get(v_s_258_, 7);
v___x_267_ = lean_array_get_size(v_ncRings_262_);
v___x_268_ = lean_nat_dec_lt(v_ringId_256_, v___x_267_);
if (v___x_268_ == 0)
{
lean_dec_ref(v_f_257_);
return v_s_258_;
}
else
{
lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_280_; 
lean_inc_ref(v_typeOrderClassify_266_);
lean_inc_ref(v_orders_265_);
lean_inc_ref(v_typeClassify_264_);
lean_inc_ref(v_ncSemirings_263_);
lean_inc_ref(v_ncRings_262_);
lean_inc_ref(v_semirings_261_);
lean_inc_ref(v_rings_260_);
lean_inc(v_exp_259_);
v_isSharedCheck_280_ = !lean_is_exclusive(v_s_258_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; lean_object* v_unused_282_; lean_object* v_unused_283_; lean_object* v_unused_284_; lean_object* v_unused_285_; lean_object* v_unused_286_; lean_object* v_unused_287_; lean_object* v_unused_288_; 
v_unused_281_ = lean_ctor_get(v_s_258_, 7);
lean_dec(v_unused_281_);
v_unused_282_ = lean_ctor_get(v_s_258_, 6);
lean_dec(v_unused_282_);
v_unused_283_ = lean_ctor_get(v_s_258_, 5);
lean_dec(v_unused_283_);
v_unused_284_ = lean_ctor_get(v_s_258_, 4);
lean_dec(v_unused_284_);
v_unused_285_ = lean_ctor_get(v_s_258_, 3);
lean_dec(v_unused_285_);
v_unused_286_ = lean_ctor_get(v_s_258_, 2);
lean_dec(v_unused_286_);
v_unused_287_ = lean_ctor_get(v_s_258_, 1);
lean_dec(v_unused_287_);
v_unused_288_ = lean_ctor_get(v_s_258_, 0);
lean_dec(v_unused_288_);
v___x_270_ = v_s_258_;
v_isShared_271_ = v_isSharedCheck_280_;
goto v_resetjp_269_;
}
else
{
lean_dec(v_s_258_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_280_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v_v_272_; lean_object* v___x_273_; lean_object* v_xs_x27_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
v_v_272_ = lean_array_fget(v_ncRings_262_, v_ringId_256_);
v___x_273_ = lean_box(0);
v_xs_x27_274_ = lean_array_fset(v_ncRings_262_, v_ringId_256_, v___x_273_);
v___x_275_ = lean_apply_1(v_f_257_, v_v_272_);
v___x_276_ = lean_array_fset(v_xs_x27_274_, v_ringId_256_, v___x_275_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 3, v___x_276_);
v___x_278_ = v___x_270_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_exp_259_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_rings_260_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_semirings_261_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_279_, 4, v_ncSemirings_263_);
lean_ctor_set(v_reuseFailAlloc_279_, 5, v_typeClassify_264_);
lean_ctor_set(v_reuseFailAlloc_279_, 6, v_orders_265_);
lean_ctor_set(v_reuseFailAlloc_279_, 7, v_typeOrderClassify_266_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___lam__0___boxed(lean_object* v_ringId_289_, lean_object* v_f_290_, lean_object* v_s_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___lam__0(v_ringId_289_, v_f_290_, v_s_291_);
lean_dec(v_ringId_289_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(lean_object* v_f_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v_ringId_297_; lean_object* v___f_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v_ringId_297_ = lean_ctor_get(v_a_294_, 0);
lean_inc(v_ringId_297_);
v___f_298_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_298_, 0, v_ringId_297_);
lean_closure_set(v___f_298_, 1, v_f_293_);
v___x_299_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_300_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_299_, v___f_298_, v_a_295_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___boxed(lean_object* v_f_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(v_f_301_, v_a_302_, v_a_303_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing(lean_object* v_f_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(v_f_306_, v_a_307_, v_a_313_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___boxed(lean_object* v_f_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing(v_f_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
lean_dec(v_a_323_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
return v_res_333_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_335_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__0));
v___x_336_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___boxed), 12, 0);
v___x_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v___x_335_);
return v___x_337_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM(void){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___redArg(lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_340_, v_a_341_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_353_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_353_ == 0)
{
v___x_346_ = v___x_343_;
v_isShared_347_ = v_isSharedCheck_353_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_343_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_353_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v_ringId_348_; lean_object* v___x_349_; lean_object* v___x_351_; 
v_ringId_348_ = lean_ctor_get(v_a_339_, 0);
v___x_349_ = l_Lean_Meta_Grind_Arith_CommRing_State_getNCRing(v_a_344_, v_ringId_348_);
lean_dec(v_a_344_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_349_);
v___x_351_ = v___x_346_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_349_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
else
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_361_; 
v_a_354_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_361_ == 0)
{
v___x_356_ = v___x_343_;
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_343_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_354_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___redArg___boxed(lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___redArg(v_a_362_, v_a_363_, v_a_364_);
lean_dec_ref(v_a_364_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState(lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___redArg(v_a_367_, v_a_368_, v_a_376_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___boxed(lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState(v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
lean_dec(v_a_384_);
lean_dec_ref(v_a_383_);
lean_dec(v_a_382_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg___lam__0(lean_object* v_ringId_393_, lean_object* v_f_394_, lean_object* v_s_395_){
_start:
{
lean_object* v_rings_396_; lean_object* v_exprToRingId_397_; lean_object* v_semirings_398_; lean_object* v_exprToSemiringId_399_; lean_object* v_ncRings_400_; lean_object* v_exprToNCRingId_401_; lean_object* v_ncSemirings_402_; lean_object* v_exprToNCSemiringId_403_; lean_object* v_steps_404_; uint8_t v_reportedMaxDegreeIssue_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_426_; 
v_rings_396_ = lean_ctor_get(v_s_395_, 0);
v_exprToRingId_397_ = lean_ctor_get(v_s_395_, 1);
v_semirings_398_ = lean_ctor_get(v_s_395_, 2);
v_exprToSemiringId_399_ = lean_ctor_get(v_s_395_, 3);
v_ncRings_400_ = lean_ctor_get(v_s_395_, 4);
v_exprToNCRingId_401_ = lean_ctor_get(v_s_395_, 5);
v_ncSemirings_402_ = lean_ctor_get(v_s_395_, 6);
v_exprToNCSemiringId_403_ = lean_ctor_get(v_s_395_, 7);
v_steps_404_ = lean_ctor_get(v_s_395_, 8);
v_reportedMaxDegreeIssue_405_ = lean_ctor_get_uint8(v_s_395_, sizeof(void*)*9);
v_isSharedCheck_426_ = !lean_is_exclusive(v_s_395_);
if (v_isSharedCheck_426_ == 0)
{
v___x_407_ = v_s_395_;
v_isShared_408_ = v_isSharedCheck_426_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_steps_404_);
lean_inc(v_exprToNCSemiringId_403_);
lean_inc(v_ncSemirings_402_);
lean_inc(v_exprToNCRingId_401_);
lean_inc(v_ncRings_400_);
lean_inc(v_exprToSemiringId_399_);
lean_inc(v_semirings_398_);
lean_inc(v_exprToRingId_397_);
lean_inc(v_rings_396_);
lean_dec(v_s_395_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_426_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_409_ = lean_unsigned_to_nat(1u);
v___x_410_ = lean_nat_add(v_ringId_393_, v___x_409_);
v___x_411_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default;
v___x_412_ = l_Array_rightpad___redArg(v___x_410_, v___x_411_, v_ncRings_400_);
lean_dec(v___x_410_);
v___x_413_ = lean_array_get_size(v___x_412_);
v___x_414_ = lean_nat_dec_lt(v_ringId_393_, v___x_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_416_; 
lean_dec_ref(v_f_394_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 4, v___x_412_);
v___x_416_ = v___x_407_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_rings_396_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_exprToRingId_397_);
lean_ctor_set(v_reuseFailAlloc_417_, 2, v_semirings_398_);
lean_ctor_set(v_reuseFailAlloc_417_, 3, v_exprToSemiringId_399_);
lean_ctor_set(v_reuseFailAlloc_417_, 4, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_417_, 5, v_exprToNCRingId_401_);
lean_ctor_set(v_reuseFailAlloc_417_, 6, v_ncSemirings_402_);
lean_ctor_set(v_reuseFailAlloc_417_, 7, v_exprToNCSemiringId_403_);
lean_ctor_set(v_reuseFailAlloc_417_, 8, v_steps_404_);
lean_ctor_set_uint8(v_reuseFailAlloc_417_, sizeof(void*)*9, v_reportedMaxDegreeIssue_405_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
else
{
lean_object* v_v_418_; lean_object* v___x_419_; lean_object* v_xs_x27_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_424_; 
v_v_418_ = lean_array_fget(v___x_412_, v_ringId_393_);
v___x_419_ = lean_box(0);
v_xs_x27_420_ = lean_array_fset(v___x_412_, v_ringId_393_, v___x_419_);
v___x_421_ = lean_apply_1(v_f_394_, v_v_418_);
v___x_422_ = lean_array_fset(v_xs_x27_420_, v_ringId_393_, v___x_421_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 4, v___x_422_);
v___x_424_ = v___x_407_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_rings_396_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_exprToRingId_397_);
lean_ctor_set(v_reuseFailAlloc_425_, 2, v_semirings_398_);
lean_ctor_set(v_reuseFailAlloc_425_, 3, v_exprToSemiringId_399_);
lean_ctor_set(v_reuseFailAlloc_425_, 4, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_425_, 5, v_exprToNCRingId_401_);
lean_ctor_set(v_reuseFailAlloc_425_, 6, v_ncSemirings_402_);
lean_ctor_set(v_reuseFailAlloc_425_, 7, v_exprToNCSemiringId_403_);
lean_ctor_set(v_reuseFailAlloc_425_, 8, v_steps_404_);
lean_ctor_set_uint8(v_reuseFailAlloc_425_, sizeof(void*)*9, v_reportedMaxDegreeIssue_405_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg___lam__0___boxed(lean_object* v_ringId_427_, lean_object* v_f_428_, lean_object* v_s_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg___lam__0(v_ringId_427_, v_f_428_, v_s_429_);
lean_dec(v_ringId_427_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg(lean_object* v_f_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_ringId_435_; lean_object* v___f_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v_ringId_435_ = lean_ctor_get(v_a_432_, 0);
lean_inc(v_ringId_435_);
v___f_436_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_436_, 0, v_ringId_435_);
lean_closure_set(v___f_436_, 1, v_f_431_);
v___x_437_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_438_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_437_, v___f_436_, v_a_433_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg___boxed(lean_object* v_f_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg(v_f_439_, v_a_440_, v_a_441_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState(lean_object* v_f_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg(v_f_444_, v_a_445_, v_a_446_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___boxed(lean_object* v_f_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState(v_f_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_);
lean_dec(v_a_469_);
lean_dec_ref(v_a_468_);
lean_dec(v_a_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_a_465_);
lean_dec_ref(v_a_464_);
lean_dec(v_a_463_);
lean_dec_ref(v_a_462_);
lean_dec(v_a_461_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
return v_res_471_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM___closed__1(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_473_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM___closed__0));
v___x_474_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___boxed), 12, 0);
v___x_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
lean_ctor_set(v___x_475_, 1, v___x_473_);
return v___x_475_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM(void){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM___closed__1);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___lam__0(lean_object* v___x_477_, lean_object* v_x_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___redArg(v___y_479_, v___y_480_, v___y_488_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_507_; 
v_a_492_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_507_ == 0)
{
v___x_494_ = v___x_491_;
v_isShared_495_ = v_isSharedCheck_507_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_491_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_507_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v_vars_496_; lean_object* v_size_497_; uint8_t v___x_498_; 
v_vars_496_ = lean_ctor_get(v_a_492_, 0);
lean_inc_ref(v_vars_496_);
lean_dec(v_a_492_);
v_size_497_ = lean_ctor_get(v_vars_496_, 2);
v___x_498_ = lean_nat_dec_lt(v_x_478_, v_size_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_501_; 
lean_dec_ref(v_vars_496_);
v___x_499_ = l_outOfBounds___redArg(v___x_477_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v___x_499_);
v___x_501_ = v___x_494_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_499_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
else
{
lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_503_ = l_Lean_PersistentArray_get_x21___redArg(v___x_477_, v_vars_496_, v_x_478_);
lean_dec_ref(v_vars_496_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v___x_503_);
v___x_505_ = v___x_494_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
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
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
v_a_508_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_491_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_491_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___lam__0___boxed(lean_object* v___x_516_, lean_object* v_x_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___lam__0(v___x_516_, v_x_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v_x_517_);
lean_dec_ref(v___x_516_);
return v_res_530_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___closed__0(void){
_start:
{
lean_object* v___x_531_; lean_object* v___f_532_; 
v___x_531_ = l_Lean_instInhabitedExpr;
v___f_532_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___lam__0___boxed), 14, 1);
lean_closure_set(v___f_532_, 0, v___x_531_);
return v___f_532_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM(void){
_start:
{
lean_object* v___f_533_; 
v___f_533_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarNonCommRingM___closed__0);
return v___f_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_534_, lean_object* v_vals_535_, lean_object* v_i_536_, lean_object* v_k_537_){
_start:
{
lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_538_ = lean_array_get_size(v_keys_534_);
v___x_539_ = lean_nat_dec_lt(v_i_536_, v___x_538_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; 
lean_dec(v_i_536_);
v___x_540_ = lean_box(0);
return v___x_540_;
}
else
{
lean_object* v_k_x27_541_; size_t v___x_542_; size_t v___x_543_; uint8_t v___x_544_; 
v_k_x27_541_ = lean_array_fget_borrowed(v_keys_534_, v_i_536_);
v___x_542_ = lean_ptr_addr(v_k_537_);
v___x_543_ = lean_ptr_addr(v_k_x27_541_);
v___x_544_ = lean_usize_dec_eq(v___x_542_, v___x_543_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = lean_unsigned_to_nat(1u);
v___x_546_ = lean_nat_add(v_i_536_, v___x_545_);
lean_dec(v_i_536_);
v_i_536_ = v___x_546_;
goto _start;
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_array_fget_borrowed(v_vals_535_, v_i_536_);
lean_dec(v_i_536_);
lean_inc(v___x_548_);
v___x_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_550_, lean_object* v_vals_551_, lean_object* v_i_552_, lean_object* v_k_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_550_, v_vals_551_, v_i_552_, v_k_553_);
lean_dec_ref(v_k_553_);
lean_dec_ref(v_vals_551_);
lean_dec_ref(v_keys_550_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg(lean_object* v_x_555_, size_t v_x_556_, lean_object* v_x_557_){
_start:
{
if (lean_obj_tag(v_x_555_) == 0)
{
lean_object* v_es_558_; lean_object* v___x_559_; size_t v___x_560_; size_t v___x_561_; lean_object* v_j_562_; lean_object* v___x_563_; 
v_es_558_ = lean_ctor_get(v_x_555_, 0);
v___x_559_ = lean_box(2);
v___x_560_ = ((size_t)31ULL);
v___x_561_ = lean_usize_land(v_x_556_, v___x_560_);
v_j_562_ = lean_usize_to_nat(v___x_561_);
v___x_563_ = lean_array_get_borrowed(v___x_559_, v_es_558_, v_j_562_);
lean_dec(v_j_562_);
switch(lean_obj_tag(v___x_563_))
{
case 0:
{
lean_object* v_key_564_; lean_object* v_val_565_; size_t v___x_566_; size_t v___x_567_; uint8_t v___x_568_; 
v_key_564_ = lean_ctor_get(v___x_563_, 0);
v_val_565_ = lean_ctor_get(v___x_563_, 1);
v___x_566_ = lean_ptr_addr(v_x_557_);
v___x_567_ = lean_ptr_addr(v_key_564_);
v___x_568_ = lean_usize_dec_eq(v___x_566_, v___x_567_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; 
v___x_569_ = lean_box(0);
return v___x_569_;
}
else
{
lean_object* v___x_570_; 
lean_inc(v_val_565_);
v___x_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_570_, 0, v_val_565_);
return v___x_570_;
}
}
case 1:
{
lean_object* v_node_571_; size_t v___x_572_; size_t v___x_573_; 
v_node_571_ = lean_ctor_get(v___x_563_, 0);
v___x_572_ = ((size_t)5ULL);
v___x_573_ = lean_usize_shift_right(v_x_556_, v___x_572_);
v_x_555_ = v_node_571_;
v_x_556_ = v___x_573_;
goto _start;
}
default: 
{
lean_object* v___x_575_; 
v___x_575_ = lean_box(0);
return v___x_575_;
}
}
}
else
{
lean_object* v_ks_576_; lean_object* v_vs_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v_ks_576_ = lean_ctor_get(v_x_555_, 0);
v_vs_577_ = lean_ctor_get(v_x_555_, 1);
v___x_578_ = lean_unsigned_to_nat(0u);
v___x_579_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_576_, v_vs_577_, v___x_578_, v_x_557_);
return v___x_579_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_580_, lean_object* v_x_581_, lean_object* v_x_582_){
_start:
{
size_t v_x_905__boxed_583_; lean_object* v_res_584_; 
v_x_905__boxed_583_ = lean_unbox_usize(v_x_581_);
lean_dec(v_x_581_);
v_res_584_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg(v_x_580_, v_x_905__boxed_583_, v_x_582_);
lean_dec_ref(v_x_582_);
lean_dec_ref(v_x_580_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg(lean_object* v_x_585_, lean_object* v_x_586_){
_start:
{
size_t v___x_587_; size_t v___x_588_; size_t v___x_589_; uint64_t v___x_590_; size_t v___x_591_; lean_object* v___x_592_; 
v___x_587_ = lean_ptr_addr(v_x_586_);
v___x_588_ = ((size_t)3ULL);
v___x_589_ = lean_usize_shift_right(v___x_587_, v___x_588_);
v___x_590_ = lean_usize_to_uint64(v___x_589_);
v___x_591_ = lean_uint64_to_usize(v___x_590_);
v___x_592_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg(v_x_585_, v___x_591_, v_x_586_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg___boxed(lean_object* v_x_593_, lean_object* v_x_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg(v_x_593_, v_x_594_);
lean_dec_ref(v_x_594_);
lean_dec_ref(v_x_593_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg(lean_object* v_e_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_597_, v_a_598_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_610_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_610_ == 0)
{
v___x_603_ = v___x_600_;
v_isShared_604_ = v_isSharedCheck_610_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_600_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_610_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v_exprToNCRingId_605_; lean_object* v___x_606_; lean_object* v___x_608_; 
v_exprToNCRingId_605_ = lean_ctor_get(v_a_601_, 5);
lean_inc_ref(v_exprToNCRingId_605_);
lean_dec(v_a_601_);
v___x_606_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg(v_exprToNCRingId_605_, v_e_596_);
lean_dec_ref(v_exprToNCRingId_605_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_606_);
v___x_608_ = v___x_603_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
v_a_611_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_600_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_600_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_611_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg___boxed(lean_object* v_e_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg(v_e_619_, v_a_620_, v_a_621_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_e_619_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f(lean_object* v_e_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg(v_e_624_, v_a_625_, v_a_633_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___boxed(lean_object* v_e_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f(v_e_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
lean_dec(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
lean_dec(v_a_639_);
lean_dec(v_a_638_);
lean_dec_ref(v_e_637_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0(lean_object* v_00_u03b2_650_, lean_object* v_x_651_, lean_object* v_x_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg(v_x_651_, v_x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___boxed(lean_object* v_00_u03b2_654_, lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0(v_00_u03b2_654_, v_x_655_, v_x_656_);
lean_dec_ref(v_x_656_);
lean_dec_ref(v_x_655_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_658_, lean_object* v_x_659_, size_t v_x_660_, lean_object* v_x_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg(v_x_659_, v_x_660_, v_x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_663_, lean_object* v_x_664_, lean_object* v_x_665_, lean_object* v_x_666_){
_start:
{
size_t v_x_1026__boxed_667_; lean_object* v_res_668_; 
v_x_1026__boxed_667_ = lean_unbox_usize(v_x_665_);
lean_dec(v_x_665_);
v_res_668_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0(v_00_u03b2_663_, v_x_664_, v_x_1026__boxed_667_, v_x_666_);
lean_dec_ref(v_x_666_);
lean_dec_ref(v_x_664_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_669_, lean_object* v_keys_670_, lean_object* v_vals_671_, lean_object* v_heq_672_, lean_object* v_i_673_, lean_object* v_k_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_670_, v_vals_671_, v_i_673_, v_k_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_676_, lean_object* v_keys_677_, lean_object* v_vals_678_, lean_object* v_heq_679_, lean_object* v_i_680_, lean_object* v_k_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_676_, v_keys_677_, v_vals_678_, v_heq_679_, v_i_680_, v_k_681_);
lean_dec_ref(v_k_681_);
lean_dec_ref(v_vals_678_);
lean_dec_ref(v_keys_677_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_683_, lean_object* v_x_684_, lean_object* v_x_685_, lean_object* v_x_686_){
_start:
{
lean_object* v_ks_687_; lean_object* v_vs_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_714_; 
v_ks_687_ = lean_ctor_get(v_x_683_, 0);
v_vs_688_ = lean_ctor_get(v_x_683_, 1);
v_isSharedCheck_714_ = !lean_is_exclusive(v_x_683_);
if (v_isSharedCheck_714_ == 0)
{
v___x_690_ = v_x_683_;
v_isShared_691_ = v_isSharedCheck_714_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_vs_688_);
lean_inc(v_ks_687_);
lean_dec(v_x_683_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_714_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_692_ = lean_array_get_size(v_ks_687_);
v___x_693_ = lean_nat_dec_lt(v_x_684_, v___x_692_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
lean_dec(v_x_684_);
v___x_694_ = lean_array_push(v_ks_687_, v_x_685_);
v___x_695_ = lean_array_push(v_vs_688_, v_x_686_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v___x_695_);
lean_ctor_set(v___x_690_, 0, v___x_694_);
v___x_697_ = v___x_690_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_694_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
else
{
lean_object* v_k_x27_699_; size_t v___x_700_; size_t v___x_701_; uint8_t v___x_702_; 
v_k_x27_699_ = lean_array_fget_borrowed(v_ks_687_, v_x_684_);
v___x_700_ = lean_ptr_addr(v_x_685_);
v___x_701_ = lean_ptr_addr(v_k_x27_699_);
v___x_702_ = lean_usize_dec_eq(v___x_700_, v___x_701_);
if (v___x_702_ == 0)
{
lean_object* v___x_704_; 
if (v_isShared_691_ == 0)
{
v___x_704_ = v___x_690_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_ks_687_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v_vs_688_);
v___x_704_ = v_reuseFailAlloc_708_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_unsigned_to_nat(1u);
v___x_706_ = lean_nat_add(v_x_684_, v___x_705_);
lean_dec(v_x_684_);
v_x_683_ = v___x_704_;
v_x_684_ = v___x_706_;
goto _start;
}
}
else
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_709_ = lean_array_fset(v_ks_687_, v_x_684_, v_x_685_);
v___x_710_ = lean_array_fset(v_vs_688_, v_x_684_, v_x_686_);
lean_dec(v_x_684_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v___x_710_);
lean_ctor_set(v___x_690_, 0, v___x_709_);
v___x_712_ = v___x_690_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v___x_710_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_715_, lean_object* v_k_716_, lean_object* v_v_717_){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_unsigned_to_nat(0u);
v___x_719_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_715_, v___x_718_, v_k_716_, v_v_717_);
return v___x_719_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(lean_object* v_x_721_, size_t v_x_722_, size_t v_x_723_, lean_object* v_x_724_, lean_object* v_x_725_){
_start:
{
if (lean_obj_tag(v_x_721_) == 0)
{
lean_object* v_es_726_; size_t v___x_727_; size_t v___x_728_; lean_object* v_j_729_; lean_object* v___x_730_; uint8_t v___x_731_; 
v_es_726_ = lean_ctor_get(v_x_721_, 0);
v___x_727_ = ((size_t)31ULL);
v___x_728_ = lean_usize_land(v_x_722_, v___x_727_);
v_j_729_ = lean_usize_to_nat(v___x_728_);
v___x_730_ = lean_array_get_size(v_es_726_);
v___x_731_ = lean_nat_dec_lt(v_j_729_, v___x_730_);
if (v___x_731_ == 0)
{
lean_dec(v_j_729_);
lean_dec(v_x_725_);
lean_dec_ref(v_x_724_);
return v_x_721_;
}
else
{
lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_772_; 
lean_inc_ref(v_es_726_);
v_isSharedCheck_772_ = !lean_is_exclusive(v_x_721_);
if (v_isSharedCheck_772_ == 0)
{
lean_object* v_unused_773_; 
v_unused_773_ = lean_ctor_get(v_x_721_, 0);
lean_dec(v_unused_773_);
v___x_733_ = v_x_721_;
v_isShared_734_ = v_isSharedCheck_772_;
goto v_resetjp_732_;
}
else
{
lean_dec(v_x_721_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_772_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v_v_735_; lean_object* v___x_736_; lean_object* v_xs_x27_737_; lean_object* v___y_739_; 
v_v_735_ = lean_array_fget(v_es_726_, v_j_729_);
v___x_736_ = lean_box(0);
v_xs_x27_737_ = lean_array_fset(v_es_726_, v_j_729_, v___x_736_);
switch(lean_obj_tag(v_v_735_))
{
case 0:
{
lean_object* v_key_744_; lean_object* v_val_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_757_; 
v_key_744_ = lean_ctor_get(v_v_735_, 0);
v_val_745_ = lean_ctor_get(v_v_735_, 1);
v_isSharedCheck_757_ = !lean_is_exclusive(v_v_735_);
if (v_isSharedCheck_757_ == 0)
{
v___x_747_ = v_v_735_;
v_isShared_748_ = v_isSharedCheck_757_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_val_745_);
lean_inc(v_key_744_);
lean_dec(v_v_735_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_757_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
size_t v___x_749_; size_t v___x_750_; uint8_t v___x_751_; 
v___x_749_ = lean_ptr_addr(v_x_724_);
v___x_750_ = lean_ptr_addr(v_key_744_);
v___x_751_ = lean_usize_dec_eq(v___x_749_, v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; 
lean_del_object(v___x_747_);
v___x_752_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_744_, v_val_745_, v_x_724_, v_x_725_);
v___x_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
v___y_739_ = v___x_753_;
goto v___jp_738_;
}
else
{
lean_object* v___x_755_; 
lean_dec(v_val_745_);
lean_dec(v_key_744_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 1, v_x_725_);
lean_ctor_set(v___x_747_, 0, v_x_724_);
v___x_755_ = v___x_747_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_x_724_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_x_725_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
v___y_739_ = v___x_755_;
goto v___jp_738_;
}
}
}
}
case 1:
{
lean_object* v_node_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_770_; 
v_node_758_ = lean_ctor_get(v_v_735_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v_v_735_);
if (v_isSharedCheck_770_ == 0)
{
v___x_760_ = v_v_735_;
v_isShared_761_ = v_isSharedCheck_770_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_node_758_);
lean_dec(v_v_735_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_770_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
size_t v___x_762_; size_t v___x_763_; size_t v___x_764_; size_t v___x_765_; lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_762_ = ((size_t)5ULL);
v___x_763_ = lean_usize_shift_right(v_x_722_, v___x_762_);
v___x_764_ = ((size_t)1ULL);
v___x_765_ = lean_usize_add(v_x_723_, v___x_764_);
v___x_766_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_node_758_, v___x_763_, v___x_765_, v_x_724_, v_x_725_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 0, v___x_766_);
v___x_768_ = v___x_760_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
v___y_739_ = v___x_768_;
goto v___jp_738_;
}
}
}
default: 
{
lean_object* v___x_771_; 
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v_x_724_);
lean_ctor_set(v___x_771_, 1, v_x_725_);
v___y_739_ = v___x_771_;
goto v___jp_738_;
}
}
v___jp_738_:
{
lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_740_ = lean_array_fset(v_xs_x27_737_, v_j_729_, v___y_739_);
lean_dec(v_j_729_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v___x_740_);
v___x_742_ = v___x_733_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
else
{
lean_object* v_ks_774_; lean_object* v_vs_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_793_; 
v_ks_774_ = lean_ctor_get(v_x_721_, 0);
v_vs_775_ = lean_ctor_get(v_x_721_, 1);
v_isSharedCheck_793_ = !lean_is_exclusive(v_x_721_);
if (v_isSharedCheck_793_ == 0)
{
v___x_777_ = v_x_721_;
v_isShared_778_ = v_isSharedCheck_793_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_vs_775_);
lean_inc(v_ks_774_);
lean_dec(v_x_721_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_793_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_ks_774_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_vs_775_);
v___x_780_ = v_reuseFailAlloc_792_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v_newNode_781_; size_t v___x_782_; uint8_t v___x_783_; 
v_newNode_781_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1___redArg(v___x_780_, v_x_724_, v_x_725_);
v___x_782_ = ((size_t)7ULL);
v___x_783_ = lean_usize_dec_le(v___x_782_, v_x_723_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_784_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_781_);
v___x_785_ = lean_unsigned_to_nat(4u);
v___x_786_ = lean_nat_dec_lt(v___x_784_, v___x_785_);
lean_dec(v___x_784_);
if (v___x_786_ == 0)
{
lean_object* v_ks_787_; lean_object* v_vs_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v_ks_787_ = lean_ctor_get(v_newNode_781_, 0);
lean_inc_ref(v_ks_787_);
v_vs_788_ = lean_ctor_get(v_newNode_781_, 1);
lean_inc_ref(v_vs_788_);
lean_dec_ref(v_newNode_781_);
v___x_789_ = lean_unsigned_to_nat(0u);
v___x_790_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___closed__0);
v___x_791_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg(v_x_723_, v_ks_787_, v_vs_788_, v___x_789_, v___x_790_);
lean_dec_ref(v_vs_788_);
lean_dec_ref(v_ks_787_);
return v___x_791_;
}
else
{
return v_newNode_781_;
}
}
else
{
return v_newNode_781_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg(size_t v_depth_794_, lean_object* v_keys_795_, lean_object* v_vals_796_, lean_object* v_i_797_, lean_object* v_entries_798_){
_start:
{
lean_object* v___x_799_; uint8_t v___x_800_; 
v___x_799_ = lean_array_get_size(v_keys_795_);
v___x_800_ = lean_nat_dec_lt(v_i_797_, v___x_799_);
if (v___x_800_ == 0)
{
lean_dec(v_i_797_);
return v_entries_798_;
}
else
{
lean_object* v_k_801_; lean_object* v_v_802_; size_t v___x_803_; size_t v___x_804_; size_t v___x_805_; uint64_t v___x_806_; size_t v_h_807_; size_t v___x_808_; lean_object* v___x_809_; size_t v___x_810_; size_t v___x_811_; size_t v___x_812_; size_t v_h_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v_k_801_ = lean_array_fget_borrowed(v_keys_795_, v_i_797_);
v_v_802_ = lean_array_fget_borrowed(v_vals_796_, v_i_797_);
v___x_803_ = lean_ptr_addr(v_k_801_);
v___x_804_ = ((size_t)3ULL);
v___x_805_ = lean_usize_shift_right(v___x_803_, v___x_804_);
v___x_806_ = lean_usize_to_uint64(v___x_805_);
v_h_807_ = lean_uint64_to_usize(v___x_806_);
v___x_808_ = ((size_t)5ULL);
v___x_809_ = lean_unsigned_to_nat(1u);
v___x_810_ = ((size_t)1ULL);
v___x_811_ = lean_usize_sub(v_depth_794_, v___x_810_);
v___x_812_ = lean_usize_mul(v___x_808_, v___x_811_);
v_h_813_ = lean_usize_shift_right(v_h_807_, v___x_812_);
v___x_814_ = lean_nat_add(v_i_797_, v___x_809_);
lean_dec(v_i_797_);
lean_inc(v_v_802_);
lean_inc(v_k_801_);
v___x_815_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_entries_798_, v_h_813_, v_depth_794_, v_k_801_, v_v_802_);
v_i_797_ = v___x_814_;
v_entries_798_ = v___x_815_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_817_, lean_object* v_keys_818_, lean_object* v_vals_819_, lean_object* v_i_820_, lean_object* v_entries_821_){
_start:
{
size_t v_depth_boxed_822_; lean_object* v_res_823_; 
v_depth_boxed_822_ = lean_unbox_usize(v_depth_817_);
lean_dec(v_depth_817_);
v_res_823_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_822_, v_keys_818_, v_vals_819_, v_i_820_, v_entries_821_);
lean_dec_ref(v_vals_819_);
lean_dec_ref(v_keys_818_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___boxed(lean_object* v_x_824_, lean_object* v_x_825_, lean_object* v_x_826_, lean_object* v_x_827_, lean_object* v_x_828_){
_start:
{
size_t v_x_7502__boxed_829_; size_t v_x_7503__boxed_830_; lean_object* v_res_831_; 
v_x_7502__boxed_829_ = lean_unbox_usize(v_x_825_);
lean_dec(v_x_825_);
v_x_7503__boxed_830_ = lean_unbox_usize(v_x_826_);
lean_dec(v_x_826_);
v_res_831_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_x_824_, v_x_7502__boxed_829_, v_x_7503__boxed_830_, v_x_827_, v_x_828_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0___redArg(lean_object* v_x_832_, lean_object* v_x_833_, lean_object* v_x_834_){
_start:
{
size_t v___x_835_; size_t v___x_836_; size_t v___x_837_; uint64_t v___x_838_; size_t v___x_839_; size_t v___x_840_; lean_object* v___x_841_; 
v___x_835_ = lean_ptr_addr(v_x_833_);
v___x_836_ = ((size_t)3ULL);
v___x_837_ = lean_usize_shift_right(v___x_835_, v___x_836_);
v___x_838_ = lean_usize_to_uint64(v___x_837_);
v___x_839_ = lean_uint64_to_usize(v___x_838_);
v___x_840_ = ((size_t)1ULL);
v___x_841_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_x_832_, v___x_839_, v___x_840_, v_x_833_, v_x_834_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___lam__0(lean_object* v_e_842_, lean_object* v_ringId_843_, lean_object* v_s_844_){
_start:
{
lean_object* v_rings_845_; lean_object* v_exprToRingId_846_; lean_object* v_semirings_847_; lean_object* v_exprToSemiringId_848_; lean_object* v_ncRings_849_; lean_object* v_exprToNCRingId_850_; lean_object* v_ncSemirings_851_; lean_object* v_exprToNCSemiringId_852_; lean_object* v_steps_853_; uint8_t v_reportedMaxDegreeIssue_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_862_; 
v_rings_845_ = lean_ctor_get(v_s_844_, 0);
v_exprToRingId_846_ = lean_ctor_get(v_s_844_, 1);
v_semirings_847_ = lean_ctor_get(v_s_844_, 2);
v_exprToSemiringId_848_ = lean_ctor_get(v_s_844_, 3);
v_ncRings_849_ = lean_ctor_get(v_s_844_, 4);
v_exprToNCRingId_850_ = lean_ctor_get(v_s_844_, 5);
v_ncSemirings_851_ = lean_ctor_get(v_s_844_, 6);
v_exprToNCSemiringId_852_ = lean_ctor_get(v_s_844_, 7);
v_steps_853_ = lean_ctor_get(v_s_844_, 8);
v_reportedMaxDegreeIssue_854_ = lean_ctor_get_uint8(v_s_844_, sizeof(void*)*9);
v_isSharedCheck_862_ = !lean_is_exclusive(v_s_844_);
if (v_isSharedCheck_862_ == 0)
{
v___x_856_ = v_s_844_;
v_isShared_857_ = v_isSharedCheck_862_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_steps_853_);
lean_inc(v_exprToNCSemiringId_852_);
lean_inc(v_ncSemirings_851_);
lean_inc(v_exprToNCRingId_850_);
lean_inc(v_ncRings_849_);
lean_inc(v_exprToSemiringId_848_);
lean_inc(v_semirings_847_);
lean_inc(v_exprToRingId_846_);
lean_inc(v_rings_845_);
lean_dec(v_s_844_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_862_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_858_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0___redArg(v_exprToNCRingId_850_, v_e_842_, v_ringId_843_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 5, v___x_858_);
v___x_860_ = v___x_856_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_rings_845_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_exprToRingId_846_);
lean_ctor_set(v_reuseFailAlloc_861_, 2, v_semirings_847_);
lean_ctor_set(v_reuseFailAlloc_861_, 3, v_exprToSemiringId_848_);
lean_ctor_set(v_reuseFailAlloc_861_, 4, v_ncRings_849_);
lean_ctor_set(v_reuseFailAlloc_861_, 5, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_861_, 6, v_ncSemirings_851_);
lean_ctor_set(v_reuseFailAlloc_861_, 7, v_exprToNCSemiringId_852_);
lean_ctor_set(v_reuseFailAlloc_861_, 8, v_steps_853_);
lean_ctor_set_uint8(v_reuseFailAlloc_861_, sizeof(void*)*9, v_reportedMaxDegreeIssue_854_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__1(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__0));
v___x_865_ = l_Lean_stringToMessageData(v___x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(lean_object* v_e_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v_ringId_879_; lean_object* v___f_880_; lean_object* v___x_881_; 
v_ringId_879_ = lean_ctor_get(v_a_867_, 0);
lean_inc(v_ringId_879_);
lean_inc_ref(v_e_866_);
v___f_880_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_880_, 0, v_e_866_);
lean_closure_set(v___f_880_, 1, v_ringId_879_);
v___x_881_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg(v_e_866_, v_a_868_, v_a_873_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
lean_dec_ref_known(v___x_881_, 1);
if (lean_obj_tag(v_a_882_) == 1)
{
lean_object* v_val_883_; uint8_t v___x_884_; 
lean_dec_ref(v___f_880_);
v_val_883_ = lean_ctor_get(v_a_882_, 0);
lean_inc(v_val_883_);
lean_dec_ref_known(v_a_882_, 1);
v___x_884_ = lean_nat_dec_eq(v_val_883_, v_ringId_879_);
lean_dec(v_val_883_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_885_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__1);
v___x_886_ = l_Lean_indentExpr(v_e_866_);
v___x_887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_885_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_869_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; uint8_t v_verbose_890_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_889_);
lean_dec_ref_known(v___x_888_, 1);
v_verbose_890_ = lean_ctor_get_uint8(v_a_889_, 0);
lean_dec(v_a_889_);
if (v_verbose_890_ == 0)
{
lean_dec_ref_known(v___x_887_, 2);
goto v___jp_876_;
}
else
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_Meta_Sym_reportIssue(v___x_887_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_dec_ref_known(v___x_891_, 1);
goto v___jp_876_;
}
else
{
return v___x_891_;
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_dec_ref_known(v___x_887_, 2);
v_a_892_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_888_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_888_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
else
{
lean_dec_ref(v_e_866_);
goto v___jp_876_;
}
}
else
{
lean_object* v___x_900_; lean_object* v___x_901_; 
lean_dec(v_a_882_);
lean_dec_ref(v_e_866_);
v___x_900_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_901_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_900_, v___f_880_, v_a_868_);
return v___x_901_;
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec_ref(v___f_880_);
lean_dec_ref(v_e_866_);
v_a_902_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_881_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_881_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
v___jp_876_:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = lean_box(0);
v___x_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
return v___x_878_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___boxed(lean_object* v_e_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(v_e_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId(lean_object* v_e_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(v_e_921_, v_a_922_, v_a_923_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___boxed(lean_object* v_e_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId(v_e_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec(v_a_937_);
lean_dec_ref(v_a_936_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0(lean_object* v_00_u03b2_949_, lean_object* v_x_950_, lean_object* v_x_951_, lean_object* v_x_952_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0___redArg(v_x_950_, v_x_951_, v_x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0(lean_object* v_00_u03b2_954_, lean_object* v_x_955_, size_t v_x_956_, size_t v_x_957_, lean_object* v_x_958_, lean_object* v_x_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_x_955_, v_x_956_, v_x_957_, v_x_958_, v_x_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_961_, lean_object* v_x_962_, lean_object* v_x_963_, lean_object* v_x_964_, lean_object* v_x_965_, lean_object* v_x_966_){
_start:
{
size_t v_x_7788__boxed_967_; size_t v_x_7789__boxed_968_; lean_object* v_res_969_; 
v_x_7788__boxed_967_ = lean_unbox_usize(v_x_963_);
lean_dec(v_x_963_);
v_x_7789__boxed_968_ = lean_unbox_usize(v_x_964_);
lean_dec(v_x_964_);
v_res_969_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0(v_00_u03b2_961_, v_x_962_, v_x_7788__boxed_967_, v_x_7789__boxed_968_, v_x_965_, v_x_966_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_970_, lean_object* v_n_971_, lean_object* v_k_972_, lean_object* v_v_973_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1___redArg(v_n_971_, v_k_972_, v_v_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_975_, size_t v_depth_976_, lean_object* v_keys_977_, lean_object* v_vals_978_, lean_object* v_heq_979_, lean_object* v_i_980_, lean_object* v_entries_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg(v_depth_976_, v_keys_977_, v_vals_978_, v_i_980_, v_entries_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_983_, lean_object* v_depth_984_, lean_object* v_keys_985_, lean_object* v_vals_986_, lean_object* v_heq_987_, lean_object* v_i_988_, lean_object* v_entries_989_){
_start:
{
size_t v_depth_boxed_990_; lean_object* v_res_991_; 
v_depth_boxed_990_ = lean_unbox_usize(v_depth_984_);
lean_dec(v_depth_984_);
v_res_991_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2(v_00_u03b2_983_, v_depth_boxed_990_, v_keys_985_, v_vals_986_, v_heq_987_, v_i_988_, v_entries_989_);
lean_dec_ref(v_vals_986_);
lean_dec_ref(v_keys_985_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_992_, lean_object* v_x_993_, lean_object* v_x_994_, lean_object* v_x_995_, lean_object* v_x_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_993_, v_x_994_, v_x_995_, v_x_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___lam__0(lean_object* v_e_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(v_e_998_, v___y_999_, v___y_1000_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___lam__0___boxed(lean_object* v_e_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___lam__0(v_e_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0(lean_object* v___f_1028_, lean_object* v___x_1029_, lean_object* v___x_1030_, lean_object* v___f_1031_, lean_object* v_e_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_1032_, v___y_1034_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; uint8_t v___x_1047_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v___x_1045_, 1);
v___x_1047_ = lean_unbox(v_a_1046_);
lean_dec(v_a_1046_);
if (v___x_1047_ == 0)
{
lean_object* v_gen_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v_gen_1048_ = lean_ctor_get(v___y_1033_, 1);
v___x_1049_ = lean_box(0);
lean_inc(v___y_1043_);
lean_inc_ref(v___y_1042_);
lean_inc(v___y_1041_);
lean_inc_ref(v___y_1040_);
lean_inc(v___y_1039_);
lean_inc_ref(v___y_1038_);
lean_inc(v___y_1037_);
lean_inc_ref(v___y_1036_);
lean_inc(v___y_1035_);
lean_inc(v___y_1034_);
lean_inc(v_gen_1048_);
lean_inc_ref(v_e_1032_);
v___x_1050_ = lean_grind_internalize(v_e_1032_, v_gen_1048_, v___x_1049_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v___x_3333__overap_1051_; lean_object* v___x_1052_; 
lean_dec_ref_known(v___x_1050_, 1);
v___x_3333__overap_1051_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v___f_1028_, v___x_1029_, v___x_1030_, v___f_1031_, v_e_1032_);
lean_inc(v___y_1043_);
lean_inc_ref(v___y_1042_);
lean_inc(v___y_1041_);
lean_inc_ref(v___y_1040_);
lean_inc(v___y_1039_);
lean_inc_ref(v___y_1038_);
lean_inc(v___y_1037_);
lean_inc_ref(v___y_1036_);
lean_inc(v___y_1035_);
lean_inc(v___y_1034_);
lean_inc_ref(v___y_1033_);
v___x_1052_ = lean_apply_12(v___x_3333__overap_1051_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, lean_box(0));
return v___x_1052_;
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_dec_ref(v_e_1032_);
lean_dec_ref(v___f_1031_);
lean_dec_ref(v___x_1030_);
lean_dec_ref(v___x_1029_);
lean_dec(v___f_1028_);
v_a_1053_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1050_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1050_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
else
{
lean_object* v___x_3337__overap_1061_; lean_object* v___x_1062_; 
v___x_3337__overap_1061_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v___f_1028_, v___x_1029_, v___x_1030_, v___f_1031_, v_e_1032_);
lean_inc(v___y_1043_);
lean_inc_ref(v___y_1042_);
lean_inc(v___y_1041_);
lean_inc_ref(v___y_1040_);
lean_inc(v___y_1039_);
lean_inc_ref(v___y_1038_);
lean_inc(v___y_1037_);
lean_inc_ref(v___y_1036_);
lean_inc(v___y_1035_);
lean_inc(v___y_1034_);
lean_inc_ref(v___y_1033_);
v___x_1062_ = lean_apply_12(v___x_3337__overap_1061_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, lean_box(0));
return v___x_1062_;
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_dec_ref(v_e_1032_);
lean_dec_ref(v___f_1031_);
lean_dec_ref(v___x_1030_);
lean_dec_ref(v___x_1029_);
lean_dec(v___f_1028_);
v_a_1063_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1045_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1045_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0___boxed(lean_object** _args){
lean_object* v___f_1071_ = _args[0];
lean_object* v___x_1072_ = _args[1];
lean_object* v___x_1073_ = _args[2];
lean_object* v___f_1074_ = _args[3];
lean_object* v_e_1075_ = _args[4];
lean_object* v___y_1076_ = _args[5];
lean_object* v___y_1077_ = _args[6];
lean_object* v___y_1078_ = _args[7];
lean_object* v___y_1079_ = _args[8];
lean_object* v___y_1080_ = _args[9];
lean_object* v___y_1081_ = _args[10];
lean_object* v___y_1082_ = _args[11];
lean_object* v___y_1083_ = _args[12];
lean_object* v___y_1084_ = _args[13];
lean_object* v___y_1085_ = _args[14];
lean_object* v___y_1086_ = _args[15];
lean_object* v___y_1087_ = _args[16];
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0(v___f_1071_, v___x_1072_, v___x_1073_, v___f_1074_, v_e_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
return v_res_1088_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__0(void){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_instMonadEIO___redArg();
return v___x_1089_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__1(void){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__0);
v___x_1091_ = l_StateRefT_x27_instMonad___redArg(v___x_1090_);
return v___x_1091_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM(void){
_start:
{
lean_object* v___x_1101_; lean_object* v_toApplicative_1102_; lean_object* v_toFunctor_1103_; lean_object* v_toSeq_1104_; lean_object* v_toSeqLeft_1105_; lean_object* v_toSeqRight_1106_; lean_object* v___f_1107_; lean_object* v___f_1108_; lean_object* v___f_1109_; lean_object* v___f_1110_; lean_object* v___x_1111_; lean_object* v___f_1112_; lean_object* v___f_1113_; lean_object* v___f_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v_toApplicative_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1156_; 
v___x_1101_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__1);
v_toApplicative_1102_ = lean_ctor_get(v___x_1101_, 0);
v_toFunctor_1103_ = lean_ctor_get(v_toApplicative_1102_, 0);
v_toSeq_1104_ = lean_ctor_get(v_toApplicative_1102_, 2);
v_toSeqLeft_1105_ = lean_ctor_get(v_toApplicative_1102_, 3);
v_toSeqRight_1106_ = lean_ctor_get(v_toApplicative_1102_, 4);
v___f_1107_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__2));
v___f_1108_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__3));
lean_inc_ref_n(v_toFunctor_1103_, 2);
v___f_1109_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1109_, 0, v_toFunctor_1103_);
v___f_1110_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1110_, 0, v_toFunctor_1103_);
v___x_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___f_1109_);
lean_ctor_set(v___x_1111_, 1, v___f_1110_);
lean_inc(v_toSeqRight_1106_);
v___f_1112_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1112_, 0, v_toSeqRight_1106_);
lean_inc(v_toSeqLeft_1105_);
v___f_1113_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1113_, 0, v_toSeqLeft_1105_);
lean_inc(v_toSeq_1104_);
v___f_1114_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1114_, 0, v_toSeq_1104_);
v___x_1115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1111_);
lean_ctor_set(v___x_1115_, 1, v___f_1107_);
lean_ctor_set(v___x_1115_, 2, v___f_1114_);
lean_ctor_set(v___x_1115_, 3, v___f_1113_);
lean_ctor_set(v___x_1115_, 4, v___f_1112_);
v___x_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
lean_ctor_set(v___x_1116_, 1, v___f_1108_);
v___x_1117_ = l_StateRefT_x27_instMonad___redArg(v___x_1116_);
v_toApplicative_1118_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1156_ == 0)
{
lean_object* v_unused_1157_; 
v_unused_1157_ = lean_ctor_get(v___x_1117_, 1);
lean_dec(v_unused_1157_);
v___x_1120_ = v___x_1117_;
v_isShared_1121_ = v_isSharedCheck_1156_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_toApplicative_1118_);
lean_dec(v___x_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1156_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v_toFunctor_1122_; lean_object* v_toSeq_1123_; lean_object* v_toSeqLeft_1124_; lean_object* v_toSeqRight_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1154_; 
v_toFunctor_1122_ = lean_ctor_get(v_toApplicative_1118_, 0);
v_toSeq_1123_ = lean_ctor_get(v_toApplicative_1118_, 2);
v_toSeqLeft_1124_ = lean_ctor_get(v_toApplicative_1118_, 3);
v_toSeqRight_1125_ = lean_ctor_get(v_toApplicative_1118_, 4);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_toApplicative_1118_);
if (v_isSharedCheck_1154_ == 0)
{
lean_object* v_unused_1155_; 
v_unused_1155_ = lean_ctor_get(v_toApplicative_1118_, 1);
lean_dec(v_unused_1155_);
v___x_1127_ = v_toApplicative_1118_;
v_isShared_1128_ = v_isSharedCheck_1154_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_toSeqRight_1125_);
lean_inc(v_toSeqLeft_1124_);
lean_inc(v_toSeq_1123_);
lean_inc(v_toFunctor_1122_);
lean_dec(v_toApplicative_1118_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1154_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___f_1129_; lean_object* v___f_1130_; lean_object* v___f_1131_; lean_object* v___f_1132_; lean_object* v___x_1133_; lean_object* v___f_1134_; lean_object* v___f_1135_; lean_object* v___f_1136_; lean_object* v___x_1138_; 
v___f_1129_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__4));
v___f_1130_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__5));
lean_inc_ref(v_toFunctor_1122_);
v___f_1131_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1131_, 0, v_toFunctor_1122_);
v___f_1132_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1132_, 0, v_toFunctor_1122_);
v___x_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___f_1131_);
lean_ctor_set(v___x_1133_, 1, v___f_1132_);
v___f_1134_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1134_, 0, v_toSeqRight_1125_);
v___f_1135_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1135_, 0, v_toSeqLeft_1124_);
v___f_1136_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1136_, 0, v_toSeq_1123_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 4, v___f_1134_);
lean_ctor_set(v___x_1127_, 3, v___f_1135_);
lean_ctor_set(v___x_1127_, 2, v___f_1136_);
lean_ctor_set(v___x_1127_, 1, v___f_1129_);
lean_ctor_set(v___x_1127_, 0, v___x_1133_);
v___x_1138_ = v___x_1127_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1133_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v___f_1129_);
lean_ctor_set(v_reuseFailAlloc_1153_, 2, v___f_1136_);
lean_ctor_set(v_reuseFailAlloc_1153_, 3, v___f_1135_);
lean_ctor_set(v_reuseFailAlloc_1153_, 4, v___f_1134_);
v___x_1138_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1140_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 1, v___f_1130_);
lean_ctor_set(v___x_1120_, 0, v___x_1138_);
v___x_1140_ = v___x_1120_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v___f_1130_);
v___x_1140_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___f_1148_; lean_object* v___x_1149_; lean_object* v___f_1150_; lean_object* v___f_1151_; 
v___x_1141_ = l_StateRefT_x27_instMonad___redArg(v___x_1140_);
v___x_1142_ = l_ReaderT_instMonad___redArg(v___x_1141_);
v___x_1143_ = l_StateRefT_x27_instMonad___redArg(v___x_1142_);
v___x_1144_ = l_ReaderT_instMonad___redArg(v___x_1143_);
v___x_1145_ = l_ReaderT_instMonad___redArg(v___x_1144_);
v___x_1146_ = l_StateRefT_x27_instMonad___redArg(v___x_1145_);
v___x_1147_ = l_ReaderT_instMonad___redArg(v___x_1146_);
v___f_1148_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___closed__8));
v___x_1149_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateNonCommRingM;
v___f_1150_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___closed__0));
v___f_1151_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarNonCommRingM___lam__0___boxed), 17, 4);
lean_closure_set(v___f_1151_, 0, v___f_1148_);
lean_closure_set(v___f_1151_, 1, v___x_1147_);
lean_closure_set(v___f_1151_, 2, v___x_1149_);
lean_closure_set(v___f_1151_, 3, v___f_1150_);
return v___f_1151_;
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
