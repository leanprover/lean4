// Lean compiler output
// Module: Lean.Meta.Tactic.Generalize
// Imports: public import Lean.Meta.KAbstract public import Lean.Meta.Tactic.Intro public import Lean.Meta.Tactic.FVarSubst public import Lean.Meta.Tactic.Revert import Lean.Meta.AppBuilder
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(lean_object*, size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__0;
uint8_t lean_usize_dec_le(size_t, size_t);
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__1;
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__2;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_generalize(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
static lean_object* l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__3;
lean_object* l_Lean_Meta_mkHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__0;
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(uint8_t, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1;
static lean_object* l_Lean_MVarId_generalizeHyp___closed__0;
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_generalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedGeneralizeArg_default;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__1;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__0;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedGeneralizeArg;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* _init_l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__2;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedGeneralizeArg_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedGeneralizeArg() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedGeneralizeArg_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
x_14 = lean_st_ref_set(x_2, x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 3);
x_19 = lean_ctor_get(x_11, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_st_ref_set(x_2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("x", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_nat_dec_lt(x_4, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_fget_borrowed(x_1, x_4);
x_14 = lean_ctor_get(x_13, 0);
x_15 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_14);
x_16 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(x_14, x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_17);
x_18 = lean_infer_type(x_17, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(x_19, x_6);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_4, x_22);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_24 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(x_1, x_2, x_3, x_23, x_5, x_6, x_7, x_8);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_15, 0);
lean_inc(x_129);
x_26 = x_129;
x_27 = x_5;
x_28 = x_6;
x_29 = x_7;
x_30 = x_8;
x_31 = lean_box(0);
goto block_128;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__1;
lean_inc(x_8);
lean_inc_ref(x_7);
x_131 = l_Lean_Core_mkFreshUserName(x_130, x_7, x_8);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec_ref(x_131);
x_26 = x_132;
x_27 = x_5;
x_28 = x_6;
x_29 = x_7;
x_30 = x_8;
x_31 = lean_box(0);
goto block_128;
}
else
{
uint8_t x_133; 
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_133 = !lean_is_exclusive(x_131);
if (x_133 == 0)
{
return x_131;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_131, 0);
lean_inc(x_134);
lean_dec(x_131);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
}
}
block_128:
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Meta_Context_config(x_27);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint64_t x_44; uint8_t x_45; 
x_34 = lean_ctor_get_uint8(x_27, sizeof(void*)*7);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_27, 2);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_27, 3);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_27, 4);
lean_inc(x_38);
x_39 = lean_ctor_get(x_27, 5);
lean_inc(x_39);
x_40 = lean_ctor_get(x_27, 6);
lean_inc(x_40);
x_41 = lean_ctor_get_uint8(x_27, sizeof(void*)*7 + 1);
x_42 = lean_ctor_get_uint8(x_27, sizeof(void*)*7 + 2);
x_43 = lean_ctor_get_uint8(x_27, sizeof(void*)*7 + 3);
lean_ctor_set_uint8(x_32, 9, x_2);
x_44 = l_Lean_Meta_Context_configKey(x_27);
x_45 = !lean_is_exclusive(x_27);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint64_t x_53; uint64_t x_54; lean_object* x_55; uint64_t x_56; uint64_t x_57; uint64_t x_58; lean_object* x_59; lean_object* x_60; 
x_46 = lean_ctor_get(x_27, 6);
lean_dec(x_46);
x_47 = lean_ctor_get(x_27, 5);
lean_dec(x_47);
x_48 = lean_ctor_get(x_27, 4);
lean_dec(x_48);
x_49 = lean_ctor_get(x_27, 3);
lean_dec(x_49);
x_50 = lean_ctor_get(x_27, 2);
lean_dec(x_50);
x_51 = lean_ctor_get(x_27, 1);
lean_dec(x_51);
x_52 = lean_ctor_get(x_27, 0);
lean_dec(x_52);
x_53 = 2;
x_54 = lean_uint64_shift_right(x_44, x_53);
x_55 = lean_box(0);
x_56 = lean_uint64_shift_left(x_54, x_53);
x_57 = l_Lean_Meta_TransparencyMode_toUInt64(x_2);
x_58 = lean_uint64_lor(x_56, x_57);
x_59 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_59, 0, x_32);
lean_ctor_set_uint64(x_59, sizeof(void*)*1, x_58);
lean_ctor_set(x_27, 0, x_59);
x_60 = l_Lean_Meta_kabstract(x_25, x_17, x_55, x_27, x_28, x_29, x_30);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = 0;
x_64 = l_Lean_mkForall(x_26, x_63, x_21, x_62);
lean_ctor_set(x_60, 0, x_64);
return x_60;
}
else
{
lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
lean_dec(x_60);
x_66 = 0;
x_67 = l_Lean_mkForall(x_26, x_66, x_21, x_65);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
else
{
lean_dec(x_26);
lean_dec(x_21);
return x_60;
}
}
else
{
uint64_t x_69; uint64_t x_70; lean_object* x_71; uint64_t x_72; uint64_t x_73; uint64_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_27);
x_69 = 2;
x_70 = lean_uint64_shift_right(x_44, x_69);
x_71 = lean_box(0);
x_72 = lean_uint64_shift_left(x_70, x_69);
x_73 = l_Lean_Meta_TransparencyMode_toUInt64(x_2);
x_74 = lean_uint64_lor(x_72, x_73);
x_75 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_75, 0, x_32);
lean_ctor_set_uint64(x_75, sizeof(void*)*1, x_74);
x_76 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_35);
lean_ctor_set(x_76, 2, x_36);
lean_ctor_set(x_76, 3, x_37);
lean_ctor_set(x_76, 4, x_38);
lean_ctor_set(x_76, 5, x_39);
lean_ctor_set(x_76, 6, x_40);
lean_ctor_set_uint8(x_76, sizeof(void*)*7, x_34);
lean_ctor_set_uint8(x_76, sizeof(void*)*7 + 1, x_41);
lean_ctor_set_uint8(x_76, sizeof(void*)*7 + 2, x_42);
lean_ctor_set_uint8(x_76, sizeof(void*)*7 + 3, x_43);
x_77 = l_Lean_Meta_kabstract(x_25, x_17, x_71, x_76, x_28, x_29, x_30);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
x_80 = 0;
x_81 = l_Lean_mkForall(x_26, x_80, x_21, x_78);
if (lean_is_scalar(x_79)) {
 x_82 = lean_alloc_ctor(0, 1, 0);
} else {
 x_82 = x_79;
}
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
else
{
lean_dec(x_26);
lean_dec(x_21);
return x_77;
}
}
}
else
{
uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; lean_object* x_111; uint64_t x_112; lean_object* x_113; uint64_t x_114; uint64_t x_115; lean_object* x_116; uint64_t x_117; uint64_t x_118; uint64_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_83 = lean_ctor_get_uint8(x_32, 0);
x_84 = lean_ctor_get_uint8(x_32, 1);
x_85 = lean_ctor_get_uint8(x_32, 2);
x_86 = lean_ctor_get_uint8(x_32, 3);
x_87 = lean_ctor_get_uint8(x_32, 4);
x_88 = lean_ctor_get_uint8(x_32, 5);
x_89 = lean_ctor_get_uint8(x_32, 6);
x_90 = lean_ctor_get_uint8(x_32, 7);
x_91 = lean_ctor_get_uint8(x_32, 8);
x_92 = lean_ctor_get_uint8(x_32, 10);
x_93 = lean_ctor_get_uint8(x_32, 11);
x_94 = lean_ctor_get_uint8(x_32, 12);
x_95 = lean_ctor_get_uint8(x_32, 13);
x_96 = lean_ctor_get_uint8(x_32, 14);
x_97 = lean_ctor_get_uint8(x_32, 15);
x_98 = lean_ctor_get_uint8(x_32, 16);
x_99 = lean_ctor_get_uint8(x_32, 17);
x_100 = lean_ctor_get_uint8(x_32, 18);
lean_dec(x_32);
x_101 = lean_ctor_get_uint8(x_27, sizeof(void*)*7);
x_102 = lean_ctor_get(x_27, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_27, 2);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_27, 3);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_27, 4);
lean_inc(x_105);
x_106 = lean_ctor_get(x_27, 5);
lean_inc(x_106);
x_107 = lean_ctor_get(x_27, 6);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_27, sizeof(void*)*7 + 1);
x_109 = lean_ctor_get_uint8(x_27, sizeof(void*)*7 + 2);
x_110 = lean_ctor_get_uint8(x_27, sizeof(void*)*7 + 3);
x_111 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_111, 0, x_83);
lean_ctor_set_uint8(x_111, 1, x_84);
lean_ctor_set_uint8(x_111, 2, x_85);
lean_ctor_set_uint8(x_111, 3, x_86);
lean_ctor_set_uint8(x_111, 4, x_87);
lean_ctor_set_uint8(x_111, 5, x_88);
lean_ctor_set_uint8(x_111, 6, x_89);
lean_ctor_set_uint8(x_111, 7, x_90);
lean_ctor_set_uint8(x_111, 8, x_91);
lean_ctor_set_uint8(x_111, 9, x_2);
lean_ctor_set_uint8(x_111, 10, x_92);
lean_ctor_set_uint8(x_111, 11, x_93);
lean_ctor_set_uint8(x_111, 12, x_94);
lean_ctor_set_uint8(x_111, 13, x_95);
lean_ctor_set_uint8(x_111, 14, x_96);
lean_ctor_set_uint8(x_111, 15, x_97);
lean_ctor_set_uint8(x_111, 16, x_98);
lean_ctor_set_uint8(x_111, 17, x_99);
lean_ctor_set_uint8(x_111, 18, x_100);
x_112 = l_Lean_Meta_Context_configKey(x_27);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 lean_ctor_release(x_27, 3);
 lean_ctor_release(x_27, 4);
 lean_ctor_release(x_27, 5);
 lean_ctor_release(x_27, 6);
 x_113 = x_27;
} else {
 lean_dec_ref(x_27);
 x_113 = lean_box(0);
}
x_114 = 2;
x_115 = lean_uint64_shift_right(x_112, x_114);
x_116 = lean_box(0);
x_117 = lean_uint64_shift_left(x_115, x_114);
x_118 = l_Lean_Meta_TransparencyMode_toUInt64(x_2);
x_119 = lean_uint64_lor(x_117, x_118);
x_120 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_120, 0, x_111);
lean_ctor_set_uint64(x_120, sizeof(void*)*1, x_119);
if (lean_is_scalar(x_113)) {
 x_121 = lean_alloc_ctor(0, 7, 4);
} else {
 x_121 = x_113;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_102);
lean_ctor_set(x_121, 2, x_103);
lean_ctor_set(x_121, 3, x_104);
lean_ctor_set(x_121, 4, x_105);
lean_ctor_set(x_121, 5, x_106);
lean_ctor_set(x_121, 6, x_107);
lean_ctor_set_uint8(x_121, sizeof(void*)*7, x_101);
lean_ctor_set_uint8(x_121, sizeof(void*)*7 + 1, x_108);
lean_ctor_set_uint8(x_121, sizeof(void*)*7 + 2, x_109);
lean_ctor_set_uint8(x_121, sizeof(void*)*7 + 3, x_110);
x_122 = l_Lean_Meta_kabstract(x_25, x_17, x_116, x_121, x_28, x_29, x_30);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 x_124 = x_122;
} else {
 lean_dec_ref(x_122);
 x_124 = lean_box(0);
}
x_125 = 0;
x_126 = l_Lean_mkForall(x_26, x_125, x_21, x_123);
if (lean_is_scalar(x_124)) {
 x_127 = lean_alloc_ctor(0, 1, 0);
} else {
 x_127 = x_124;
}
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
else
{
lean_dec(x_26);
lean_dec(x_21);
return x_122;
}
}
}
}
else
{
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_24;
}
}
else
{
lean_dec(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_20;
}
}
else
{
lean_dec(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_18;
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_4, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_Meta_instInhabitedGeneralizeArg_default;
x_16 = lean_array_get_borrowed(x_15, x_1, x_4);
x_17 = lean_ctor_get(x_16, 2);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_54; lean_object* x_55; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_17, 0);
x_54 = lean_array_fget_borrowed(x_2, x_4);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_54);
x_55 = lean_infer_type(x_54, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
lean_inc_ref(x_18);
x_57 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(x_18, x_6);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_58);
x_59 = lean_infer_type(x_58, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(x_60, x_6);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_63 = l_Lean_Meta_isExprDefEq(x_56, x_62, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_54);
lean_inc(x_58);
x_66 = l_Lean_Meta_mkHEq(x_58, x_54, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_68 = l_Lean_Meta_mkHEqRefl(x_58, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
x_20 = x_67;
x_21 = x_69;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = x_8;
x_26 = lean_box(0);
goto block_53;
}
else
{
uint8_t x_70; 
lean_dec(x_67);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_70 = !lean_is_exclusive(x_68);
if (x_70 == 0)
{
return x_68;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_68, 0);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_58);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_73 = !lean_is_exclusive(x_66);
if (x_73 == 0)
{
return x_66;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_66, 0);
lean_inc(x_74);
lean_dec(x_66);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_54);
lean_inc(x_58);
x_76 = l_Lean_Meta_mkEq(x_58, x_54, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_78 = l_Lean_Meta_mkEqRefl(x_58, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
x_20 = x_77;
x_21 = x_79;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = x_8;
x_26 = lean_box(0);
goto block_53;
}
else
{
uint8_t x_80; 
lean_dec(x_77);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_80 = !lean_is_exclusive(x_78);
if (x_80 == 0)
{
return x_78;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
lean_dec(x_78);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_58);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_83 = !lean_is_exclusive(x_76);
if (x_83 == 0)
{
return x_76;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_76, 0);
lean_inc(x_84);
lean_dec(x_76);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_58);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_86 = !lean_is_exclusive(x_63);
if (x_86 == 0)
{
return x_63;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_63, 0);
lean_inc(x_87);
lean_dec(x_63);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_89 = !lean_is_exclusive(x_61);
if (x_89 == 0)
{
return x_61;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_61, 0);
lean_inc(x_90);
lean_dec(x_61);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_92 = !lean_is_exclusive(x_59);
if (x_92 == 0)
{
return x_59;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_59, 0);
lean_inc(x_93);
lean_dec(x_59);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_56);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_95 = !lean_is_exclusive(x_57);
if (x_95 == 0)
{
return x_57;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_57, 0);
lean_inc(x_96);
lean_dec(x_57);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_98 = !lean_is_exclusive(x_55);
if (x_98 == 0)
{
return x_55;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_55, 0);
lean_inc(x_99);
lean_dec(x_55);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
}
block_53:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_4, x_27);
lean_dec(x_4);
x_29 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(x_1, x_2, x_3, x_28, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set(x_35, 1, x_33);
x_36 = 0;
lean_inc(x_19);
x_37 = l_Lean_mkForall(x_19, x_36, x_20, x_34);
lean_ctor_set(x_31, 1, x_37);
lean_ctor_set(x_31, 0, x_35);
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_31, 0);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_31);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_21);
lean_ctor_set(x_40, 1, x_38);
x_41 = 0;
lean_inc(x_19);
x_42 = l_Lean_mkForall(x_19, x_41, x_20, x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_29, 0, x_43);
return x_29;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_29, 0);
lean_inc(x_44);
lean_dec(x_29);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_47 = x_44;
} else {
 lean_dec_ref(x_44);
 x_47 = lean_box(0);
}
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_21);
lean_ctor_set(x_48, 1, x_45);
x_49 = 0;
lean_inc(x_19);
x_50 = l_Lean_mkForall(x_19, x_49, x_20, x_46);
if (lean_is_scalar(x_47)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_47;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
else
{
lean_dec_ref(x_21);
lean_dec_ref(x_20);
return x_29;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_unsigned_to_nat(1u);
x_102 = lean_nat_add(x_4, x_101);
lean_dec(x_4);
x_4 = x_102;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_11, 0, x_3);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_5);
x_13 = lean_unbox(x_6);
x_14 = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3(x_1, x_2, x_3, x_4, x_12, x_13, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_12 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(x_1, x_5, x_6, x_2, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = 1;
x_18 = l_Lean_Meta_mkForallFVars(x_5, x_16, x_3, x_4, x_4, x_17, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_ctor_set(x_13, 1, x_20);
lean_ctor_set(x_18, 0, x_13);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
lean_ctor_set(x_13, 1, x_21);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_13);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_free_object(x_13);
lean_dec(x_15);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_28 = 1;
x_29 = l_Lean_Meta_mkForallFVars(x_5, x_27, x_3, x_4, x_4, x_28, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_30);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 1, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_26);
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 x_35 = x_29;
} else {
 lean_dec_ref(x_29);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 1, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_34);
return x_36;
}
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
x_13 = lean_unbox(x_4);
x_14 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = 1;
if (lean_obj_tag(x_6) == 0)
{
if (x_4 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
goto _start;
}
else
{
return x_7;
}
}
else
{
lean_dec_ref(x_6);
return x_7;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(x_1, x_4, x_5);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_array_push(x_6, x_3);
x_11 = lean_array_push(x_7, x_4);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_fget_borrowed(x_6, x_2);
x_13 = l_Lean_instBEqMVarId_beq(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fset(x_6, x_2, x_3);
x_18 = lean_array_fset(x_7, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_23 = lean_array_push(x_19, x_3);
x_24 = lean_array_push(x_20, x_4);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_array_fget_borrowed(x_19, x_2);
x_27 = l_Lean_instBEqMVarId_beq(x_3, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_2, x_29);
lean_dec(x_2);
x_1 = x_28;
x_2 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_array_fset(x_19, x_2, x_3);
x_33 = lean_array_fset(x_20, x_2, x_4);
lean_dec(x_2);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__1;
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc_ref(x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_14 = x_1;
} else {
 lean_dec_ref(x_1);
 x_14 = lean_box(0);
}
x_15 = lean_array_fget(x_6, x_11);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_6, x_11, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
x_25 = l_Lean_instBEqMVarId_beq(x_4, x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_15);
x_26 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_23, x_24, x_4, x_5);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_18 = x_27;
goto block_21;
}
else
{
lean_dec(x_24);
lean_dec(x_23);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_18 = x_15;
goto block_21;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = l_Lean_instBEqMVarId_beq(x_4, x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_28, x_29, x_4, x_5);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_18 = x_32;
goto block_21;
}
else
{
lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_5);
x_18 = x_33;
goto block_21;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_7);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_18 = x_15;
goto block_21;
}
else
{
lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_15, 0);
lean_inc(x_39);
lean_dec(x_15);
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(x_39, x_40, x_41, x_4, x_5);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_18 = x_43;
goto block_21;
}
}
default: 
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_5);
x_18 = x_44;
goto block_21;
}
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fset(x_17, x_11, x_18);
lean_dec(x_11);
if (lean_is_scalar(x_14)) {
 x_20 = lean_alloc_ctor(0, 1, 0);
} else {
 x_20 = x_14;
}
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_1);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; size_t x_54; uint8_t x_55; 
x_46 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6___redArg(x_1, x_4, x_5);
x_54 = 7;
x_55 = lean_usize_dec_le(x_54, x_3);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_46);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_dec_lt(x_56, x_57);
lean_dec(x_56);
x_47 = x_58;
goto block_53;
}
else
{
x_47 = x_55;
goto block_53;
}
block_53:
{
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_46, 0);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_49);
lean_dec_ref(x_46);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__2;
x_52 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(x_3, x_48, x_49, x_50, x_51);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
return x_52;
}
else
{
return x_46;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; size_t x_70; uint8_t x_71; 
x_59 = lean_ctor_get(x_1, 0);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_1);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6___redArg(x_61, x_4, x_5);
x_70 = 7;
x_71 = lean_usize_dec_le(x_70, x_3);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_62);
x_73 = lean_unsigned_to_nat(4u);
x_74 = lean_nat_dec_lt(x_72, x_73);
lean_dec(x_72);
x_63 = x_74;
goto block_69;
}
else
{
x_63 = x_71;
goto block_69;
}
block_69:
{
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_65);
lean_dec_ref(x_62);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__2;
x_68 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(x_3, x_64, x_65, x_66, x_67);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
return x_68;
}
else
{
return x_62;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
x_10 = l_Lean_instHashableMVarId_hash(x_8);
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_instHashableMVarId_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_take(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 7);
x_10 = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(x_9, x_1, x_2);
lean_ctor_set(x_7, 7, x_10);
x_11 = lean_st_ref_set(x_3, x_5);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_23 = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(x_21, x_1, x_2);
x_24 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_15);
lean_ctor_set(x_24, 2, x_16);
lean_ctor_set(x_24, 3, x_17);
lean_ctor_set(x_24, 4, x_18);
lean_ctor_set(x_24, 5, x_19);
lean_ctor_set(x_24, 6, x_20);
lean_ctor_set(x_24, 7, x_23);
lean_ctor_set(x_24, 8, x_22);
lean_ctor_set(x_5, 0, x_24);
x_25 = lean_st_ref_set(x_3, x_5);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
x_30 = lean_ctor_get(x_5, 2);
x_31 = lean_ctor_get(x_5, 3);
x_32 = lean_ctor_get(x_5, 4);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_28, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_28, 3);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_28, 4);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_28, 5);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_28, 6);
lean_inc_ref(x_39);
x_40 = lean_ctor_get(x_28, 7);
lean_inc_ref(x_40);
x_41 = lean_ctor_get(x_28, 8);
lean_inc_ref(x_41);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 lean_ctor_release(x_28, 3);
 lean_ctor_release(x_28, 4);
 lean_ctor_release(x_28, 5);
 lean_ctor_release(x_28, 6);
 lean_ctor_release(x_28, 7);
 lean_ctor_release(x_28, 8);
 x_42 = x_28;
} else {
 lean_dec_ref(x_28);
 x_42 = lean_box(0);
}
x_43 = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(x_40, x_1, x_2);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 9, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_34);
lean_ctor_set(x_44, 2, x_35);
lean_ctor_set(x_44, 3, x_36);
lean_ctor_set(x_44, 4, x_37);
lean_ctor_set(x_44, 5, x_38);
lean_ctor_set(x_44, 6, x_39);
lean_ctor_set(x_44, 7, x_43);
lean_ctor_set(x_44, 8, x_41);
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_29);
lean_ctor_set(x_45, 2, x_30);
lean_ctor_set(x_45, 3, x_31);
lean_ctor_set(x_45, 4, x_32);
x_46 = lean_st_ref_set(x_3, x_45);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("result is not type correct", 26, 26);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec_ref(x_10);
lean_inc(x_1);
x_11 = l_Lean_MVarId_getTag(x_1, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_inc(x_1);
x_13 = l_Lean_MVarId_getType(x_1, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(x_14, x_6);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_17 = x_15;
} else {
 lean_dec_ref(x_15);
 x_17 = lean_box(0);
}
x_18 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_19 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(x_3, x_4, x_16, x_18, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_80; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_20);
x_80 = l_Lean_Meta_isTypeCorrect(x_20, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec_ref(x_80);
x_82 = lean_unbox(x_81);
lean_dec(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_83 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1;
lean_inc(x_20);
x_84 = l_Lean_indentExpr(x_20);
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
lean_inc(x_1);
x_87 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_86, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_87) == 0)
{
lean_dec_ref(x_87);
x_41 = x_5;
x_42 = x_6;
x_43 = x_7;
x_44 = x_8;
x_45 = lean_box(0);
goto block_79;
}
else
{
uint8_t x_88; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
return x_87;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
else
{
lean_dec(x_2);
x_41 = x_5;
x_42 = x_6;
x_43 = x_7;
x_44 = x_8;
x_45 = lean_box(0);
goto block_79;
}
}
else
{
uint8_t x_91; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_80);
if (x_91 == 0)
{
return x_80;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_80, 0);
lean_inc(x_92);
lean_dec(x_80);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
}
block_40:
{
lean_object* x_29; 
lean_inc_ref(x_21);
x_29 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_20, x_12, x_21, x_22, x_23, x_24);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
lean_inc(x_30);
x_31 = l_Lean_mkAppN(x_30, x_25);
lean_dec_ref(x_25);
x_32 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(x_1, x_31, x_22);
lean_dec_ref(x_32);
x_33 = 1;
x_34 = l_Lean_Expr_mvarId_x21(x_30);
lean_dec(x_30);
x_35 = lean_box(0);
x_36 = l_Lean_Meta_introNCore(x_34, x_26, x_35, x_28, x_33, x_21, x_22, x_23, x_24);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
block_79:
{
size_t x_46; size_t x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_array_size(x_3);
x_47 = 0;
lean_inc_ref(x_3);
x_48 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__0(x_46, x_47, x_3);
x_49 = lean_array_get_size(x_3);
x_50 = lean_nat_dec_lt(x_18, x_49);
if (x_50 == 0)
{
lean_dec(x_17);
lean_dec_ref(x_3);
x_21 = x_41;
x_22 = x_42;
x_23 = x_43;
x_24 = x_44;
x_25 = x_48;
x_26 = x_49;
x_27 = lean_box(0);
x_28 = x_50;
goto block_40;
}
else
{
if (x_50 == 0)
{
lean_dec(x_17);
lean_dec_ref(x_3);
x_21 = x_41;
x_22 = x_42;
x_23 = x_43;
x_24 = x_44;
x_25 = x_48;
x_26 = x_49;
x_27 = lean_box(0);
x_28 = x_50;
goto block_40;
}
else
{
size_t x_51; uint8_t x_52; 
x_51 = lean_usize_of_nat(x_49);
x_52 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__2(x_3, x_47, x_51);
if (x_52 == 0)
{
lean_dec(x_17);
lean_dec_ref(x_3);
x_21 = x_41;
x_22 = x_42;
x_23 = x_43;
x_24 = x_44;
x_25 = x_48;
x_26 = x_49;
x_27 = lean_box(0);
x_28 = x_52;
goto block_40;
}
else
{
uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = 0;
x_54 = lean_box(x_53);
x_55 = lean_box(x_52);
x_56 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__0___boxed), 11, 4);
lean_closure_set(x_56, 0, x_3);
lean_closure_set(x_56, 1, x_18);
lean_closure_set(x_56, 2, x_54);
lean_closure_set(x_56, 3, x_55);
if (lean_is_scalar(x_17)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_17;
 lean_ctor_set_tag(x_57, 1);
}
lean_ctor_set(x_57, 0, x_49);
lean_inc(x_44);
lean_inc_ref(x_43);
lean_inc(x_42);
lean_inc_ref(x_41);
x_58 = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__3___redArg(x_20, x_57, x_56, x_53, x_53, x_41, x_42, x_43, x_44);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc_ref(x_41);
x_62 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_61, x_12, x_41, x_42, x_43, x_44);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
lean_inc(x_63);
x_64 = l_Lean_mkAppN(x_63, x_48);
lean_dec_ref(x_48);
lean_inc(x_60);
x_65 = lean_array_mk(x_60);
x_66 = l_Lean_mkAppN(x_64, x_65);
lean_dec_ref(x_65);
x_67 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(x_1, x_66, x_42);
lean_dec_ref(x_67);
x_68 = l_Lean_Expr_mvarId_x21(x_63);
lean_dec(x_63);
x_69 = l_List_lengthTR___redArg(x_60);
lean_dec(x_60);
x_70 = lean_nat_add(x_49, x_69);
lean_dec(x_69);
x_71 = lean_box(0);
x_72 = l_Lean_Meta_introNCore(x_68, x_70, x_71, x_53, x_52, x_41, x_42, x_43, x_44);
return x_72;
}
else
{
uint8_t x_73; 
lean_dec(x_60);
lean_dec_ref(x_48);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_62);
if (x_73 == 0)
{
return x_62;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_62, 0);
lean_inc(x_74);
lean_dec(x_62);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec_ref(x_48);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_12);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_58);
if (x_76 == 0)
{
return x_58;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_58, 0);
lean_inc(x_77);
lean_dec(x_58);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
}
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_19);
if (x_94 == 0)
{
return x_19;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_19, 0);
lean_inc(x_95);
lean_dec(x_19);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_13);
if (x_97 == 0)
{
return x_13;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_13, 0);
lean_inc(x_98);
lean_dec(x_13);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_11);
if (x_100 == 0)
{
return x_11;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_11, 0);
lean_inc(x_101);
lean_dec(x_11);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_10);
if (x_103 == 0)
{
return x_10;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_10, 0);
lean_inc(x_104);
lean_dec(x_10);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("generalize", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__1;
x_10 = lean_box(x_3);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___boxed), 9, 4);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_9);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_10);
x_12 = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__4___redArg(x_1, x_11, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___redArg(x_1, x_2, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__7(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4_spec__6_spec__7___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalize(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_MVarId_generalize(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_7, 2);
x_12 = lean_nat_dec_lt(x_10, x_11);
if (x_12 == 0)
{
return x_4;
}
else
{
uint8_t x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_14 = lean_ctor_get(x_7, 2);
lean_dec(x_14);
x_15 = lean_ctor_get(x_7, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_7, 0);
lean_dec(x_16);
x_17 = lean_array_uget(x_1, x_3);
x_18 = lean_array_fget(x_9, x_10);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_10, x_19);
lean_dec(x_10);
lean_ctor_set(x_7, 1, x_20);
x_21 = l_Lean_mkFVar(x_18);
x_22 = l_Lean_Meta_FVarSubst_insert(x_8, x_17, x_21);
lean_ctor_set(x_4, 1, x_22);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_3 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; 
lean_dec(x_7);
x_26 = lean_array_uget(x_1, x_3);
x_27 = lean_array_fget(x_9, x_10);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_10, x_28);
lean_dec(x_10);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_9);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_11);
x_31 = l_Lean_mkFVar(x_27);
x_32 = l_Lean_Meta_FVarSubst_insert(x_8, x_26, x_31);
lean_ctor_set(x_4, 1, x_32);
lean_ctor_set(x_4, 0, x_30);
x_33 = 1;
x_34 = lean_usize_add(x_3, x_33);
x_3 = x_34;
goto _start;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_ctor_get(x_4, 0);
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_4);
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
x_40 = lean_ctor_get(x_36, 2);
x_41 = lean_nat_dec_lt(x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; 
lean_inc(x_40);
lean_inc(x_39);
lean_inc_ref(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 x_43 = x_36;
} else {
 lean_dec_ref(x_36);
 x_43 = lean_box(0);
}
x_44 = lean_array_uget(x_1, x_3);
x_45 = lean_array_fget(x_38, x_39);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_add(x_39, x_46);
lean_dec(x_39);
if (lean_is_scalar(x_43)) {
 x_48 = lean_alloc_ctor(0, 3, 0);
} else {
 x_48 = x_43;
}
lean_ctor_set(x_48, 0, x_38);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_40);
x_49 = l_Lean_mkFVar(x_45);
x_50 = l_Lean_Meta_FVarSubst_insert(x_37, x_44, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
x_52 = 1;
x_53 = lean_usize_add(x_3, x_52);
x_3 = x_53;
x_4 = x_51;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_3);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_uget(x_3, x_2);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_8, 2);
x_13 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(x_10, x_4);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_3, x_2, x_15);
lean_ctor_set(x_8, 0, x_14);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_16, x_2, x_8);
x_2 = x_18;
x_3 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
lean_free_object(x_8);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_3);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
x_26 = lean_ctor_get(x_8, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_8);
x_27 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(x_24, x_4);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_array_uset(x_3, x_2, x_29);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_25);
lean_ctor_set(x_31, 2, x_26);
x_32 = 1;
x_33 = lean_usize_add(x_2, x_32);
x_34 = lean_array_uset(x_30, x_2, x_31);
x_2 = x_33;
x_3 = x_34;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_3);
x_36 = lean_ctor_get(x_27, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_37 = x_27;
} else {
 lean_dec_ref(x_27);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 1, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_36);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(x_6, x_7, x_3, x_4);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_4, x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_array_uget(x_3, x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_13);
lean_dec(x_12);
x_14 = l_Lean_Meta_Context_config(x_6);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_16 = lean_ctor_get_uint8(x_6, sizeof(void*)*7);
x_17 = lean_ctor_get(x_6, 1);
x_18 = lean_ctor_get(x_6, 2);
x_19 = lean_ctor_get(x_6, 3);
x_20 = lean_ctor_get(x_6, 4);
x_21 = lean_ctor_get(x_6, 5);
x_22 = lean_ctor_get(x_6, 6);
x_23 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 1);
x_24 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 2);
x_25 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 3);
lean_ctor_set_uint8(x_14, 9, x_1);
x_26 = l_Lean_Meta_Context_configKey(x_6);
x_27 = 2;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_box(0);
x_30 = lean_uint64_shift_left(x_28, x_27);
x_31 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_32 = lean_uint64_lor(x_30, x_31);
x_33 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_33, 0, x_14);
lean_ctor_set_uint64(x_33, sizeof(void*)*1, x_32);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
x_34 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_17);
lean_ctor_set(x_34, 2, x_18);
lean_ctor_set(x_34, 3, x_19);
lean_ctor_set(x_34, 4, x_20);
lean_ctor_set(x_34, 5, x_21);
lean_ctor_set(x_34, 6, x_22);
lean_ctor_set_uint8(x_34, sizeof(void*)*7, x_16);
lean_ctor_set_uint8(x_34, sizeof(void*)*7 + 1, x_23);
lean_ctor_set_uint8(x_34, sizeof(void*)*7 + 2, x_24);
lean_ctor_set_uint8(x_34, sizeof(void*)*7 + 3, x_25);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_2);
x_35 = l_Lean_Meta_kabstract(x_2, x_13, x_29, x_34, x_7, x_8, x_9);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = l_Lean_Expr_hasLooseBVars(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
size_t x_39; size_t x_40; 
lean_free_object(x_35);
x_39 = 1;
x_40 = lean_usize_add(x_4, x_39);
x_4 = x_40;
goto _start;
}
else
{
lean_object* x_42; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_42 = lean_box(x_38);
lean_ctor_set(x_35, 0, x_42);
return x_35;
}
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_35, 0);
lean_inc(x_43);
lean_dec(x_35);
x_44 = l_Lean_Expr_hasLooseBVars(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
size_t x_45; size_t x_46; 
x_45 = 1;
x_46 = lean_usize_add(x_4, x_45);
x_4 = x_46;
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_48 = lean_box(x_44);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_50 = !lean_is_exclusive(x_35);
if (x_50 == 0)
{
return x_35;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_35, 0);
lean_inc(x_51);
lean_dec(x_35);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; lean_object* x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; lean_object* x_85; uint64_t x_86; uint64_t x_87; uint64_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_53 = lean_ctor_get_uint8(x_14, 0);
x_54 = lean_ctor_get_uint8(x_14, 1);
x_55 = lean_ctor_get_uint8(x_14, 2);
x_56 = lean_ctor_get_uint8(x_14, 3);
x_57 = lean_ctor_get_uint8(x_14, 4);
x_58 = lean_ctor_get_uint8(x_14, 5);
x_59 = lean_ctor_get_uint8(x_14, 6);
x_60 = lean_ctor_get_uint8(x_14, 7);
x_61 = lean_ctor_get_uint8(x_14, 8);
x_62 = lean_ctor_get_uint8(x_14, 10);
x_63 = lean_ctor_get_uint8(x_14, 11);
x_64 = lean_ctor_get_uint8(x_14, 12);
x_65 = lean_ctor_get_uint8(x_14, 13);
x_66 = lean_ctor_get_uint8(x_14, 14);
x_67 = lean_ctor_get_uint8(x_14, 15);
x_68 = lean_ctor_get_uint8(x_14, 16);
x_69 = lean_ctor_get_uint8(x_14, 17);
x_70 = lean_ctor_get_uint8(x_14, 18);
lean_dec(x_14);
x_71 = lean_ctor_get_uint8(x_6, sizeof(void*)*7);
x_72 = lean_ctor_get(x_6, 1);
x_73 = lean_ctor_get(x_6, 2);
x_74 = lean_ctor_get(x_6, 3);
x_75 = lean_ctor_get(x_6, 4);
x_76 = lean_ctor_get(x_6, 5);
x_77 = lean_ctor_get(x_6, 6);
x_78 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 1);
x_79 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 2);
x_80 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 3);
x_81 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_81, 0, x_53);
lean_ctor_set_uint8(x_81, 1, x_54);
lean_ctor_set_uint8(x_81, 2, x_55);
lean_ctor_set_uint8(x_81, 3, x_56);
lean_ctor_set_uint8(x_81, 4, x_57);
lean_ctor_set_uint8(x_81, 5, x_58);
lean_ctor_set_uint8(x_81, 6, x_59);
lean_ctor_set_uint8(x_81, 7, x_60);
lean_ctor_set_uint8(x_81, 8, x_61);
lean_ctor_set_uint8(x_81, 9, x_1);
lean_ctor_set_uint8(x_81, 10, x_62);
lean_ctor_set_uint8(x_81, 11, x_63);
lean_ctor_set_uint8(x_81, 12, x_64);
lean_ctor_set_uint8(x_81, 13, x_65);
lean_ctor_set_uint8(x_81, 14, x_66);
lean_ctor_set_uint8(x_81, 15, x_67);
lean_ctor_set_uint8(x_81, 16, x_68);
lean_ctor_set_uint8(x_81, 17, x_69);
lean_ctor_set_uint8(x_81, 18, x_70);
x_82 = l_Lean_Meta_Context_configKey(x_6);
x_83 = 2;
x_84 = lean_uint64_shift_right(x_82, x_83);
x_85 = lean_box(0);
x_86 = lean_uint64_shift_left(x_84, x_83);
x_87 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_88 = lean_uint64_lor(x_86, x_87);
x_89 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_89, 0, x_81);
lean_ctor_set_uint64(x_89, sizeof(void*)*1, x_88);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc_ref(x_74);
lean_inc_ref(x_73);
lean_inc(x_72);
x_90 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_72);
lean_ctor_set(x_90, 2, x_73);
lean_ctor_set(x_90, 3, x_74);
lean_ctor_set(x_90, 4, x_75);
lean_ctor_set(x_90, 5, x_76);
lean_ctor_set(x_90, 6, x_77);
lean_ctor_set_uint8(x_90, sizeof(void*)*7, x_71);
lean_ctor_set_uint8(x_90, sizeof(void*)*7 + 1, x_78);
lean_ctor_set_uint8(x_90, sizeof(void*)*7 + 2, x_79);
lean_ctor_set_uint8(x_90, sizeof(void*)*7 + 3, x_80);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_2);
x_91 = l_Lean_Meta_kabstract(x_2, x_13, x_85, x_90, x_7, x_8, x_9);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
x_94 = l_Lean_Expr_hasLooseBVars(x_92);
lean_dec(x_92);
if (x_94 == 0)
{
size_t x_95; size_t x_96; 
lean_dec(x_93);
x_95 = 1;
x_96 = lean_usize_add(x_4, x_95);
x_4 = x_96;
goto _start;
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_98 = lean_box(x_94);
if (lean_is_scalar(x_93)) {
 x_99 = lean_alloc_ctor(0, 1, 0);
} else {
 x_99 = x_93;
}
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_100 = lean_ctor_get(x_91, 0);
lean_inc(x_100);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_101 = x_91;
} else {
 lean_dec_ref(x_91);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 1, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_100);
return x_102;
}
}
}
else
{
uint8_t x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_103 = 0;
x_104 = lean_box(x_103);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(x_11, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_19; 
x_19 = lean_usize_dec_eq(x_5, x_6);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_25; 
x_20 = lean_array_uget(x_4, x_5);
lean_inc_ref(x_8);
lean_inc(x_20);
x_25 = l_Lean_FVarId_getType___redArg(x_20, x_8, x_10, x_11);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(x_26, x_9);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_array_get_size(x_1);
x_31 = lean_nat_dec_lt(x_29, x_30);
if (x_31 == 0)
{
lean_dec(x_28);
x_21 = x_2;
x_22 = lean_box(0);
goto block_24;
}
else
{
if (x_31 == 0)
{
lean_dec(x_28);
x_21 = x_2;
x_22 = lean_box(0);
goto block_24;
}
else
{
size_t x_32; size_t x_33; lean_object* x_34; 
x_32 = 0;
x_33 = lean_usize_of_nat(x_30);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
x_34 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(x_3, x_28, x_1, x_32, x_33, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
x_21 = x_36;
x_22 = lean_box(0);
goto block_24;
}
else
{
uint8_t x_37; 
lean_dec(x_20);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_20);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_40 = !lean_is_exclusive(x_27);
if (x_40 == 0)
{
return x_27;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_27, 0);
lean_inc(x_41);
lean_dec(x_27);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_20);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_43 = !lean_is_exclusive(x_25);
if (x_43 == 0)
{
return x_25;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_25, 0);
lean_inc(x_44);
lean_dec(x_25);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
block_24:
{
if (x_21 == 0)
{
lean_dec(x_20);
x_13 = x_7;
x_14 = lean_box(0);
goto block_18;
}
else
{
lean_object* x_23; 
x_23 = lean_array_push(x_7, x_20);
x_13 = x_23;
x_14 = lean_box(0);
goto block_18;
}
}
}
else
{
lean_object* x_46; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_7);
return x_46;
}
block_18:
{
size_t x_15; size_t x_16; 
x_15 = 1;
x_16 = lean_usize_add(x_5, x_15);
x_5 = x_16;
x_7 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_13 = lean_unbox(x_2);
x_14 = lean_unbox(x_3);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(x_1, x_13, x_14, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_19; 
x_19 = lean_usize_dec_eq(x_5, x_6);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_25; 
x_20 = lean_array_uget(x_4, x_5);
lean_inc_ref(x_8);
lean_inc(x_20);
x_25 = l_Lean_FVarId_getType___redArg(x_20, x_8, x_10, x_11);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_spec__0___redArg(x_26, x_9);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_array_get_size(x_2);
x_31 = lean_nat_dec_lt(x_29, x_30);
if (x_31 == 0)
{
lean_dec(x_28);
x_21 = x_3;
x_22 = lean_box(0);
goto block_24;
}
else
{
if (x_31 == 0)
{
lean_dec(x_28);
x_21 = x_3;
x_22 = lean_box(0);
goto block_24;
}
else
{
size_t x_32; size_t x_33; lean_object* x_34; 
x_32 = 0;
x_33 = lean_usize_of_nat(x_30);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
x_34 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MVarId_generalizeHyp_spec__1(x_1, x_28, x_2, x_32, x_33, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
x_21 = x_36;
x_22 = lean_box(0);
goto block_24;
}
else
{
uint8_t x_37; 
lean_dec(x_20);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_20);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_40 = !lean_is_exclusive(x_27);
if (x_40 == 0)
{
return x_27;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_27, 0);
lean_inc(x_41);
lean_dec(x_27);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_20);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_43 = !lean_is_exclusive(x_25);
if (x_43 == 0)
{
return x_25;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_25, 0);
lean_inc(x_44);
lean_dec(x_25);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
block_24:
{
if (x_21 == 0)
{
lean_dec(x_20);
x_13 = x_7;
x_14 = lean_box(0);
goto block_18;
}
else
{
lean_object* x_23; 
x_23 = lean_array_push(x_7, x_20);
x_13 = x_23;
x_14 = lean_box(0);
goto block_18;
}
}
}
else
{
lean_object* x_46; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_7);
return x_46;
}
block_18:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 1;
x_16 = lean_usize_add(x_5, x_15);
x_17 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3_spec__3(x_2, x_3, x_1, x_4, x_16, x_6, x_13, x_8, x_9, x_10, x_11);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_13 = lean_unbox(x_1);
x_14 = lean_unbox(x_3);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(x_13, x_2, x_14, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_17;
}
}
static lean_object* _init_l_Lean_MVarId_generalizeHyp___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = l_Array_isEmpty___redArg(x_3);
if (x_11 == 0)
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_array_size(x_2);
x_13 = 0;
x_14 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(x_12, x_13, x_2, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_126; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_132 = lean_unsigned_to_nat(0u);
x_133 = lean_array_get_size(x_3);
x_134 = l_Lean_MVarId_generalizeHyp___closed__0;
x_135 = lean_nat_dec_lt(x_132, x_133);
if (x_135 == 0)
{
x_16 = x_134;
x_17 = lean_box(0);
goto block_125;
}
else
{
uint8_t x_136; 
x_136 = lean_nat_dec_le(x_133, x_133);
if (x_136 == 0)
{
if (x_135 == 0)
{
x_16 = x_134;
x_17 = lean_box(0);
goto block_125;
}
else
{
size_t x_137; lean_object* x_138; 
x_137 = lean_usize_of_nat(x_133);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_138 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(x_5, x_15, x_11, x_3, x_13, x_137, x_134, x_6, x_7, x_8, x_9);
x_126 = x_138;
goto block_131;
}
}
else
{
size_t x_139; lean_object* x_140; 
x_139 = lean_usize_of_nat(x_133);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_140 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_generalizeHyp_spec__3(x_5, x_15, x_11, x_3, x_13, x_139, x_134, x_6, x_7, x_8, x_9);
x_126 = x_140;
goto block_131;
}
}
block_125:
{
uint8_t x_18; lean_object* x_19; 
x_18 = 1;
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_19 = l_Lean_MVarId_revert(x_1, x_16, x_18, x_11, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_24 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(x_23, x_15, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_array_get_size(x_22);
x_30 = lean_box(0);
x_31 = l_Lean_Meta_introNCore(x_28, x_29, x_30, x_11, x_18, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_array_get_size(x_35);
x_38 = l_Array_toSubarray___redArg(x_35, x_36, x_37);
lean_ctor_set(x_20, 1, x_4);
lean_ctor_set(x_20, 0, x_38);
x_39 = lean_array_size(x_22);
x_40 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(x_22, x_39, x_13, x_20);
lean_dec(x_22);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec_ref(x_40);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_25, 1, x_33);
lean_ctor_set(x_25, 0, x_41);
lean_ctor_set(x_31, 0, x_25);
return x_31;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_33, 0);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_33);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_array_get_size(x_42);
x_46 = l_Array_toSubarray___redArg(x_42, x_44, x_45);
lean_ctor_set(x_20, 1, x_4);
lean_ctor_set(x_20, 0, x_46);
x_47 = lean_array_size(x_22);
x_48 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(x_22, x_47, x_13, x_20);
lean_dec(x_22);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_27);
lean_ctor_set(x_50, 1, x_43);
lean_ctor_set(x_25, 1, x_50);
lean_ctor_set(x_25, 0, x_49);
lean_ctor_set(x_31, 0, x_25);
return x_31;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_51 = lean_ctor_get(x_31, 0);
lean_inc(x_51);
lean_dec(x_31);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_array_get_size(x_52);
x_57 = l_Array_toSubarray___redArg(x_52, x_55, x_56);
lean_ctor_set(x_20, 1, x_4);
lean_ctor_set(x_20, 0, x_57);
x_58 = lean_array_size(x_22);
x_59 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(x_22, x_58, x_13, x_20);
lean_dec(x_22);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec_ref(x_59);
if (lean_is_scalar(x_54)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_54;
}
lean_ctor_set(x_61, 0, x_27);
lean_ctor_set(x_61, 1, x_53);
lean_ctor_set(x_25, 1, x_61);
lean_ctor_set(x_25, 0, x_60);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_25);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_free_object(x_25);
lean_dec(x_27);
lean_free_object(x_20);
lean_dec(x_22);
lean_dec(x_4);
x_63 = !lean_is_exclusive(x_31);
if (x_63 == 0)
{
return x_31;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_31, 0);
lean_inc(x_64);
lean_dec(x_31);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_25, 0);
x_67 = lean_ctor_get(x_25, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_25);
x_68 = lean_array_get_size(x_22);
x_69 = lean_box(0);
x_70 = l_Lean_Meta_introNCore(x_67, x_68, x_69, x_11, x_18, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; size_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_75 = x_71;
} else {
 lean_dec_ref(x_71);
 x_75 = lean_box(0);
}
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_array_get_size(x_73);
x_78 = l_Array_toSubarray___redArg(x_73, x_76, x_77);
lean_ctor_set(x_20, 1, x_4);
lean_ctor_set(x_20, 0, x_78);
x_79 = lean_array_size(x_22);
x_80 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(x_22, x_79, x_13, x_20);
lean_dec(x_22);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec_ref(x_80);
if (lean_is_scalar(x_75)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_75;
}
lean_ctor_set(x_82, 0, x_66);
lean_ctor_set(x_82, 1, x_74);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
if (lean_is_scalar(x_72)) {
 x_84 = lean_alloc_ctor(0, 1, 0);
} else {
 x_84 = x_72;
}
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_66);
lean_free_object(x_20);
lean_dec(x_22);
lean_dec(x_4);
x_85 = lean_ctor_get(x_70, 0);
lean_inc(x_85);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 x_86 = x_70;
} else {
 lean_dec_ref(x_70);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 1, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_85);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_free_object(x_20);
lean_dec(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
x_88 = !lean_is_exclusive(x_24);
if (x_88 == 0)
{
return x_24;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_24, 0);
lean_inc(x_89);
lean_dec(x_24);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_20, 0);
x_92 = lean_ctor_get(x_20, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_20);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_93 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(x_92, x_15, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec_ref(x_93);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_97 = x_94;
} else {
 lean_dec_ref(x_94);
 x_97 = lean_box(0);
}
x_98 = lean_array_get_size(x_91);
x_99 = lean_box(0);
x_100 = l_Lean_Meta_introNCore(x_96, x_98, x_99, x_11, x_18, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; size_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_105 = x_101;
} else {
 lean_dec_ref(x_101);
 x_105 = lean_box(0);
}
x_106 = lean_unsigned_to_nat(0u);
x_107 = lean_array_get_size(x_103);
x_108 = l_Array_toSubarray___redArg(x_103, x_106, x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_4);
x_110 = lean_array_size(x_91);
x_111 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_generalizeHyp_spec__2(x_91, x_110, x_13, x_109);
lean_dec(x_91);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec_ref(x_111);
if (lean_is_scalar(x_105)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_105;
}
lean_ctor_set(x_113, 0, x_95);
lean_ctor_set(x_113, 1, x_104);
if (lean_is_scalar(x_97)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_97;
}
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
if (lean_is_scalar(x_102)) {
 x_115 = lean_alloc_ctor(0, 1, 0);
} else {
 x_115 = x_102;
}
lean_ctor_set(x_115, 0, x_114);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_91);
lean_dec(x_4);
x_116 = lean_ctor_get(x_100, 0);
lean_inc(x_116);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 x_117 = x_100;
} else {
 lean_dec_ref(x_100);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 1, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_116);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_91);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
x_119 = lean_ctor_get(x_93, 0);
lean_inc(x_119);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_120 = x_93;
} else {
 lean_dec_ref(x_93);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 1, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_119);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
x_122 = !lean_is_exclusive(x_19);
if (x_122 == 0)
{
return x_19;
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_19, 0);
lean_inc(x_123);
lean_dec(x_19);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
}
}
block_131:
{
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_dec_ref(x_126);
x_16 = x_127;
x_17 = lean_box(0);
goto block_125;
}
else
{
uint8_t x_128; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_126);
if (x_128 == 0)
{
return x_126;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_126, 0);
lean_inc(x_129);
lean_dec(x_126);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_141 = !lean_is_exclusive(x_14);
if (x_141 == 0)
{
return x_14;
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_14, 0);
lean_inc(x_142);
lean_dec(x_14);
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_142);
return x_143;
}
}
}
else
{
lean_object* x_144; 
x_144 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_144) == 0)
{
uint8_t x_145; 
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_144, 0);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_4);
lean_ctor_set(x_147, 1, x_146);
lean_ctor_set(x_144, 0, x_147);
return x_144;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_144, 0);
lean_inc(x_148);
lean_dec(x_144);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_4);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_150, 0, x_149);
return x_150;
}
}
else
{
uint8_t x_151; 
lean_dec(x_4);
x_151 = !lean_is_exclusive(x_144);
if (x_151 == 0)
{
return x_144;
}
else
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_144, 0);
lean_inc(x_152);
lean_dec(x_144);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_152);
return x_153;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
x_12 = l_Lean_MVarId_generalizeHyp(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___redArg(x_1, x_2, x_3, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_generalizeHyp_spec__0(x_9, x_10, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_11;
}
}
lean_object* initialize_Lean_Meta_KAbstract(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Revert(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Generalize(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_KAbstract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_FVarSubst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Revert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__0 = _init_l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__0();
lean_mark_persistent(l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__0);
l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__1 = _init_l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__1);
l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__2 = _init_l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__2();
lean_mark_persistent(l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__2);
l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__3 = _init_l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__3();
lean_mark_persistent(l_Lean_Meta_instInhabitedGeneralizeArg_default___closed__3);
l_Lean_Meta_instInhabitedGeneralizeArg_default = _init_l_Lean_Meta_instInhabitedGeneralizeArg_default();
lean_mark_persistent(l_Lean_Meta_instInhabitedGeneralizeArg_default);
l_Lean_Meta_instInhabitedGeneralizeArg = _init_l_Lean_Meta_instInhabitedGeneralizeArg();
lean_mark_persistent(l_Lean_Meta_instInhabitedGeneralizeArg);
l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__0 = _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__0);
l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__1 = _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__1);
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__0();
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__1();
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__2 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__2();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_spec__1_spec__1_spec__4___redArg___closed__2);
l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__0 = _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__0);
l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1 = _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lam__1___closed__1);
l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__0 = _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__0);
l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__1 = _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__1);
l_Lean_MVarId_generalizeHyp___closed__0 = _init_l_Lean_MVarId_generalizeHyp___closed__0();
lean_mark_persistent(l_Lean_MVarId_generalizeHyp___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
