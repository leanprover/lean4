// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Canon
// Imports: Init.Grind.Util Lean.Meta.Basic Lean.Meta.FunInfo Lean.Util.FVarSubset Lean.Util.PtrSet Lean.Util.FVarSubset Lean.Meta.Tactic.Grind.Types
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___spec__1(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__5;
static lean_object* l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__6;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__12___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_canon___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__2;
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__5;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion(lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__2;
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_shouldCanon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___boxed(lean_object**);
uint64_t lean_uint64_of_nat(lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonImpl___closed__1;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_get_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__2;
uint8_t l_Lean_Expr_isApp(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__9;
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___lambda__1___boxed(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__4___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__5;
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__4;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_canon___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__2;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__8;
static lean_object* l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__5;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__6;
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPtrMap___rarg(lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__3;
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__5;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__4(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__3___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__2;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__7;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__3;
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___closed__2;
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
lean_object* l_StateRefT_x27_lift___rarg___boxed(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isImplicit(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__12;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_ReaderT_instMonadLift(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__1;
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__2(lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__4;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__4;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__2___boxed(lean_object**);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Canon_instInhabitedShouldCanonResult;
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_toCtorIdx(uint8_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isInstImplicit(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_shouldCanon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___boxed(lean_object**);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadMetaM;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__10;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__1;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__14___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__6;
static lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__4;
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_shouldCanon___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_shouldCanon___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_get_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImplicit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___closed__1;
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__7;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__9;
static lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__3;
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__3;
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__3;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__3;
static lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__1;
static size_t l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__7;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static uint64_t l_Lean_Meta_Grind_Canon_canonImplicit___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__5;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__6;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__14(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__4;
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_modify_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__1;
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lean_Meta_Grind_Canon_canonInst___closed__1;
static lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__8;
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__1;
lean_object* l_Lean_isTracingEnabledForCore(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13___boxed(lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_canon_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__13;
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
static lean_object* l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__1;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__11(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__5;
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_modify_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__11;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Lean_Meta_Grind_getConfig___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__3(lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__2;
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_get_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_get_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_get_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_modify_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_st_ref_take(x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_apply_1(x_1, x_15);
lean_ctor_set(x_12, 1, x_16);
x_17 = lean_st_ref_set(x_2, x_12, x_13);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
x_26 = lean_ctor_get(x_12, 2);
x_27 = lean_ctor_get(x_12, 3);
x_28 = lean_ctor_get(x_12, 4);
x_29 = lean_ctor_get(x_12, 5);
x_30 = lean_ctor_get(x_12, 6);
x_31 = lean_ctor_get_uint8(x_12, sizeof(void*)*15);
x_32 = lean_ctor_get(x_12, 7);
x_33 = lean_ctor_get(x_12, 8);
x_34 = lean_ctor_get(x_12, 9);
x_35 = lean_ctor_get(x_12, 10);
x_36 = lean_ctor_get(x_12, 11);
x_37 = lean_ctor_get(x_12, 12);
x_38 = lean_ctor_get(x_12, 13);
x_39 = lean_ctor_get(x_12, 14);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_40 = lean_apply_1(x_1, x_25);
x_41 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_41, 0, x_24);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_26);
lean_ctor_set(x_41, 3, x_27);
lean_ctor_set(x_41, 4, x_28);
lean_ctor_set(x_41, 5, x_29);
lean_ctor_set(x_41, 6, x_30);
lean_ctor_set(x_41, 7, x_32);
lean_ctor_set(x_41, 8, x_33);
lean_ctor_set(x_41, 9, x_34);
lean_ctor_set(x_41, 10, x_35);
lean_ctor_set(x_41, 11, x_36);
lean_ctor_set(x_41, 12, x_37);
lean_ctor_set(x_41, 13, x_38);
lean_ctor_set(x_41, 14, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*15, x_31);
x_42 = lean_st_ref_set(x_2, x_41, x_13);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
x_45 = lean_box(0);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_modify_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_modify_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_apply_10(x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___spec__1___rarg), 11, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_12 = l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___rarg(x_11, x_8, x_9, x_10);
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_11 = 0;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__1___boxed), 10, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to show that", 19, 19);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nis definitionally equal to", 27, 27);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nwhile canonicalizing", 21, 21);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nusing `", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("*1000` heartbeats, `(canonHeartbeats := ", 40, 40);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")`", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = l_Lean_Exception_isRuntime(x_1);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_1);
x_18 = l_Lean_Meta_Grind_getConfig___rarg(x_2, x_3, x_4, x_5, x_13, x_14, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__1;
x_23 = lean_ctor_get_uint8(x_20, sizeof(void*)*6 + 6);
lean_dec(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_24 = lean_box(0);
x_25 = lean_apply_10(x_22, x_24, x_6, x_7, x_2, x_3, x_4, x_5, x_13, x_14, x_21);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_26 = l_Lean_indentExpr(x_8);
x_27 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__3;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_26);
lean_ctor_set(x_18, 0, x_27);
x_28 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__5;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_indentExpr(x_9);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__7;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_indentExpr(x_10);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__9;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l___private_Init_Data_Repr_0__Nat_reprFast(x_11);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = l_Lean_MessageData_ofFormat(x_39);
lean_inc(x_40);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
x_42 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__11;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
x_45 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__13;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Meta_Grind_reportIssue(x_46, x_7, x_2, x_3, x_4, x_5, x_13, x_14, x_21);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_apply_10(x_22, x_48, x_6, x_7, x_2, x_3, x_4, x_5, x_13, x_14, x_49);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_18, 0);
x_52 = lean_ctor_get(x_18, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_18);
x_53 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__1;
x_54 = lean_ctor_get_uint8(x_51, sizeof(void*)*6 + 6);
lean_dec(x_51);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_55 = lean_box(0);
x_56 = lean_apply_10(x_53, x_55, x_6, x_7, x_2, x_3, x_4, x_5, x_13, x_14, x_52);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_57 = l_Lean_indentExpr(x_8);
x_58 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__3;
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__5;
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_indentExpr(x_9);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__7;
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_indentExpr(x_10);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__9;
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l___private_Init_Data_Repr_0__Nat_reprFast(x_11);
x_71 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = l_Lean_MessageData_ofFormat(x_71);
lean_inc(x_72);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_72);
x_74 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__11;
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_72);
x_77 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__13;
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_Meta_Grind_reportIssue(x_78, x_7, x_2, x_3, x_4, x_5, x_13, x_14, x_52);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_apply_10(x_53, x_80, x_6, x_7, x_2, x_3, x_4, x_5, x_13, x_14, x_81);
return x_82;
}
}
}
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__3___closed__1() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 1;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint64_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_14 = lean_ctor_get(x_4, 5);
lean_inc(x_14);
lean_dec(x_4);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_11, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_11, 4);
lean_inc(x_19);
x_20 = lean_ctor_get(x_11, 5);
lean_inc(x_20);
x_21 = lean_ctor_get(x_11, 6);
lean_inc(x_21);
x_22 = lean_ctor_get(x_11, 7);
lean_inc(x_22);
x_23 = lean_ctor_get(x_11, 8);
lean_inc(x_23);
x_24 = lean_ctor_get(x_11, 10);
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_11, sizeof(void*)*12);
x_26 = lean_ctor_get(x_11, 11);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_11, sizeof(void*)*12 + 1);
x_28 = lean_unsigned_to_nat(1000u);
x_29 = lean_nat_mul(x_14, x_28);
x_30 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_30, 0, x_15);
lean_ctor_set(x_30, 1, x_16);
lean_ctor_set(x_30, 2, x_17);
lean_ctor_set(x_30, 3, x_18);
lean_ctor_set(x_30, 4, x_19);
lean_ctor_set(x_30, 5, x_20);
lean_ctor_set(x_30, 6, x_21);
lean_ctor_set(x_30, 7, x_22);
lean_ctor_set(x_30, 8, x_23);
lean_ctor_set(x_30, 9, x_29);
lean_ctor_set(x_30, 10, x_24);
lean_ctor_set(x_30, 11, x_26);
lean_ctor_set_uint8(x_30, sizeof(void*)*12, x_25);
lean_ctor_set_uint8(x_30, sizeof(void*)*12 + 1, x_27);
x_31 = lean_ctor_get(x_9, 0);
lean_inc(x_31);
x_32 = lean_ctor_get_uint64(x_9, sizeof(void*)*7);
x_33 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 8);
x_34 = lean_ctor_get(x_9, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_9, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_9, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_9, 4);
lean_inc(x_37);
x_38 = lean_ctor_get(x_9, 5);
lean_inc(x_38);
x_39 = lean_ctor_get(x_9, 6);
lean_inc(x_39);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
uint8_t x_41; uint8_t x_42; uint8_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 9);
x_42 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 10);
x_43 = 1;
lean_ctor_set_uint8(x_31, 9, x_43);
x_44 = 2;
x_45 = lean_uint64_shift_right(x_32, x_44);
x_46 = lean_uint64_shift_left(x_45, x_44);
x_47 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__3___closed__1;
x_48 = lean_uint64_lor(x_46, x_47);
x_49 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_49, 0, x_31);
lean_ctor_set(x_49, 1, x_34);
lean_ctor_set(x_49, 2, x_35);
lean_ctor_set(x_49, 3, x_36);
lean_ctor_set(x_49, 4, x_37);
lean_ctor_set(x_49, 5, x_38);
lean_ctor_set(x_49, 6, x_39);
lean_ctor_set_uint64(x_49, sizeof(void*)*7, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*7 + 8, x_33);
lean_ctor_set_uint8(x_49, sizeof(void*)*7 + 9, x_41);
lean_ctor_set_uint8(x_49, sizeof(void*)*7 + 10, x_42);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_2);
lean_inc(x_1);
x_50 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_49, x_10, x_30, x_12, x_13);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
return x_50;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
x_58 = l_Lean_Exception_isInterrupt(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_free_object(x_50);
x_59 = lean_box(0);
x_60 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2(x_56, x_7, x_8, x_9, x_10, x_5, x_6, x_1, x_2, x_3, x_14, x_59, x_11, x_12, x_57);
return x_60;
}
else
{
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_50;
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_50, 0);
x_62 = lean_ctor_get(x_50, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_50);
x_63 = l_Lean_Exception_isInterrupt(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_box(0);
x_65 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2(x_61, x_7, x_8, x_9, x_10, x_5, x_6, x_1, x_2, x_3, x_14, x_64, x_11, x_12, x_62);
return x_65;
}
else
{
lean_object* x_66; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_61);
lean_ctor_set(x_66, 1, x_62);
return x_66;
}
}
}
}
else
{
uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; lean_object* x_87; uint64_t x_88; uint64_t x_89; uint64_t x_90; uint64_t x_91; uint64_t x_92; lean_object* x_93; lean_object* x_94; 
x_67 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 9);
x_68 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 10);
x_69 = lean_ctor_get_uint8(x_31, 0);
x_70 = lean_ctor_get_uint8(x_31, 1);
x_71 = lean_ctor_get_uint8(x_31, 2);
x_72 = lean_ctor_get_uint8(x_31, 3);
x_73 = lean_ctor_get_uint8(x_31, 4);
x_74 = lean_ctor_get_uint8(x_31, 5);
x_75 = lean_ctor_get_uint8(x_31, 6);
x_76 = lean_ctor_get_uint8(x_31, 7);
x_77 = lean_ctor_get_uint8(x_31, 8);
x_78 = lean_ctor_get_uint8(x_31, 10);
x_79 = lean_ctor_get_uint8(x_31, 11);
x_80 = lean_ctor_get_uint8(x_31, 12);
x_81 = lean_ctor_get_uint8(x_31, 13);
x_82 = lean_ctor_get_uint8(x_31, 14);
x_83 = lean_ctor_get_uint8(x_31, 15);
x_84 = lean_ctor_get_uint8(x_31, 16);
x_85 = lean_ctor_get_uint8(x_31, 17);
lean_dec(x_31);
x_86 = 1;
x_87 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_87, 0, x_69);
lean_ctor_set_uint8(x_87, 1, x_70);
lean_ctor_set_uint8(x_87, 2, x_71);
lean_ctor_set_uint8(x_87, 3, x_72);
lean_ctor_set_uint8(x_87, 4, x_73);
lean_ctor_set_uint8(x_87, 5, x_74);
lean_ctor_set_uint8(x_87, 6, x_75);
lean_ctor_set_uint8(x_87, 7, x_76);
lean_ctor_set_uint8(x_87, 8, x_77);
lean_ctor_set_uint8(x_87, 9, x_86);
lean_ctor_set_uint8(x_87, 10, x_78);
lean_ctor_set_uint8(x_87, 11, x_79);
lean_ctor_set_uint8(x_87, 12, x_80);
lean_ctor_set_uint8(x_87, 13, x_81);
lean_ctor_set_uint8(x_87, 14, x_82);
lean_ctor_set_uint8(x_87, 15, x_83);
lean_ctor_set_uint8(x_87, 16, x_84);
lean_ctor_set_uint8(x_87, 17, x_85);
x_88 = 2;
x_89 = lean_uint64_shift_right(x_32, x_88);
x_90 = lean_uint64_shift_left(x_89, x_88);
x_91 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__3___closed__1;
x_92 = lean_uint64_lor(x_90, x_91);
x_93 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_93, 0, x_87);
lean_ctor_set(x_93, 1, x_34);
lean_ctor_set(x_93, 2, x_35);
lean_ctor_set(x_93, 3, x_36);
lean_ctor_set(x_93, 4, x_37);
lean_ctor_set(x_93, 5, x_38);
lean_ctor_set(x_93, 6, x_39);
lean_ctor_set_uint64(x_93, sizeof(void*)*7, x_92);
lean_ctor_set_uint8(x_93, sizeof(void*)*7 + 8, x_33);
lean_ctor_set_uint8(x_93, sizeof(void*)*7 + 9, x_67);
lean_ctor_set_uint8(x_93, sizeof(void*)*7 + 10, x_68);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_2);
lean_inc(x_1);
x_94 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_93, x_10, x_30, x_12, x_13);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_99 = lean_ctor_get(x_94, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_94, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_101 = x_94;
} else {
 lean_dec_ref(x_94);
 x_101 = lean_box(0);
}
x_102 = l_Lean_Exception_isInterrupt(x_99);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_101);
x_103 = lean_box(0);
x_104 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2(x_99, x_7, x_8, x_9, x_10, x_5, x_6, x_1, x_2, x_3, x_14, x_103, x_11, x_12, x_100);
return x_104;
}
else
{
lean_object* x_105; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_101)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_101;
}
lean_ctor_set(x_105, 0, x_99);
lean_ctor_set(x_105, 1, x_100);
return x_105;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_getConfig___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___closed__1;
x_2 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__3), 13, 3);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
x_14 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___closed__2;
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___spec__1___rarg), 11, 2);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_13);
x_16 = l_Lean_Core_withCurrHeartbeats___at___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___spec__2(x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_expr_eqv(x_10, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_4, x_15);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_eq(x_11, x_13);
lean_dec(x_13);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_4, x_19);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__2;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_expr_eqv(x_14, x_16);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_13);
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_eq(x_15, x_17);
lean_dec(x_17);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_13);
lean_free_object(x_1);
x_21 = lean_box(0);
return x_21;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
}
case 1:
{
lean_object* x_22; size_t x_23; 
lean_free_object(x_1);
x_22 = lean_ctor_get(x_11, 0);
lean_inc(x_22);
lean_dec(x_11);
x_23 = lean_usize_shift_right(x_2, x_6);
x_1 = x_22;
x_2 = x_23;
goto _start;
}
default: 
{
lean_object* x_25; 
lean_free_object(x_1);
x_25 = lean_box(0);
return x_25;
}
}
}
else
{
lean_object* x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = 5;
x_28 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__2;
x_29 = lean_usize_land(x_2, x_28);
x_30 = lean_usize_to_nat(x_29);
x_31 = lean_box(2);
x_32 = lean_array_get(x_31, x_26, x_30);
lean_dec(x_30);
lean_dec(x_26);
switch (lean_obj_tag(x_32)) {
case 0:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_3, 0);
x_36 = lean_ctor_get(x_3, 1);
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
x_39 = lean_expr_eqv(x_35, x_37);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_38);
lean_dec(x_34);
x_40 = lean_box(0);
return x_40;
}
else
{
uint8_t x_41; 
x_41 = lean_nat_dec_eq(x_36, x_38);
lean_dec(x_38);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_34);
x_42 = lean_box(0);
return x_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_34);
return x_43;
}
}
}
case 1:
{
lean_object* x_44; size_t x_45; 
x_44 = lean_ctor_get(x_32, 0);
lean_inc(x_44);
lean_dec(x_32);
x_45 = lean_usize_shift_right(x_2, x_27);
x_1 = x_44;
x_2 = x_45;
goto _start;
}
default: 
{
lean_object* x_47; 
x_47 = lean_box(0);
return x_47;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_1, 1);
lean_inc(x_49);
lean_dec(x_1);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__3(x_48, x_49, lean_box(0), x_50, x_3);
lean_dec(x_49);
lean_dec(x_48);
return x_51;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; size_t x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_Expr_hash(x_3);
x_6 = lean_uint64_of_nat(x_4);
x_7 = lean_uint64_mix_hash(x_5, x_6);
x_8 = lean_uint64_to_usize(x_7);
x_9 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2(x_1, x_8, x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Expr_hash(x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 1;
x_14 = lean_usize_sub(x_1, x_13);
x_15 = 5;
x_16 = lean_usize_mul(x_15, x_14);
x_17 = lean_usize_shift_right(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_expr_eqv(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__2;
x_11 = lean_usize_land(x_2, x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_expr_eqv(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_expr_eqv(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_9);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = lean_usize_shift_right(x_2, x_9);
x_42 = lean_usize_add(x_3, x_8);
x_43 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__2;
x_52 = lean_usize_land(x_2, x_51);
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(0);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = lean_expr_eqv(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = lean_usize_shift_right(x_2, x_50);
x_74 = lean_usize_add(x_3, x_49);
x_75 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; size_t x_85; uint8_t x_86; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__7(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
x_88 = lean_unsigned_to_nat(4u);
x_89 = lean_nat_dec_lt(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__1;
x_93 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_3, x_90, x_91, lean_box(0), x_83, x_92);
lean_dec(x_91);
lean_dec(x_90);
return x_93;
}
else
{
return x_84;
}
}
else
{
return x_84;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; uint8_t x_100; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__7(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
x_102 = lean_unsigned_to_nat(4u);
x_103 = lean_nat_dec_lt(x_101, x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_106 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__1;
x_107 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_3, x_104, x_105, lean_box(0), x_97, x_106);
lean_dec(x_105);
lean_dec(x_104);
return x_107;
}
else
{
return x_98;
}
}
else
{
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Expr_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debugn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("canon", 5, 5);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__1;
x_2 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__2;
x_3 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("found using `isDefEqBounded`: ", 30, 30);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ===> ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (x_1 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded(x_3, x_4, x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_2);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_st_ref_take(x_7, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_28, 1);
x_33 = lean_ctor_get(x_28, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_29, 1);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_30);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_4);
lean_inc(x_3);
x_38 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_37, x_3, x_4);
lean_ctor_set(x_30, 1, x_38);
x_39 = lean_st_ref_set(x_7, x_29, x_32);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_41 = lean_ctor_get(x_39, 1);
x_42 = lean_ctor_get(x_39, 0);
lean_dec(x_42);
x_43 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__4;
x_44 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_43, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_41);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_free_object(x_39);
lean_free_object(x_28);
lean_dec(x_3);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_box(0);
x_49 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_4, x_48, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_47);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_49;
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_44);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_44, 1);
x_52 = lean_ctor_get(x_44, 0);
lean_dec(x_52);
x_53 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_51);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = l_Lean_MessageData_ofExpr(x_3);
x_56 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__6;
lean_ctor_set_tag(x_44, 7);
lean_ctor_set(x_44, 1, x_55);
lean_ctor_set(x_44, 0, x_56);
x_57 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__8;
lean_ctor_set_tag(x_39, 7);
lean_ctor_set(x_39, 1, x_57);
lean_ctor_set(x_39, 0, x_44);
lean_inc(x_4);
x_58 = l_Lean_MessageData_ofExpr(x_4);
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_58);
lean_ctor_set(x_28, 0, x_39);
x_59 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_28);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_43, x_60, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_54);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_4, x_62, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_63);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_62);
return x_64;
}
else
{
uint8_t x_65; 
lean_free_object(x_44);
lean_free_object(x_39);
lean_free_object(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_65 = !lean_is_exclusive(x_53);
if (x_65 == 0)
{
return x_53;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_53, 0);
x_67 = lean_ctor_get(x_53, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_53);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_44, 1);
lean_inc(x_69);
lean_dec(x_44);
x_70 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = l_Lean_MessageData_ofExpr(x_3);
x_73 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__6;
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__8;
lean_ctor_set_tag(x_39, 7);
lean_ctor_set(x_39, 1, x_75);
lean_ctor_set(x_39, 0, x_74);
lean_inc(x_4);
x_76 = l_Lean_MessageData_ofExpr(x_4);
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_76);
lean_ctor_set(x_28, 0, x_39);
x_77 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10;
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_28);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_43, x_78, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_71);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_4, x_80, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_81);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_80);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_free_object(x_39);
lean_free_object(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_83 = lean_ctor_get(x_70, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_70, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_85 = x_70;
} else {
 lean_dec_ref(x_70);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_87 = lean_ctor_get(x_39, 1);
lean_inc(x_87);
lean_dec(x_39);
x_88 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__4;
x_89 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_88, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_87);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_unbox(x_90);
lean_dec(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_free_object(x_28);
lean_dec(x_3);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_93 = lean_box(0);
x_94 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_4, x_93, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_92);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_96 = x_89;
} else {
 lean_dec_ref(x_89);
 x_96 = lean_box(0);
}
x_97 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_95);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = l_Lean_MessageData_ofExpr(x_3);
x_100 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__6;
if (lean_is_scalar(x_96)) {
 x_101 = lean_alloc_ctor(7, 2, 0);
} else {
 x_101 = x_96;
 lean_ctor_set_tag(x_101, 7);
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__8;
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
lean_inc(x_4);
x_104 = l_Lean_MessageData_ofExpr(x_4);
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_104);
lean_ctor_set(x_28, 0, x_103);
x_105 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10;
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_28);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_88, x_106, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_98);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_4, x_108, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_109);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_108);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_96);
lean_free_object(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_111 = lean_ctor_get(x_97, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_97, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_113 = x_97;
} else {
 lean_dec_ref(x_97);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_115 = lean_ctor_get(x_30, 0);
x_116 = lean_ctor_get(x_30, 1);
x_117 = lean_ctor_get(x_30, 2);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_30);
lean_inc(x_4);
lean_inc(x_3);
x_118 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_116, x_3, x_4);
x_119 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_119, 0, x_115);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_119, 2, x_117);
lean_ctor_set(x_29, 1, x_119);
x_120 = lean_st_ref_set(x_7, x_29, x_32);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_122 = x_120;
} else {
 lean_dec_ref(x_120);
 x_122 = lean_box(0);
}
x_123 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__4;
x_124 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_123, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_121);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_unbox(x_125);
lean_dec(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_122);
lean_free_object(x_28);
lean_dec(x_3);
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
lean_dec(x_124);
x_128 = lean_box(0);
x_129 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_4, x_128, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_127);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_124, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_131 = x_124;
} else {
 lean_dec_ref(x_124);
 x_131 = lean_box(0);
}
x_132 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_130);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
x_134 = l_Lean_MessageData_ofExpr(x_3);
x_135 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__6;
if (lean_is_scalar(x_131)) {
 x_136 = lean_alloc_ctor(7, 2, 0);
} else {
 x_136 = x_131;
 lean_ctor_set_tag(x_136, 7);
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_134);
x_137 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__8;
if (lean_is_scalar(x_122)) {
 x_138 = lean_alloc_ctor(7, 2, 0);
} else {
 x_138 = x_122;
 lean_ctor_set_tag(x_138, 7);
}
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
lean_inc(x_4);
x_139 = l_Lean_MessageData_ofExpr(x_4);
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_139);
lean_ctor_set(x_28, 0, x_138);
x_140 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10;
x_141 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_141, 0, x_28);
lean_ctor_set(x_141, 1, x_140);
x_142 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_123, x_141, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_133);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_4, x_143, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_144);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_143);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_131);
lean_dec(x_122);
lean_free_object(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_146 = lean_ctor_get(x_132, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_132, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_148 = x_132;
} else {
 lean_dec_ref(x_132);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_150 = lean_ctor_get(x_29, 0);
x_151 = lean_ctor_get(x_29, 2);
x_152 = lean_ctor_get(x_29, 3);
x_153 = lean_ctor_get(x_29, 4);
x_154 = lean_ctor_get(x_29, 5);
x_155 = lean_ctor_get(x_29, 6);
x_156 = lean_ctor_get_uint8(x_29, sizeof(void*)*15);
x_157 = lean_ctor_get(x_29, 7);
x_158 = lean_ctor_get(x_29, 8);
x_159 = lean_ctor_get(x_29, 9);
x_160 = lean_ctor_get(x_29, 10);
x_161 = lean_ctor_get(x_29, 11);
x_162 = lean_ctor_get(x_29, 12);
x_163 = lean_ctor_get(x_29, 13);
x_164 = lean_ctor_get(x_29, 14);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_29);
x_165 = lean_ctor_get(x_30, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_30, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_30, 2);
lean_inc(x_167);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 x_168 = x_30;
} else {
 lean_dec_ref(x_30);
 x_168 = lean_box(0);
}
lean_inc(x_4);
lean_inc(x_3);
x_169 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_166, x_3, x_4);
if (lean_is_scalar(x_168)) {
 x_170 = lean_alloc_ctor(0, 3, 0);
} else {
 x_170 = x_168;
}
lean_ctor_set(x_170, 0, x_165);
lean_ctor_set(x_170, 1, x_169);
lean_ctor_set(x_170, 2, x_167);
x_171 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_171, 0, x_150);
lean_ctor_set(x_171, 1, x_170);
lean_ctor_set(x_171, 2, x_151);
lean_ctor_set(x_171, 3, x_152);
lean_ctor_set(x_171, 4, x_153);
lean_ctor_set(x_171, 5, x_154);
lean_ctor_set(x_171, 6, x_155);
lean_ctor_set(x_171, 7, x_157);
lean_ctor_set(x_171, 8, x_158);
lean_ctor_set(x_171, 9, x_159);
lean_ctor_set(x_171, 10, x_160);
lean_ctor_set(x_171, 11, x_161);
lean_ctor_set(x_171, 12, x_162);
lean_ctor_set(x_171, 13, x_163);
lean_ctor_set(x_171, 14, x_164);
lean_ctor_set_uint8(x_171, sizeof(void*)*15, x_156);
x_172 = lean_st_ref_set(x_7, x_171, x_32);
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_174 = x_172;
} else {
 lean_dec_ref(x_172);
 x_174 = lean_box(0);
}
x_175 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__4;
x_176 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_175, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_173);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_unbox(x_177);
lean_dec(x_177);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_174);
lean_free_object(x_28);
lean_dec(x_3);
x_179 = lean_ctor_get(x_176, 1);
lean_inc(x_179);
lean_dec(x_176);
x_180 = lean_box(0);
x_181 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_4, x_180, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_179);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_176, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_183 = x_176;
} else {
 lean_dec_ref(x_176);
 x_183 = lean_box(0);
}
x_184 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_182);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_185 = lean_ctor_get(x_184, 1);
lean_inc(x_185);
lean_dec(x_184);
x_186 = l_Lean_MessageData_ofExpr(x_3);
x_187 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__6;
if (lean_is_scalar(x_183)) {
 x_188 = lean_alloc_ctor(7, 2, 0);
} else {
 x_188 = x_183;
 lean_ctor_set_tag(x_188, 7);
}
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_186);
x_189 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__8;
if (lean_is_scalar(x_174)) {
 x_190 = lean_alloc_ctor(7, 2, 0);
} else {
 x_190 = x_174;
 lean_ctor_set_tag(x_190, 7);
}
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
lean_inc(x_4);
x_191 = l_Lean_MessageData_ofExpr(x_4);
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_191);
lean_ctor_set(x_28, 0, x_190);
x_192 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10;
x_193 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_193, 0, x_28);
lean_ctor_set(x_193, 1, x_192);
x_194 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_175, x_193, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_185);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_4, x_195, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_196);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_195);
return x_197;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_183);
lean_dec(x_174);
lean_free_object(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_198 = lean_ctor_get(x_184, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_184, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_200 = x_184;
} else {
 lean_dec_ref(x_184);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_202 = lean_ctor_get(x_28, 1);
lean_inc(x_202);
lean_dec(x_28);
x_203 = lean_ctor_get(x_29, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_29, 2);
lean_inc(x_204);
x_205 = lean_ctor_get(x_29, 3);
lean_inc(x_205);
x_206 = lean_ctor_get(x_29, 4);
lean_inc(x_206);
x_207 = lean_ctor_get(x_29, 5);
lean_inc(x_207);
x_208 = lean_ctor_get(x_29, 6);
lean_inc(x_208);
x_209 = lean_ctor_get_uint8(x_29, sizeof(void*)*15);
x_210 = lean_ctor_get(x_29, 7);
lean_inc(x_210);
x_211 = lean_ctor_get(x_29, 8);
lean_inc(x_211);
x_212 = lean_ctor_get(x_29, 9);
lean_inc(x_212);
x_213 = lean_ctor_get(x_29, 10);
lean_inc(x_213);
x_214 = lean_ctor_get(x_29, 11);
lean_inc(x_214);
x_215 = lean_ctor_get(x_29, 12);
lean_inc(x_215);
x_216 = lean_ctor_get(x_29, 13);
lean_inc(x_216);
x_217 = lean_ctor_get(x_29, 14);
lean_inc(x_217);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 lean_ctor_release(x_29, 2);
 lean_ctor_release(x_29, 3);
 lean_ctor_release(x_29, 4);
 lean_ctor_release(x_29, 5);
 lean_ctor_release(x_29, 6);
 lean_ctor_release(x_29, 7);
 lean_ctor_release(x_29, 8);
 lean_ctor_release(x_29, 9);
 lean_ctor_release(x_29, 10);
 lean_ctor_release(x_29, 11);
 lean_ctor_release(x_29, 12);
 lean_ctor_release(x_29, 13);
 lean_ctor_release(x_29, 14);
 x_218 = x_29;
} else {
 lean_dec_ref(x_29);
 x_218 = lean_box(0);
}
x_219 = lean_ctor_get(x_30, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_30, 1);
lean_inc(x_220);
x_221 = lean_ctor_get(x_30, 2);
lean_inc(x_221);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 x_222 = x_30;
} else {
 lean_dec_ref(x_30);
 x_222 = lean_box(0);
}
lean_inc(x_4);
lean_inc(x_3);
x_223 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_220, x_3, x_4);
if (lean_is_scalar(x_222)) {
 x_224 = lean_alloc_ctor(0, 3, 0);
} else {
 x_224 = x_222;
}
lean_ctor_set(x_224, 0, x_219);
lean_ctor_set(x_224, 1, x_223);
lean_ctor_set(x_224, 2, x_221);
if (lean_is_scalar(x_218)) {
 x_225 = lean_alloc_ctor(0, 15, 1);
} else {
 x_225 = x_218;
}
lean_ctor_set(x_225, 0, x_203);
lean_ctor_set(x_225, 1, x_224);
lean_ctor_set(x_225, 2, x_204);
lean_ctor_set(x_225, 3, x_205);
lean_ctor_set(x_225, 4, x_206);
lean_ctor_set(x_225, 5, x_207);
lean_ctor_set(x_225, 6, x_208);
lean_ctor_set(x_225, 7, x_210);
lean_ctor_set(x_225, 8, x_211);
lean_ctor_set(x_225, 9, x_212);
lean_ctor_set(x_225, 10, x_213);
lean_ctor_set(x_225, 11, x_214);
lean_ctor_set(x_225, 12, x_215);
lean_ctor_set(x_225, 13, x_216);
lean_ctor_set(x_225, 14, x_217);
lean_ctor_set_uint8(x_225, sizeof(void*)*15, x_209);
x_226 = lean_st_ref_set(x_7, x_225, x_202);
x_227 = lean_ctor_get(x_226, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_228 = x_226;
} else {
 lean_dec_ref(x_226);
 x_228 = lean_box(0);
}
x_229 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__4;
x_230 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_229, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_227);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_unbox(x_231);
lean_dec(x_231);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_228);
lean_dec(x_3);
x_233 = lean_ctor_get(x_230, 1);
lean_inc(x_233);
lean_dec(x_230);
x_234 = lean_box(0);
x_235 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_4, x_234, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_233);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_230, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_237 = x_230;
} else {
 lean_dec_ref(x_230);
 x_237 = lean_box(0);
}
x_238 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_236);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
lean_dec(x_238);
x_240 = l_Lean_MessageData_ofExpr(x_3);
x_241 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__6;
if (lean_is_scalar(x_237)) {
 x_242 = lean_alloc_ctor(7, 2, 0);
} else {
 x_242 = x_237;
 lean_ctor_set_tag(x_242, 7);
}
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_240);
x_243 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__8;
if (lean_is_scalar(x_228)) {
 x_244 = lean_alloc_ctor(7, 2, 0);
} else {
 x_244 = x_228;
 lean_ctor_set_tag(x_244, 7);
}
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
lean_inc(x_4);
x_245 = l_Lean_MessageData_ofExpr(x_4);
x_246 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
x_247 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10;
x_248 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
x_249 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_229, x_248, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_239);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_4, x_250, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_251);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_250);
return x_252;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_237);
lean_dec(x_228);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_253 = lean_ctor_get(x_238, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_238, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_255 = x_238;
} else {
 lean_dec_ref(x_238);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_253);
lean_ctor_set(x_256, 1, x_254);
return x_256;
}
}
}
}
}
else
{
uint8_t x_257; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_257 = !lean_is_exclusive(x_18);
if (x_257 == 0)
{
return x_18;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_18, 0);
x_259 = lean_ctor_get(x_18, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_18);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
return x_260;
}
}
}
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("found ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_32; uint8_t x_33; 
lean_dec(x_10);
x_22 = lean_ctor_get(x_9, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_24 = x_9;
} else {
 lean_dec_ref(x_9);
 x_24 = lean_box(0);
}
x_32 = lean_ctor_get(x_16, 0);
lean_inc(x_32);
x_33 = !lean_is_exclusive(x_22);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint64_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_34 = lean_ctor_get(x_22, 0);
x_35 = lean_ctor_get(x_22, 1);
x_36 = lean_ctor_get_uint64(x_16, sizeof(void*)*7);
x_37 = lean_ctor_get_uint8(x_16, sizeof(void*)*7 + 8);
x_38 = lean_ctor_get(x_16, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_16, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_16, 3);
lean_inc(x_40);
x_41 = lean_ctor_get(x_16, 4);
lean_inc(x_41);
x_42 = lean_ctor_get(x_16, 5);
lean_inc(x_42);
x_43 = lean_ctor_get(x_16, 6);
lean_inc(x_43);
x_44 = !lean_is_exclusive(x_32);
if (x_44 == 0)
{
uint8_t x_45; uint8_t x_46; uint8_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; lean_object* x_53; lean_object* x_54; 
x_45 = lean_ctor_get_uint8(x_16, sizeof(void*)*7 + 9);
x_46 = lean_ctor_get_uint8(x_16, sizeof(void*)*7 + 10);
x_47 = 1;
lean_ctor_set_uint8(x_32, 9, x_47);
x_48 = 2;
x_49 = lean_uint64_shift_right(x_36, x_48);
x_50 = lean_uint64_shift_left(x_49, x_48);
x_51 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__3___closed__1;
x_52 = lean_uint64_lor(x_50, x_51);
x_53 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_53, 0, x_32);
lean_ctor_set(x_53, 1, x_38);
lean_ctor_set(x_53, 2, x_39);
lean_ctor_set(x_53, 3, x_40);
lean_ctor_set(x_53, 4, x_41);
lean_ctor_set(x_53, 5, x_42);
lean_ctor_set(x_53, 6, x_43);
lean_ctor_set_uint64(x_53, sizeof(void*)*7, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*7 + 8, x_37);
lean_ctor_set_uint8(x_53, sizeof(void*)*7 + 9, x_45);
lean_ctor_set_uint8(x_53, sizeof(void*)*7 + 10, x_46);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_4);
x_54 = l_Lean_Meta_isExprDefEq(x_4, x_35, x_53, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_free_object(x_22);
lean_dec(x_34);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
lean_inc(x_6);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_6);
x_25 = x_58;
x_26 = x_57;
goto block_31;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_dec(x_54);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_34);
lean_inc(x_2);
x_60 = l_Lean_Meta_isExprDefEq(x_2, x_34, x_16, x_17, x_18, x_19, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_free_object(x_22);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_box(0);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_6);
x_65 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2(x_3, x_6, x_2, x_34, x_1, x_64, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_63);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_25 = x_66;
x_26 = x_67;
goto block_31;
}
else
{
uint8_t x_68; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_65);
if (x_68 == 0)
{
return x_65;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_65, 0);
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_65);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_72 = lean_ctor_get(x_60, 1);
lean_inc(x_72);
lean_dec(x_60);
x_73 = lean_st_ref_take(x_12, x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
x_76 = !lean_is_exclusive(x_73);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_73, 1);
x_78 = lean_ctor_get(x_73, 0);
lean_dec(x_78);
x_79 = !lean_is_exclusive(x_74);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_74, 1);
lean_dec(x_80);
x_81 = !lean_is_exclusive(x_75);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_75, 1);
lean_inc(x_34);
lean_inc(x_2);
x_83 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_82, x_2, x_34);
lean_ctor_set(x_75, 1, x_83);
x_84 = lean_st_ref_set(x_12, x_74, x_77);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_86 = lean_ctor_get(x_84, 1);
x_87 = lean_ctor_get(x_84, 0);
lean_dec(x_87);
x_88 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__4;
x_89 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_88, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_86);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_unbox(x_90);
lean_dec(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_free_object(x_84);
lean_free_object(x_73);
lean_free_object(x_22);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_93 = lean_box(0);
x_94 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_34, x_93, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_92);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_25 = x_95;
x_26 = x_96;
goto block_31;
}
else
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_89);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_89, 1);
x_99 = lean_ctor_get(x_89, 0);
lean_dec(x_99);
x_100 = l_Lean_Meta_Grind_updateLastTag(x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_98);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
lean_inc(x_2);
x_102 = l_Lean_MessageData_ofExpr(x_2);
x_103 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___closed__2;
lean_ctor_set_tag(x_89, 7);
lean_ctor_set(x_89, 1, x_102);
lean_ctor_set(x_89, 0, x_103);
x_104 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__8;
lean_ctor_set_tag(x_84, 7);
lean_ctor_set(x_84, 1, x_104);
lean_ctor_set(x_84, 0, x_89);
lean_inc(x_34);
x_105 = l_Lean_MessageData_ofExpr(x_34);
lean_ctor_set_tag(x_73, 7);
lean_ctor_set(x_73, 1, x_105);
lean_ctor_set(x_73, 0, x_84);
x_106 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_106);
lean_ctor_set(x_22, 0, x_73);
x_107 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_88, x_22, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_101);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_34, x_108, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_109);
lean_dec(x_108);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_25 = x_111;
x_26 = x_112;
goto block_31;
}
else
{
uint8_t x_113; 
lean_free_object(x_89);
lean_free_object(x_84);
lean_free_object(x_73);
lean_free_object(x_22);
lean_dec(x_34);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_100);
if (x_113 == 0)
{
return x_100;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_100, 0);
x_115 = lean_ctor_get(x_100, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_100);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_89, 1);
lean_inc(x_117);
lean_dec(x_89);
x_118 = l_Lean_Meta_Grind_updateLastTag(x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_117);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
lean_inc(x_2);
x_120 = l_Lean_MessageData_ofExpr(x_2);
x_121 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___closed__2;
x_122 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
x_123 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__8;
lean_ctor_set_tag(x_84, 7);
lean_ctor_set(x_84, 1, x_123);
lean_ctor_set(x_84, 0, x_122);
lean_inc(x_34);
x_124 = l_Lean_MessageData_ofExpr(x_34);
lean_ctor_set_tag(x_73, 7);
lean_ctor_set(x_73, 1, x_124);
lean_ctor_set(x_73, 0, x_84);
x_125 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_125);
lean_ctor_set(x_22, 0, x_73);
x_126 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_88, x_22, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_119);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_34, x_127, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_128);
lean_dec(x_127);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_25 = x_130;
x_26 = x_131;
goto block_31;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_free_object(x_84);
lean_free_object(x_73);
lean_free_object(x_22);
lean_dec(x_34);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_132 = lean_ctor_get(x_118, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_118, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_134 = x_118;
} else {
 lean_dec_ref(x_118);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_136 = lean_ctor_get(x_84, 1);
lean_inc(x_136);
lean_dec(x_84);
x_137 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__4;
x_138 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_137, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_136);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_unbox(x_139);
lean_dec(x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_free_object(x_73);
lean_free_object(x_22);
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec(x_138);
x_142 = lean_box(0);
x_143 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_34, x_142, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_141);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_25 = x_144;
x_26 = x_145;
goto block_31;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_138, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_147 = x_138;
} else {
 lean_dec_ref(x_138);
 x_147 = lean_box(0);
}
x_148 = l_Lean_Meta_Grind_updateLastTag(x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_146);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec(x_148);
lean_inc(x_2);
x_150 = l_Lean_MessageData_ofExpr(x_2);
x_151 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___closed__2;
if (lean_is_scalar(x_147)) {
 x_152 = lean_alloc_ctor(7, 2, 0);
} else {
 x_152 = x_147;
 lean_ctor_set_tag(x_152, 7);
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_150);
x_153 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__8;
x_154 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
lean_inc(x_34);
x_155 = l_Lean_MessageData_ofExpr(x_34);
lean_ctor_set_tag(x_73, 7);
lean_ctor_set(x_73, 1, x_155);
lean_ctor_set(x_73, 0, x_154);
x_156 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_156);
lean_ctor_set(x_22, 0, x_73);
x_157 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_137, x_22, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_149);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_34, x_158, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_159);
lean_dec(x_158);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_25 = x_161;
x_26 = x_162;
goto block_31;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_147);
lean_free_object(x_73);
lean_free_object(x_22);
lean_dec(x_34);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_163 = lean_ctor_get(x_148, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_148, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_165 = x_148;
} else {
 lean_dec_ref(x_148);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_167 = lean_ctor_get(x_75, 0);
x_168 = lean_ctor_get(x_75, 1);
x_169 = lean_ctor_get(x_75, 2);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_75);
lean_inc(x_34);
lean_inc(x_2);
x_170 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_168, x_2, x_34);
x_171 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_171, 0, x_167);
lean_ctor_set(x_171, 1, x_170);
lean_ctor_set(x_171, 2, x_169);
lean_ctor_set(x_74, 1, x_171);
x_172 = lean_st_ref_set(x_12, x_74, x_77);
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_174 = x_172;
} else {
 lean_dec_ref(x_172);
 x_174 = lean_box(0);
}
x_175 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__4;
x_176 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_175, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_173);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_unbox(x_177);
lean_dec(x_177);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_174);
lean_free_object(x_73);
lean_free_object(x_22);
x_179 = lean_ctor_get(x_176, 1);
lean_inc(x_179);
lean_dec(x_176);
x_180 = lean_box(0);
x_181 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_34, x_180, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_179);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_25 = x_182;
x_26 = x_183;
goto block_31;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_176, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_185 = x_176;
} else {
 lean_dec_ref(x_176);
 x_185 = lean_box(0);
}
x_186 = l_Lean_Meta_Grind_updateLastTag(x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_184);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
lean_dec(x_186);
lean_inc(x_2);
x_188 = l_Lean_MessageData_ofExpr(x_2);
x_189 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___closed__2;
if (lean_is_scalar(x_185)) {
 x_190 = lean_alloc_ctor(7, 2, 0);
} else {
 x_190 = x_185;
 lean_ctor_set_tag(x_190, 7);
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_188);
x_191 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__8;
if (lean_is_scalar(x_174)) {
 x_192 = lean_alloc_ctor(7, 2, 0);
} else {
 x_192 = x_174;
 lean_ctor_set_tag(x_192, 7);
}
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
lean_inc(x_34);
x_193 = l_Lean_MessageData_ofExpr(x_34);
lean_ctor_set_tag(x_73, 7);
lean_ctor_set(x_73, 1, x_193);
lean_ctor_set(x_73, 0, x_192);
x_194 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_194);
lean_ctor_set(x_22, 0, x_73);
x_195 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_175, x_22, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_187);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_34, x_196, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_197);
lean_dec(x_196);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_25 = x_199;
x_26 = x_200;
goto block_31;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_185);
lean_dec(x_174);
lean_free_object(x_73);
lean_free_object(x_22);
lean_dec(x_34);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_201 = lean_ctor_get(x_186, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_186, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_203 = x_186;
} else {
 lean_dec_ref(x_186);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_205 = lean_ctor_get(x_74, 0);
x_206 = lean_ctor_get(x_74, 2);
x_207 = lean_ctor_get(x_74, 3);
x_208 = lean_ctor_get(x_74, 4);
x_209 = lean_ctor_get(x_74, 5);
x_210 = lean_ctor_get(x_74, 6);
x_211 = lean_ctor_get_uint8(x_74, sizeof(void*)*15);
x_212 = lean_ctor_get(x_74, 7);
x_213 = lean_ctor_get(x_74, 8);
x_214 = lean_ctor_get(x_74, 9);
x_215 = lean_ctor_get(x_74, 10);
x_216 = lean_ctor_get(x_74, 11);
x_217 = lean_ctor_get(x_74, 12);
x_218 = lean_ctor_get(x_74, 13);
x_219 = lean_ctor_get(x_74, 14);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_210);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_74);
x_220 = lean_ctor_get(x_75, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_75, 1);
lean_inc(x_221);
x_222 = lean_ctor_get(x_75, 2);
lean_inc(x_222);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 x_223 = x_75;
} else {
 lean_dec_ref(x_75);
 x_223 = lean_box(0);
}
lean_inc(x_34);
lean_inc(x_2);
x_224 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_221, x_2, x_34);
if (lean_is_scalar(x_223)) {
 x_225 = lean_alloc_ctor(0, 3, 0);
} else {
 x_225 = x_223;
}
lean_ctor_set(x_225, 0, x_220);
lean_ctor_set(x_225, 1, x_224);
lean_ctor_set(x_225, 2, x_222);
x_226 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_226, 0, x_205);
lean_ctor_set(x_226, 1, x_225);
lean_ctor_set(x_226, 2, x_206);
lean_ctor_set(x_226, 3, x_207);
lean_ctor_set(x_226, 4, x_208);
lean_ctor_set(x_226, 5, x_209);
lean_ctor_set(x_226, 6, x_210);
lean_ctor_set(x_226, 7, x_212);
lean_ctor_set(x_226, 8, x_213);
lean_ctor_set(x_226, 9, x_214);
lean_ctor_set(x_226, 10, x_215);
lean_ctor_set(x_226, 11, x_216);
lean_ctor_set(x_226, 12, x_217);
lean_ctor_set(x_226, 13, x_218);
lean_ctor_set(x_226, 14, x_219);
lean_ctor_set_uint8(x_226, sizeof(void*)*15, x_211);
x_227 = lean_st_ref_set(x_12, x_226, x_77);
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_229 = x_227;
} else {
 lean_dec_ref(x_227);
 x_229 = lean_box(0);
}
x_230 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__4;
x_231 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_230, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_228);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_unbox(x_232);
lean_dec(x_232);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_229);
lean_free_object(x_73);
lean_free_object(x_22);
x_234 = lean_ctor_get(x_231, 1);
lean_inc(x_234);
lean_dec(x_231);
x_235 = lean_box(0);
x_236 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_34, x_235, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_234);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
x_25 = x_237;
x_26 = x_238;
goto block_31;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_231, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_240 = x_231;
} else {
 lean_dec_ref(x_231);
 x_240 = lean_box(0);
}
x_241 = l_Lean_Meta_Grind_updateLastTag(x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_239);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
lean_dec(x_241);
lean_inc(x_2);
x_243 = l_Lean_MessageData_ofExpr(x_2);
x_244 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___closed__2;
if (lean_is_scalar(x_240)) {
 x_245 = lean_alloc_ctor(7, 2, 0);
} else {
 x_245 = x_240;
 lean_ctor_set_tag(x_245, 7);
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_243);
x_246 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__8;
if (lean_is_scalar(x_229)) {
 x_247 = lean_alloc_ctor(7, 2, 0);
} else {
 x_247 = x_229;
 lean_ctor_set_tag(x_247, 7);
}
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
lean_inc(x_34);
x_248 = l_Lean_MessageData_ofExpr(x_34);
lean_ctor_set_tag(x_73, 7);
lean_ctor_set(x_73, 1, x_248);
lean_ctor_set(x_73, 0, x_247);
x_249 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_249);
lean_ctor_set(x_22, 0, x_73);
x_250 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_230, x_22, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_242);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_34, x_251, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_252);
lean_dec(x_251);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
x_25 = x_254;
x_26 = x_255;
goto block_31;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_240);
lean_dec(x_229);
lean_free_object(x_73);
lean_free_object(x_22);
lean_dec(x_34);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_256 = lean_ctor_get(x_241, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_241, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_258 = x_241;
} else {
 lean_dec_ref(x_241);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_259 = lean_alloc_ctor(1, 2, 0);
} else {
 x_259 = x_258;
}
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_257);
return x_259;
}
}
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; 
x_260 = lean_ctor_get(x_73, 1);
lean_inc(x_260);
lean_dec(x_73);
x_261 = lean_ctor_get(x_74, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_74, 2);
lean_inc(x_262);
x_263 = lean_ctor_get(x_74, 3);
lean_inc(x_263);
x_264 = lean_ctor_get(x_74, 4);
lean_inc(x_264);
x_265 = lean_ctor_get(x_74, 5);
lean_inc(x_265);
x_266 = lean_ctor_get(x_74, 6);
lean_inc(x_266);
x_267 = lean_ctor_get_uint8(x_74, sizeof(void*)*15);
x_268 = lean_ctor_get(x_74, 7);
lean_inc(x_268);
x_269 = lean_ctor_get(x_74, 8);
lean_inc(x_269);
x_270 = lean_ctor_get(x_74, 9);
lean_inc(x_270);
x_271 = lean_ctor_get(x_74, 10);
lean_inc(x_271);
x_272 = lean_ctor_get(x_74, 11);
lean_inc(x_272);
x_273 = lean_ctor_get(x_74, 12);
lean_inc(x_273);
x_274 = lean_ctor_get(x_74, 13);
lean_inc(x_274);
x_275 = lean_ctor_get(x_74, 14);
lean_inc(x_275);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 lean_ctor_release(x_74, 4);
 lean_ctor_release(x_74, 5);
 lean_ctor_release(x_74, 6);
 lean_ctor_release(x_74, 7);
 lean_ctor_release(x_74, 8);
 lean_ctor_release(x_74, 9);
 lean_ctor_release(x_74, 10);
 lean_ctor_release(x_74, 11);
 lean_ctor_release(x_74, 12);
 lean_ctor_release(x_74, 13);
 lean_ctor_release(x_74, 14);
 x_276 = x_74;
} else {
 lean_dec_ref(x_74);
 x_276 = lean_box(0);
}
x_277 = lean_ctor_get(x_75, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_75, 1);
lean_inc(x_278);
x_279 = lean_ctor_get(x_75, 2);
lean_inc(x_279);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 x_280 = x_75;
} else {
 lean_dec_ref(x_75);
 x_280 = lean_box(0);
}
lean_inc(x_34);
lean_inc(x_2);
x_281 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_278, x_2, x_34);
if (lean_is_scalar(x_280)) {
 x_282 = lean_alloc_ctor(0, 3, 0);
} else {
 x_282 = x_280;
}
lean_ctor_set(x_282, 0, x_277);
lean_ctor_set(x_282, 1, x_281);
lean_ctor_set(x_282, 2, x_279);
if (lean_is_scalar(x_276)) {
 x_283 = lean_alloc_ctor(0, 15, 1);
} else {
 x_283 = x_276;
}
lean_ctor_set(x_283, 0, x_261);
lean_ctor_set(x_283, 1, x_282);
lean_ctor_set(x_283, 2, x_262);
lean_ctor_set(x_283, 3, x_263);
lean_ctor_set(x_283, 4, x_264);
lean_ctor_set(x_283, 5, x_265);
lean_ctor_set(x_283, 6, x_266);
lean_ctor_set(x_283, 7, x_268);
lean_ctor_set(x_283, 8, x_269);
lean_ctor_set(x_283, 9, x_270);
lean_ctor_set(x_283, 10, x_271);
lean_ctor_set(x_283, 11, x_272);
lean_ctor_set(x_283, 12, x_273);
lean_ctor_set(x_283, 13, x_274);
lean_ctor_set(x_283, 14, x_275);
lean_ctor_set_uint8(x_283, sizeof(void*)*15, x_267);
x_284 = lean_st_ref_set(x_12, x_283, x_260);
x_285 = lean_ctor_get(x_284, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_286 = x_284;
} else {
 lean_dec_ref(x_284);
 x_286 = lean_box(0);
}
x_287 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__4;
x_288 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_287, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_285);
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_unbox(x_289);
lean_dec(x_289);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec(x_286);
lean_free_object(x_22);
x_291 = lean_ctor_get(x_288, 1);
lean_inc(x_291);
lean_dec(x_288);
x_292 = lean_box(0);
x_293 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_34, x_292, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_291);
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec(x_293);
x_25 = x_294;
x_26 = x_295;
goto block_31;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_288, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_297 = x_288;
} else {
 lean_dec_ref(x_288);
 x_297 = lean_box(0);
}
x_298 = l_Lean_Meta_Grind_updateLastTag(x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_296);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_299 = lean_ctor_get(x_298, 1);
lean_inc(x_299);
lean_dec(x_298);
lean_inc(x_2);
x_300 = l_Lean_MessageData_ofExpr(x_2);
x_301 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___closed__2;
if (lean_is_scalar(x_297)) {
 x_302 = lean_alloc_ctor(7, 2, 0);
} else {
 x_302 = x_297;
 lean_ctor_set_tag(x_302, 7);
}
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_300);
x_303 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__8;
if (lean_is_scalar(x_286)) {
 x_304 = lean_alloc_ctor(7, 2, 0);
} else {
 x_304 = x_286;
 lean_ctor_set_tag(x_304, 7);
}
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
lean_inc(x_34);
x_305 = l_Lean_MessageData_ofExpr(x_34);
x_306 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
x_307 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_307);
lean_ctor_set(x_22, 0, x_306);
x_308 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_287, x_22, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_299);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
lean_dec(x_308);
x_311 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_34, x_309, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_310);
lean_dec(x_309);
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_311, 1);
lean_inc(x_313);
lean_dec(x_311);
x_25 = x_312;
x_26 = x_313;
goto block_31;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_297);
lean_dec(x_286);
lean_free_object(x_22);
lean_dec(x_34);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_314 = lean_ctor_get(x_298, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_298, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_316 = x_298;
} else {
 lean_dec_ref(x_298);
 x_316 = lean_box(0);
}
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 2, 0);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_314);
lean_ctor_set(x_317, 1, x_315);
return x_317;
}
}
}
}
}
else
{
uint8_t x_318; 
lean_free_object(x_22);
lean_dec(x_34);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_318 = !lean_is_exclusive(x_60);
if (x_318 == 0)
{
return x_60;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_60, 0);
x_320 = lean_ctor_get(x_60, 1);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_60);
x_321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set(x_321, 1, x_320);
return x_321;
}
}
}
}
else
{
uint8_t x_322; 
lean_free_object(x_22);
lean_dec(x_34);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_322 = !lean_is_exclusive(x_54);
if (x_322 == 0)
{
return x_54;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_323 = lean_ctor_get(x_54, 0);
x_324 = lean_ctor_get(x_54, 1);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_54);
x_325 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set(x_325, 1, x_324);
return x_325;
}
}
}
else
{
uint8_t x_326; uint8_t x_327; uint8_t x_328; uint8_t x_329; uint8_t x_330; uint8_t x_331; uint8_t x_332; uint8_t x_333; uint8_t x_334; uint8_t x_335; uint8_t x_336; uint8_t x_337; uint8_t x_338; uint8_t x_339; uint8_t x_340; uint8_t x_341; uint8_t x_342; uint8_t x_343; uint8_t x_344; uint8_t x_345; lean_object* x_346; uint64_t x_347; uint64_t x_348; uint64_t x_349; uint64_t x_350; uint64_t x_351; lean_object* x_352; lean_object* x_353; 
x_326 = lean_ctor_get_uint8(x_16, sizeof(void*)*7 + 9);
x_327 = lean_ctor_get_uint8(x_16, sizeof(void*)*7 + 10);
x_328 = lean_ctor_get_uint8(x_32, 0);
x_329 = lean_ctor_get_uint8(x_32, 1);
x_330 = lean_ctor_get_uint8(x_32, 2);
x_331 = lean_ctor_get_uint8(x_32, 3);
x_332 = lean_ctor_get_uint8(x_32, 4);
x_333 = lean_ctor_get_uint8(x_32, 5);
x_334 = lean_ctor_get_uint8(x_32, 6);
x_335 = lean_ctor_get_uint8(x_32, 7);
x_336 = lean_ctor_get_uint8(x_32, 8);
x_337 = lean_ctor_get_uint8(x_32, 10);
x_338 = lean_ctor_get_uint8(x_32, 11);
x_339 = lean_ctor_get_uint8(x_32, 12);
x_340 = lean_ctor_get_uint8(x_32, 13);
x_341 = lean_ctor_get_uint8(x_32, 14);
x_342 = lean_ctor_get_uint8(x_32, 15);
x_343 = lean_ctor_get_uint8(x_32, 16);
x_344 = lean_ctor_get_uint8(x_32, 17);
lean_dec(x_32);
x_345 = 1;
x_346 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_346, 0, x_328);
lean_ctor_set_uint8(x_346, 1, x_329);
lean_ctor_set_uint8(x_346, 2, x_330);
lean_ctor_set_uint8(x_346, 3, x_331);
lean_ctor_set_uint8(x_346, 4, x_332);
lean_ctor_set_uint8(x_346, 5, x_333);
lean_ctor_set_uint8(x_346, 6, x_334);
lean_ctor_set_uint8(x_346, 7, x_335);
lean_ctor_set_uint8(x_346, 8, x_336);
lean_ctor_set_uint8(x_346, 9, x_345);
lean_ctor_set_uint8(x_346, 10, x_337);
lean_ctor_set_uint8(x_346, 11, x_338);
lean_ctor_set_uint8(x_346, 12, x_339);
lean_ctor_set_uint8(x_346, 13, x_340);
lean_ctor_set_uint8(x_346, 14, x_341);
lean_ctor_set_uint8(x_346, 15, x_342);
lean_ctor_set_uint8(x_346, 16, x_343);
lean_ctor_set_uint8(x_346, 17, x_344);
x_347 = 2;
x_348 = lean_uint64_shift_right(x_36, x_347);
x_349 = lean_uint64_shift_left(x_348, x_347);
x_350 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__3___closed__1;
x_351 = lean_uint64_lor(x_349, x_350);
x_352 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_352, 0, x_346);
lean_ctor_set(x_352, 1, x_38);
lean_ctor_set(x_352, 2, x_39);
lean_ctor_set(x_352, 3, x_40);
lean_ctor_set(x_352, 4, x_41);
lean_ctor_set(x_352, 5, x_42);
lean_ctor_set(x_352, 6, x_43);
lean_ctor_set_uint64(x_352, sizeof(void*)*7, x_351);
lean_ctor_set_uint8(x_352, sizeof(void*)*7 + 8, x_37);
lean_ctor_set_uint8(x_352, sizeof(void*)*7 + 9, x_326);
lean_ctor_set_uint8(x_352, sizeof(void*)*7 + 10, x_327);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_4);
x_353 = l_Lean_Meta_isExprDefEq(x_4, x_35, x_352, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; uint8_t x_355; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_unbox(x_354);
lean_dec(x_354);
if (x_355 == 0)
{
lean_object* x_356; lean_object* x_357; 
lean_free_object(x_22);
lean_dec(x_34);
x_356 = lean_ctor_get(x_353, 1);
lean_inc(x_356);
lean_dec(x_353);
lean_inc(x_6);
x_357 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_357, 0, x_6);
x_25 = x_357;
x_26 = x_356;
goto block_31;
}
else
{
lean_object* x_358; lean_object* x_359; 
x_358 = lean_ctor_get(x_353, 1);
lean_inc(x_358);
lean_dec(x_353);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_34);
lean_inc(x_2);
x_359 = l_Lean_Meta_isExprDefEq(x_2, x_34, x_16, x_17, x_18, x_19, x_358);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; uint8_t x_361; 
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_unbox(x_360);
lean_dec(x_360);
if (x_361 == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
lean_free_object(x_22);
x_362 = lean_ctor_get(x_359, 1);
lean_inc(x_362);
lean_dec(x_359);
x_363 = lean_box(0);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_6);
x_364 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2(x_3, x_6, x_2, x_34, x_1, x_363, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_362);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
lean_dec(x_364);
x_25 = x_365;
x_26 = x_366;
goto block_31;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_367 = lean_ctor_get(x_364, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_364, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_369 = x_364;
} else {
 lean_dec_ref(x_364);
 x_369 = lean_box(0);
}
if (lean_is_scalar(x_369)) {
 x_370 = lean_alloc_ctor(1, 2, 0);
} else {
 x_370 = x_369;
}
lean_ctor_set(x_370, 0, x_367);
lean_ctor_set(x_370, 1, x_368);
return x_370;
}
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; 
x_371 = lean_ctor_get(x_359, 1);
lean_inc(x_371);
lean_dec(x_359);
x_372 = lean_st_ref_take(x_12, x_371);
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_373, 1);
lean_inc(x_374);
x_375 = lean_ctor_get(x_372, 1);
lean_inc(x_375);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 x_376 = x_372;
} else {
 lean_dec_ref(x_372);
 x_376 = lean_box(0);
}
x_377 = lean_ctor_get(x_373, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_373, 2);
lean_inc(x_378);
x_379 = lean_ctor_get(x_373, 3);
lean_inc(x_379);
x_380 = lean_ctor_get(x_373, 4);
lean_inc(x_380);
x_381 = lean_ctor_get(x_373, 5);
lean_inc(x_381);
x_382 = lean_ctor_get(x_373, 6);
lean_inc(x_382);
x_383 = lean_ctor_get_uint8(x_373, sizeof(void*)*15);
x_384 = lean_ctor_get(x_373, 7);
lean_inc(x_384);
x_385 = lean_ctor_get(x_373, 8);
lean_inc(x_385);
x_386 = lean_ctor_get(x_373, 9);
lean_inc(x_386);
x_387 = lean_ctor_get(x_373, 10);
lean_inc(x_387);
x_388 = lean_ctor_get(x_373, 11);
lean_inc(x_388);
x_389 = lean_ctor_get(x_373, 12);
lean_inc(x_389);
x_390 = lean_ctor_get(x_373, 13);
lean_inc(x_390);
x_391 = lean_ctor_get(x_373, 14);
lean_inc(x_391);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 lean_ctor_release(x_373, 2);
 lean_ctor_release(x_373, 3);
 lean_ctor_release(x_373, 4);
 lean_ctor_release(x_373, 5);
 lean_ctor_release(x_373, 6);
 lean_ctor_release(x_373, 7);
 lean_ctor_release(x_373, 8);
 lean_ctor_release(x_373, 9);
 lean_ctor_release(x_373, 10);
 lean_ctor_release(x_373, 11);
 lean_ctor_release(x_373, 12);
 lean_ctor_release(x_373, 13);
 lean_ctor_release(x_373, 14);
 x_392 = x_373;
} else {
 lean_dec_ref(x_373);
 x_392 = lean_box(0);
}
x_393 = lean_ctor_get(x_374, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_374, 1);
lean_inc(x_394);
x_395 = lean_ctor_get(x_374, 2);
lean_inc(x_395);
if (lean_is_exclusive(x_374)) {
 lean_ctor_release(x_374, 0);
 lean_ctor_release(x_374, 1);
 lean_ctor_release(x_374, 2);
 x_396 = x_374;
} else {
 lean_dec_ref(x_374);
 x_396 = lean_box(0);
}
lean_inc(x_34);
lean_inc(x_2);
x_397 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_394, x_2, x_34);
if (lean_is_scalar(x_396)) {
 x_398 = lean_alloc_ctor(0, 3, 0);
} else {
 x_398 = x_396;
}
lean_ctor_set(x_398, 0, x_393);
lean_ctor_set(x_398, 1, x_397);
lean_ctor_set(x_398, 2, x_395);
if (lean_is_scalar(x_392)) {
 x_399 = lean_alloc_ctor(0, 15, 1);
} else {
 x_399 = x_392;
}
lean_ctor_set(x_399, 0, x_377);
lean_ctor_set(x_399, 1, x_398);
lean_ctor_set(x_399, 2, x_378);
lean_ctor_set(x_399, 3, x_379);
lean_ctor_set(x_399, 4, x_380);
lean_ctor_set(x_399, 5, x_381);
lean_ctor_set(x_399, 6, x_382);
lean_ctor_set(x_399, 7, x_384);
lean_ctor_set(x_399, 8, x_385);
lean_ctor_set(x_399, 9, x_386);
lean_ctor_set(x_399, 10, x_387);
lean_ctor_set(x_399, 11, x_388);
lean_ctor_set(x_399, 12, x_389);
lean_ctor_set(x_399, 13, x_390);
lean_ctor_set(x_399, 14, x_391);
lean_ctor_set_uint8(x_399, sizeof(void*)*15, x_383);
x_400 = lean_st_ref_set(x_12, x_399, x_375);
x_401 = lean_ctor_get(x_400, 1);
lean_inc(x_401);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 lean_ctor_release(x_400, 1);
 x_402 = x_400;
} else {
 lean_dec_ref(x_400);
 x_402 = lean_box(0);
}
x_403 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__4;
x_404 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_403, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_401);
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_unbox(x_405);
lean_dec(x_405);
if (x_406 == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_dec(x_402);
lean_dec(x_376);
lean_free_object(x_22);
x_407 = lean_ctor_get(x_404, 1);
lean_inc(x_407);
lean_dec(x_404);
x_408 = lean_box(0);
x_409 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_34, x_408, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_407);
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
lean_dec(x_409);
x_25 = x_410;
x_26 = x_411;
goto block_31;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_412 = lean_ctor_get(x_404, 1);
lean_inc(x_412);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 x_413 = x_404;
} else {
 lean_dec_ref(x_404);
 x_413 = lean_box(0);
}
x_414 = l_Lean_Meta_Grind_updateLastTag(x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_412);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_415 = lean_ctor_get(x_414, 1);
lean_inc(x_415);
lean_dec(x_414);
lean_inc(x_2);
x_416 = l_Lean_MessageData_ofExpr(x_2);
x_417 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___closed__2;
if (lean_is_scalar(x_413)) {
 x_418 = lean_alloc_ctor(7, 2, 0);
} else {
 x_418 = x_413;
 lean_ctor_set_tag(x_418, 7);
}
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_416);
x_419 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__8;
if (lean_is_scalar(x_402)) {
 x_420 = lean_alloc_ctor(7, 2, 0);
} else {
 x_420 = x_402;
 lean_ctor_set_tag(x_420, 7);
}
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_419);
lean_inc(x_34);
x_421 = l_Lean_MessageData_ofExpr(x_34);
if (lean_is_scalar(x_376)) {
 x_422 = lean_alloc_ctor(7, 2, 0);
} else {
 x_422 = x_376;
 lean_ctor_set_tag(x_422, 7);
}
lean_ctor_set(x_422, 0, x_420);
lean_ctor_set(x_422, 1, x_421);
x_423 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_423);
lean_ctor_set(x_22, 0, x_422);
x_424 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_403, x_22, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_415);
x_425 = lean_ctor_get(x_424, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_424, 1);
lean_inc(x_426);
lean_dec(x_424);
x_427 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_34, x_425, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_426);
lean_dec(x_425);
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_427, 1);
lean_inc(x_429);
lean_dec(x_427);
x_25 = x_428;
x_26 = x_429;
goto block_31;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
lean_dec(x_413);
lean_dec(x_402);
lean_dec(x_376);
lean_free_object(x_22);
lean_dec(x_34);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_430 = lean_ctor_get(x_414, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_414, 1);
lean_inc(x_431);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_432 = x_414;
} else {
 lean_dec_ref(x_414);
 x_432 = lean_box(0);
}
if (lean_is_scalar(x_432)) {
 x_433 = lean_alloc_ctor(1, 2, 0);
} else {
 x_433 = x_432;
}
lean_ctor_set(x_433, 0, x_430);
lean_ctor_set(x_433, 1, x_431);
return x_433;
}
}
}
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
lean_free_object(x_22);
lean_dec(x_34);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_434 = lean_ctor_get(x_359, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_359, 1);
lean_inc(x_435);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_436 = x_359;
} else {
 lean_dec_ref(x_359);
 x_436 = lean_box(0);
}
if (lean_is_scalar(x_436)) {
 x_437 = lean_alloc_ctor(1, 2, 0);
} else {
 x_437 = x_436;
}
lean_ctor_set(x_437, 0, x_434);
lean_ctor_set(x_437, 1, x_435);
return x_437;
}
}
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_free_object(x_22);
lean_dec(x_34);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_438 = lean_ctor_get(x_353, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_353, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 x_440 = x_353;
} else {
 lean_dec_ref(x_353);
 x_440 = lean_box(0);
}
if (lean_is_scalar(x_440)) {
 x_441 = lean_alloc_ctor(1, 2, 0);
} else {
 x_441 = x_440;
}
lean_ctor_set(x_441, 0, x_438);
lean_ctor_set(x_441, 1, x_439);
return x_441;
}
}
}
else
{
lean_object* x_442; lean_object* x_443; uint64_t x_444; uint8_t x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; uint8_t x_452; uint8_t x_453; uint8_t x_454; uint8_t x_455; uint8_t x_456; uint8_t x_457; uint8_t x_458; uint8_t x_459; uint8_t x_460; uint8_t x_461; uint8_t x_462; uint8_t x_463; uint8_t x_464; uint8_t x_465; uint8_t x_466; uint8_t x_467; uint8_t x_468; uint8_t x_469; uint8_t x_470; lean_object* x_471; uint8_t x_472; lean_object* x_473; uint64_t x_474; uint64_t x_475; uint64_t x_476; uint64_t x_477; uint64_t x_478; lean_object* x_479; lean_object* x_480; 
x_442 = lean_ctor_get(x_22, 0);
x_443 = lean_ctor_get(x_22, 1);
lean_inc(x_443);
lean_inc(x_442);
lean_dec(x_22);
x_444 = lean_ctor_get_uint64(x_16, sizeof(void*)*7);
x_445 = lean_ctor_get_uint8(x_16, sizeof(void*)*7 + 8);
x_446 = lean_ctor_get(x_16, 1);
lean_inc(x_446);
x_447 = lean_ctor_get(x_16, 2);
lean_inc(x_447);
x_448 = lean_ctor_get(x_16, 3);
lean_inc(x_448);
x_449 = lean_ctor_get(x_16, 4);
lean_inc(x_449);
x_450 = lean_ctor_get(x_16, 5);
lean_inc(x_450);
x_451 = lean_ctor_get(x_16, 6);
lean_inc(x_451);
x_452 = lean_ctor_get_uint8(x_16, sizeof(void*)*7 + 9);
x_453 = lean_ctor_get_uint8(x_16, sizeof(void*)*7 + 10);
x_454 = lean_ctor_get_uint8(x_32, 0);
x_455 = lean_ctor_get_uint8(x_32, 1);
x_456 = lean_ctor_get_uint8(x_32, 2);
x_457 = lean_ctor_get_uint8(x_32, 3);
x_458 = lean_ctor_get_uint8(x_32, 4);
x_459 = lean_ctor_get_uint8(x_32, 5);
x_460 = lean_ctor_get_uint8(x_32, 6);
x_461 = lean_ctor_get_uint8(x_32, 7);
x_462 = lean_ctor_get_uint8(x_32, 8);
x_463 = lean_ctor_get_uint8(x_32, 10);
x_464 = lean_ctor_get_uint8(x_32, 11);
x_465 = lean_ctor_get_uint8(x_32, 12);
x_466 = lean_ctor_get_uint8(x_32, 13);
x_467 = lean_ctor_get_uint8(x_32, 14);
x_468 = lean_ctor_get_uint8(x_32, 15);
x_469 = lean_ctor_get_uint8(x_32, 16);
x_470 = lean_ctor_get_uint8(x_32, 17);
if (lean_is_exclusive(x_32)) {
 x_471 = x_32;
} else {
 lean_dec_ref(x_32);
 x_471 = lean_box(0);
}
x_472 = 1;
if (lean_is_scalar(x_471)) {
 x_473 = lean_alloc_ctor(0, 0, 18);
} else {
 x_473 = x_471;
}
lean_ctor_set_uint8(x_473, 0, x_454);
lean_ctor_set_uint8(x_473, 1, x_455);
lean_ctor_set_uint8(x_473, 2, x_456);
lean_ctor_set_uint8(x_473, 3, x_457);
lean_ctor_set_uint8(x_473, 4, x_458);
lean_ctor_set_uint8(x_473, 5, x_459);
lean_ctor_set_uint8(x_473, 6, x_460);
lean_ctor_set_uint8(x_473, 7, x_461);
lean_ctor_set_uint8(x_473, 8, x_462);
lean_ctor_set_uint8(x_473, 9, x_472);
lean_ctor_set_uint8(x_473, 10, x_463);
lean_ctor_set_uint8(x_473, 11, x_464);
lean_ctor_set_uint8(x_473, 12, x_465);
lean_ctor_set_uint8(x_473, 13, x_466);
lean_ctor_set_uint8(x_473, 14, x_467);
lean_ctor_set_uint8(x_473, 15, x_468);
lean_ctor_set_uint8(x_473, 16, x_469);
lean_ctor_set_uint8(x_473, 17, x_470);
x_474 = 2;
x_475 = lean_uint64_shift_right(x_444, x_474);
x_476 = lean_uint64_shift_left(x_475, x_474);
x_477 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__3___closed__1;
x_478 = lean_uint64_lor(x_476, x_477);
x_479 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_479, 0, x_473);
lean_ctor_set(x_479, 1, x_446);
lean_ctor_set(x_479, 2, x_447);
lean_ctor_set(x_479, 3, x_448);
lean_ctor_set(x_479, 4, x_449);
lean_ctor_set(x_479, 5, x_450);
lean_ctor_set(x_479, 6, x_451);
lean_ctor_set_uint64(x_479, sizeof(void*)*7, x_478);
lean_ctor_set_uint8(x_479, sizeof(void*)*7 + 8, x_445);
lean_ctor_set_uint8(x_479, sizeof(void*)*7 + 9, x_452);
lean_ctor_set_uint8(x_479, sizeof(void*)*7 + 10, x_453);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_4);
x_480 = l_Lean_Meta_isExprDefEq(x_4, x_443, x_479, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_480) == 0)
{
lean_object* x_481; uint8_t x_482; 
x_481 = lean_ctor_get(x_480, 0);
lean_inc(x_481);
x_482 = lean_unbox(x_481);
lean_dec(x_481);
if (x_482 == 0)
{
lean_object* x_483; lean_object* x_484; 
lean_dec(x_442);
x_483 = lean_ctor_get(x_480, 1);
lean_inc(x_483);
lean_dec(x_480);
lean_inc(x_6);
x_484 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_484, 0, x_6);
x_25 = x_484;
x_26 = x_483;
goto block_31;
}
else
{
lean_object* x_485; lean_object* x_486; 
x_485 = lean_ctor_get(x_480, 1);
lean_inc(x_485);
lean_dec(x_480);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_442);
lean_inc(x_2);
x_486 = l_Lean_Meta_isExprDefEq(x_2, x_442, x_16, x_17, x_18, x_19, x_485);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; uint8_t x_488; 
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
x_488 = lean_unbox(x_487);
lean_dec(x_487);
if (x_488 == 0)
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_489 = lean_ctor_get(x_486, 1);
lean_inc(x_489);
lean_dec(x_486);
x_490 = lean_box(0);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_6);
x_491 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2(x_3, x_6, x_2, x_442, x_1, x_490, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_489);
if (lean_obj_tag(x_491) == 0)
{
lean_object* x_492; lean_object* x_493; 
x_492 = lean_ctor_get(x_491, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_491, 1);
lean_inc(x_493);
lean_dec(x_491);
x_25 = x_492;
x_26 = x_493;
goto block_31;
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_494 = lean_ctor_get(x_491, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_491, 1);
lean_inc(x_495);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 x_496 = x_491;
} else {
 lean_dec_ref(x_491);
 x_496 = lean_box(0);
}
if (lean_is_scalar(x_496)) {
 x_497 = lean_alloc_ctor(1, 2, 0);
} else {
 x_497 = x_496;
}
lean_ctor_set(x_497, 0, x_494);
lean_ctor_set(x_497, 1, x_495);
return x_497;
}
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; uint8_t x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; uint8_t x_533; 
x_498 = lean_ctor_get(x_486, 1);
lean_inc(x_498);
lean_dec(x_486);
x_499 = lean_st_ref_take(x_12, x_498);
x_500 = lean_ctor_get(x_499, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_500, 1);
lean_inc(x_501);
x_502 = lean_ctor_get(x_499, 1);
lean_inc(x_502);
if (lean_is_exclusive(x_499)) {
 lean_ctor_release(x_499, 0);
 lean_ctor_release(x_499, 1);
 x_503 = x_499;
} else {
 lean_dec_ref(x_499);
 x_503 = lean_box(0);
}
x_504 = lean_ctor_get(x_500, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_500, 2);
lean_inc(x_505);
x_506 = lean_ctor_get(x_500, 3);
lean_inc(x_506);
x_507 = lean_ctor_get(x_500, 4);
lean_inc(x_507);
x_508 = lean_ctor_get(x_500, 5);
lean_inc(x_508);
x_509 = lean_ctor_get(x_500, 6);
lean_inc(x_509);
x_510 = lean_ctor_get_uint8(x_500, sizeof(void*)*15);
x_511 = lean_ctor_get(x_500, 7);
lean_inc(x_511);
x_512 = lean_ctor_get(x_500, 8);
lean_inc(x_512);
x_513 = lean_ctor_get(x_500, 9);
lean_inc(x_513);
x_514 = lean_ctor_get(x_500, 10);
lean_inc(x_514);
x_515 = lean_ctor_get(x_500, 11);
lean_inc(x_515);
x_516 = lean_ctor_get(x_500, 12);
lean_inc(x_516);
x_517 = lean_ctor_get(x_500, 13);
lean_inc(x_517);
x_518 = lean_ctor_get(x_500, 14);
lean_inc(x_518);
if (lean_is_exclusive(x_500)) {
 lean_ctor_release(x_500, 0);
 lean_ctor_release(x_500, 1);
 lean_ctor_release(x_500, 2);
 lean_ctor_release(x_500, 3);
 lean_ctor_release(x_500, 4);
 lean_ctor_release(x_500, 5);
 lean_ctor_release(x_500, 6);
 lean_ctor_release(x_500, 7);
 lean_ctor_release(x_500, 8);
 lean_ctor_release(x_500, 9);
 lean_ctor_release(x_500, 10);
 lean_ctor_release(x_500, 11);
 lean_ctor_release(x_500, 12);
 lean_ctor_release(x_500, 13);
 lean_ctor_release(x_500, 14);
 x_519 = x_500;
} else {
 lean_dec_ref(x_500);
 x_519 = lean_box(0);
}
x_520 = lean_ctor_get(x_501, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_501, 1);
lean_inc(x_521);
x_522 = lean_ctor_get(x_501, 2);
lean_inc(x_522);
if (lean_is_exclusive(x_501)) {
 lean_ctor_release(x_501, 0);
 lean_ctor_release(x_501, 1);
 lean_ctor_release(x_501, 2);
 x_523 = x_501;
} else {
 lean_dec_ref(x_501);
 x_523 = lean_box(0);
}
lean_inc(x_442);
lean_inc(x_2);
x_524 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_521, x_2, x_442);
if (lean_is_scalar(x_523)) {
 x_525 = lean_alloc_ctor(0, 3, 0);
} else {
 x_525 = x_523;
}
lean_ctor_set(x_525, 0, x_520);
lean_ctor_set(x_525, 1, x_524);
lean_ctor_set(x_525, 2, x_522);
if (lean_is_scalar(x_519)) {
 x_526 = lean_alloc_ctor(0, 15, 1);
} else {
 x_526 = x_519;
}
lean_ctor_set(x_526, 0, x_504);
lean_ctor_set(x_526, 1, x_525);
lean_ctor_set(x_526, 2, x_505);
lean_ctor_set(x_526, 3, x_506);
lean_ctor_set(x_526, 4, x_507);
lean_ctor_set(x_526, 5, x_508);
lean_ctor_set(x_526, 6, x_509);
lean_ctor_set(x_526, 7, x_511);
lean_ctor_set(x_526, 8, x_512);
lean_ctor_set(x_526, 9, x_513);
lean_ctor_set(x_526, 10, x_514);
lean_ctor_set(x_526, 11, x_515);
lean_ctor_set(x_526, 12, x_516);
lean_ctor_set(x_526, 13, x_517);
lean_ctor_set(x_526, 14, x_518);
lean_ctor_set_uint8(x_526, sizeof(void*)*15, x_510);
x_527 = lean_st_ref_set(x_12, x_526, x_502);
x_528 = lean_ctor_get(x_527, 1);
lean_inc(x_528);
if (lean_is_exclusive(x_527)) {
 lean_ctor_release(x_527, 0);
 lean_ctor_release(x_527, 1);
 x_529 = x_527;
} else {
 lean_dec_ref(x_527);
 x_529 = lean_box(0);
}
x_530 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__4;
x_531 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_530, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_528);
x_532 = lean_ctor_get(x_531, 0);
lean_inc(x_532);
x_533 = lean_unbox(x_532);
lean_dec(x_532);
if (x_533 == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
lean_dec(x_529);
lean_dec(x_503);
x_534 = lean_ctor_get(x_531, 1);
lean_inc(x_534);
lean_dec(x_531);
x_535 = lean_box(0);
x_536 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_442, x_535, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_534);
x_537 = lean_ctor_get(x_536, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_536, 1);
lean_inc(x_538);
lean_dec(x_536);
x_25 = x_537;
x_26 = x_538;
goto block_31;
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_539 = lean_ctor_get(x_531, 1);
lean_inc(x_539);
if (lean_is_exclusive(x_531)) {
 lean_ctor_release(x_531, 0);
 lean_ctor_release(x_531, 1);
 x_540 = x_531;
} else {
 lean_dec_ref(x_531);
 x_540 = lean_box(0);
}
x_541 = l_Lean_Meta_Grind_updateLastTag(x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_539);
if (lean_obj_tag(x_541) == 0)
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_542 = lean_ctor_get(x_541, 1);
lean_inc(x_542);
lean_dec(x_541);
lean_inc(x_2);
x_543 = l_Lean_MessageData_ofExpr(x_2);
x_544 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___closed__2;
if (lean_is_scalar(x_540)) {
 x_545 = lean_alloc_ctor(7, 2, 0);
} else {
 x_545 = x_540;
 lean_ctor_set_tag(x_545, 7);
}
lean_ctor_set(x_545, 0, x_544);
lean_ctor_set(x_545, 1, x_543);
x_546 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__8;
if (lean_is_scalar(x_529)) {
 x_547 = lean_alloc_ctor(7, 2, 0);
} else {
 x_547 = x_529;
 lean_ctor_set_tag(x_547, 7);
}
lean_ctor_set(x_547, 0, x_545);
lean_ctor_set(x_547, 1, x_546);
lean_inc(x_442);
x_548 = l_Lean_MessageData_ofExpr(x_442);
if (lean_is_scalar(x_503)) {
 x_549 = lean_alloc_ctor(7, 2, 0);
} else {
 x_549 = x_503;
 lean_ctor_set_tag(x_549, 7);
}
lean_ctor_set(x_549, 0, x_547);
lean_ctor_set(x_549, 1, x_548);
x_550 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10;
x_551 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_551, 0, x_549);
lean_ctor_set(x_551, 1, x_550);
x_552 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_530, x_551, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_542);
x_553 = lean_ctor_get(x_552, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_552, 1);
lean_inc(x_554);
lean_dec(x_552);
x_555 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_442, x_553, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_554);
lean_dec(x_553);
x_556 = lean_ctor_get(x_555, 0);
lean_inc(x_556);
x_557 = lean_ctor_get(x_555, 1);
lean_inc(x_557);
lean_dec(x_555);
x_25 = x_556;
x_26 = x_557;
goto block_31;
}
else
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
lean_dec(x_540);
lean_dec(x_529);
lean_dec(x_503);
lean_dec(x_442);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_558 = lean_ctor_get(x_541, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_541, 1);
lean_inc(x_559);
if (lean_is_exclusive(x_541)) {
 lean_ctor_release(x_541, 0);
 lean_ctor_release(x_541, 1);
 x_560 = x_541;
} else {
 lean_dec_ref(x_541);
 x_560 = lean_box(0);
}
if (lean_is_scalar(x_560)) {
 x_561 = lean_alloc_ctor(1, 2, 0);
} else {
 x_561 = x_560;
}
lean_ctor_set(x_561, 0, x_558);
lean_ctor_set(x_561, 1, x_559);
return x_561;
}
}
}
}
else
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
lean_dec(x_442);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_562 = lean_ctor_get(x_486, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_486, 1);
lean_inc(x_563);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 x_564 = x_486;
} else {
 lean_dec_ref(x_486);
 x_564 = lean_box(0);
}
if (lean_is_scalar(x_564)) {
 x_565 = lean_alloc_ctor(1, 2, 0);
} else {
 x_565 = x_564;
}
lean_ctor_set(x_565, 0, x_562);
lean_ctor_set(x_565, 1, x_563);
return x_565;
}
}
}
else
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
lean_dec(x_442);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_566 = lean_ctor_get(x_480, 0);
lean_inc(x_566);
x_567 = lean_ctor_get(x_480, 1);
lean_inc(x_567);
if (lean_is_exclusive(x_480)) {
 lean_ctor_release(x_480, 0);
 lean_ctor_release(x_480, 1);
 x_568 = x_480;
} else {
 lean_dec_ref(x_480);
 x_568 = lean_box(0);
}
if (lean_is_scalar(x_568)) {
 x_569 = lean_alloc_ctor(1, 2, 0);
} else {
 x_569 = x_568;
}
lean_ctor_set(x_569, 0, x_566);
lean_ctor_set(x_569, 1, x_567);
return x_569;
}
}
block_31:
{
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
if (lean_is_scalar(x_24)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_24;
 lean_ctor_set_tag(x_28, 0);
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_24);
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec(x_25);
x_9 = x_23;
x_10 = x_29;
x_11 = lean_box(0);
x_20 = x_26;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__11(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = 1;
x_12 = lean_usize_sub(x_1, x_11);
x_13 = 5;
x_14 = lean_usize_mul(x_13, x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_5, x_15);
lean_dec(x_5);
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
x_19 = l_Lean_Expr_hash(x_17);
lean_dec(x_17);
x_20 = lean_uint64_of_nat(x_18);
lean_dec(x_18);
x_21 = lean_uint64_mix_hash(x_19, x_20);
x_22 = lean_uint64_to_usize(x_21);
x_23 = lean_usize_shift_right(x_22, x_14);
x_24 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10(x_6, x_23, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_16;
x_6 = x_24;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_expr_eqv(x_18, x_20);
lean_dec(x_20);
lean_dec(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_2, x_23);
lean_dec(x_2);
x_2 = x_24;
goto _start;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_eq(x_19, x_21);
lean_dec(x_21);
lean_dec(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_6);
lean_dec(x_5);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_2, x_27);
lean_dec(x_2);
x_2 = x_28;
goto _start;
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_1);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_1, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_1, 0);
lean_dec(x_32);
x_33 = lean_array_fset(x_5, x_2, x_3);
x_34 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_1);
x_35 = lean_array_fset(x_5, x_2, x_3);
x_36 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__2;
x_11 = lean_usize_land(x_2, x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
x_25 = lean_expr_eqv(x_21, x_23);
lean_dec(x_23);
lean_dec(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_22);
lean_free_object(x_15);
x_26 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_array_fset(x_17, x_12, x_27);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_28);
return x_1;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_eq(x_22, x_24);
lean_dec(x_24);
lean_dec(x_22);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_15);
x_30 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_array_fset(x_17, x_12, x_31);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_32);
return x_1;
}
else
{
lean_object* x_33; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_33 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_34 = lean_ctor_get(x_15, 0);
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_15);
x_36 = lean_ctor_get(x_4, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
x_40 = lean_expr_eqv(x_36, x_38);
lean_dec(x_38);
lean_dec(x_36);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_39);
lean_dec(x_37);
x_41 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_34, x_35, x_4, x_5);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_array_fset(x_17, x_12, x_42);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_43);
return x_1;
}
else
{
uint8_t x_44; 
x_44 = lean_nat_dec_eq(x_37, x_39);
lean_dec(x_39);
lean_dec(x_37);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_34, x_35, x_4, x_5);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_35);
lean_dec(x_34);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_5);
x_49 = lean_array_fset(x_17, x_12, x_48);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_49);
return x_1;
}
}
}
}
case 1:
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_15);
if (x_50 == 0)
{
lean_object* x_51; size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_15, 0);
x_52 = lean_usize_shift_right(x_2, x_9);
x_53 = lean_usize_add(x_3, x_8);
x_54 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10(x_51, x_52, x_53, x_4, x_5);
lean_ctor_set(x_15, 0, x_54);
x_55 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_55);
return x_1;
}
else
{
lean_object* x_56; size_t x_57; size_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_15, 0);
lean_inc(x_56);
lean_dec(x_15);
x_57 = lean_usize_shift_right(x_2, x_9);
x_58 = lean_usize_add(x_3, x_8);
x_59 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10(x_56, x_57, x_58, x_4, x_5);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_array_fset(x_17, x_12, x_60);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_61);
return x_1;
}
}
default: 
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_4);
lean_ctor_set(x_62, 1, x_5);
x_63 = lean_array_fset(x_17, x_12, x_62);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_63);
return x_1;
}
}
}
}
else
{
lean_object* x_64; size_t x_65; size_t x_66; size_t x_67; size_t x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_64 = lean_ctor_get(x_1, 0);
lean_inc(x_64);
lean_dec(x_1);
x_65 = 1;
x_66 = 5;
x_67 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__2;
x_68 = lean_usize_land(x_2, x_67);
x_69 = lean_usize_to_nat(x_68);
x_70 = lean_array_get_size(x_64);
x_71 = lean_nat_dec_lt(x_69, x_70);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_69);
lean_dec(x_5);
lean_dec(x_4);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_64);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_array_fget(x_64, x_69);
x_74 = lean_box(0);
x_75 = lean_array_fset(x_64, x_69, x_74);
switch (lean_obj_tag(x_73)) {
case 0:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_76 = lean_ctor_get(x_73, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_78 = x_73;
} else {
 lean_dec_ref(x_73);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_4, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_4, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_76, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
x_83 = lean_expr_eqv(x_79, x_81);
lean_dec(x_81);
lean_dec(x_79);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_78);
x_84 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_76, x_77, x_4, x_5);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_array_fset(x_75, x_69, x_85);
lean_dec(x_69);
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
else
{
uint8_t x_88; 
x_88 = lean_nat_dec_eq(x_80, x_82);
lean_dec(x_82);
lean_dec(x_80);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_78);
x_89 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_76, x_77, x_4, x_5);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = lean_array_fset(x_75, x_69, x_90);
lean_dec(x_69);
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_77);
lean_dec(x_76);
if (lean_is_scalar(x_78)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_78;
}
lean_ctor_set(x_93, 0, x_4);
lean_ctor_set(x_93, 1, x_5);
x_94 = lean_array_fset(x_75, x_69, x_93);
lean_dec(x_69);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
}
}
case 1:
{
lean_object* x_96; lean_object* x_97; size_t x_98; size_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_96 = lean_ctor_get(x_73, 0);
lean_inc(x_96);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_97 = x_73;
} else {
 lean_dec_ref(x_73);
 x_97 = lean_box(0);
}
x_98 = lean_usize_shift_right(x_2, x_66);
x_99 = lean_usize_add(x_3, x_65);
x_100 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10(x_96, x_98, x_99, x_4, x_5);
if (lean_is_scalar(x_97)) {
 x_101 = lean_alloc_ctor(1, 1, 0);
} else {
 x_101 = x_97;
}
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_array_fset(x_75, x_69, x_101);
lean_dec(x_69);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
default: 
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_4);
lean_ctor_set(x_104, 1, x_5);
x_105 = lean_array_fset(x_75, x_69, x_104);
lean_dec(x_69);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
}
}
}
else
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_1);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; size_t x_110; uint8_t x_111; 
x_108 = lean_unsigned_to_nat(0u);
x_109 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__12(x_1, x_108, x_4, x_5);
x_110 = 7;
x_111 = lean_usize_dec_le(x_110, x_3);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_109);
x_113 = lean_unsigned_to_nat(4u);
x_114 = lean_nat_dec_lt(x_112, x_113);
lean_dec(x_112);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_109, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_109, 1);
lean_inc(x_116);
lean_dec(x_109);
x_117 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__1;
x_118 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__11(x_3, x_115, x_116, lean_box(0), x_108, x_117);
lean_dec(x_116);
lean_dec(x_115);
return x_118;
}
else
{
return x_109;
}
}
else
{
return x_109;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; size_t x_124; uint8_t x_125; 
x_119 = lean_ctor_get(x_1, 0);
x_120 = lean_ctor_get(x_1, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_1);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_unsigned_to_nat(0u);
x_123 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__12(x_121, x_122, x_4, x_5);
x_124 = 7;
x_125 = lean_usize_dec_le(x_124, x_3);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_126 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_123);
x_127 = lean_unsigned_to_nat(4u);
x_128 = lean_nat_dec_lt(x_126, x_127);
lean_dec(x_126);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_129 = lean_ctor_get(x_123, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_123, 1);
lean_inc(x_130);
lean_dec(x_123);
x_131 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__1;
x_132 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__11(x_3, x_129, x_130, lean_box(0), x_122, x_131);
lean_dec(x_130);
lean_dec(x_129);
return x_132;
}
else
{
return x_123;
}
}
else
{
return x_123;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; size_t x_10; lean_object* x_11; 
x_4 = 1;
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = l_Lean_Expr_hash(x_5);
lean_dec(x_5);
x_8 = lean_uint64_of_nat(x_6);
lean_dec(x_6);
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = lean_uint64_to_usize(x_9);
x_11 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10(x_1, x_10, x_4, x_2, x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_expr_eqv(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__14(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__2;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_expr_eqv(x_3, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_free_object(x_1);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
lean_free_object(x_1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_usize_shift_right(x_2, x_6);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = 5;
x_22 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__2;
x_23 = lean_usize_land(x_2, x_22);
x_24 = lean_usize_to_nat(x_23);
x_25 = lean_box(2);
x_26 = lean_array_get(x_25, x_20, x_24);
lean_dec(x_24);
lean_dec(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_expr_eqv(x_3, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
}
case 1:
{
lean_object* x_32; size_t x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_usize_shift_right(x_2, x_21);
x_1 = x_32;
x_2 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; 
x_35 = lean_box(0);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_36, x_37, lean_box(0), x_38, x_3);
lean_dec(x_37);
lean_dec(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Expr_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__14(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_st_ref_take(x_6, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 1);
x_20 = lean_ctor_get(x_15, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_16, 1);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_1);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 0, x_1);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_3);
x_27 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__9(x_24, x_4, x_26);
lean_inc_n(x_1, 2);
x_28 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_25, x_1, x_1);
lean_ctor_set(x_17, 1, x_28);
lean_ctor_set(x_17, 0, x_27);
x_29 = lean_st_ref_set(x_6, x_16, x_19);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_1);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_ctor_get(x_17, 0);
x_35 = lean_ctor_get(x_17, 1);
x_36 = lean_ctor_get(x_17, 2);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_17);
lean_inc(x_1);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 0, x_1);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_15);
lean_ctor_set(x_37, 1, x_3);
x_38 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__9(x_34, x_4, x_37);
lean_inc_n(x_1, 2);
x_39 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_35, x_1, x_1);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_36);
lean_ctor_set(x_16, 1, x_40);
x_41 = lean_st_ref_set(x_6, x_16, x_19);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_45 = lean_ctor_get(x_16, 0);
x_46 = lean_ctor_get(x_16, 2);
x_47 = lean_ctor_get(x_16, 3);
x_48 = lean_ctor_get(x_16, 4);
x_49 = lean_ctor_get(x_16, 5);
x_50 = lean_ctor_get(x_16, 6);
x_51 = lean_ctor_get_uint8(x_16, sizeof(void*)*15);
x_52 = lean_ctor_get(x_16, 7);
x_53 = lean_ctor_get(x_16, 8);
x_54 = lean_ctor_get(x_16, 9);
x_55 = lean_ctor_get(x_16, 10);
x_56 = lean_ctor_get(x_16, 11);
x_57 = lean_ctor_get(x_16, 12);
x_58 = lean_ctor_get(x_16, 13);
x_59 = lean_ctor_get(x_16, 14);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_16);
x_60 = lean_ctor_get(x_17, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_17, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_17, 2);
lean_inc(x_62);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 x_63 = x_17;
} else {
 lean_dec_ref(x_17);
 x_63 = lean_box(0);
}
lean_inc(x_1);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 0, x_1);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_15);
lean_ctor_set(x_64, 1, x_3);
x_65 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__9(x_60, x_4, x_64);
lean_inc_n(x_1, 2);
x_66 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_61, x_1, x_1);
if (lean_is_scalar(x_63)) {
 x_67 = lean_alloc_ctor(0, 3, 0);
} else {
 x_67 = x_63;
}
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_67, 2, x_62);
x_68 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_68, 0, x_45);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_46);
lean_ctor_set(x_68, 3, x_47);
lean_ctor_set(x_68, 4, x_48);
lean_ctor_set(x_68, 5, x_49);
lean_ctor_set(x_68, 6, x_50);
lean_ctor_set(x_68, 7, x_52);
lean_ctor_set(x_68, 8, x_53);
lean_ctor_set(x_68, 9, x_54);
lean_ctor_set(x_68, 10, x_55);
lean_ctor_set(x_68, 11, x_56);
lean_ctor_set(x_68, 12, x_57);
lean_ctor_set(x_68, 13, x_58);
lean_ctor_set(x_68, 14, x_59);
lean_ctor_set_uint8(x_68, sizeof(void*)*15, x_51);
x_69 = lean_st_ref_set(x_6, x_68, x_19);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_1);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_73 = lean_ctor_get(x_15, 1);
lean_inc(x_73);
lean_dec(x_15);
x_74 = lean_ctor_get(x_16, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_16, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_16, 3);
lean_inc(x_76);
x_77 = lean_ctor_get(x_16, 4);
lean_inc(x_77);
x_78 = lean_ctor_get(x_16, 5);
lean_inc(x_78);
x_79 = lean_ctor_get(x_16, 6);
lean_inc(x_79);
x_80 = lean_ctor_get_uint8(x_16, sizeof(void*)*15);
x_81 = lean_ctor_get(x_16, 7);
lean_inc(x_81);
x_82 = lean_ctor_get(x_16, 8);
lean_inc(x_82);
x_83 = lean_ctor_get(x_16, 9);
lean_inc(x_83);
x_84 = lean_ctor_get(x_16, 10);
lean_inc(x_84);
x_85 = lean_ctor_get(x_16, 11);
lean_inc(x_85);
x_86 = lean_ctor_get(x_16, 12);
lean_inc(x_86);
x_87 = lean_ctor_get(x_16, 13);
lean_inc(x_87);
x_88 = lean_ctor_get(x_16, 14);
lean_inc(x_88);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 lean_ctor_release(x_16, 3);
 lean_ctor_release(x_16, 4);
 lean_ctor_release(x_16, 5);
 lean_ctor_release(x_16, 6);
 lean_ctor_release(x_16, 7);
 lean_ctor_release(x_16, 8);
 lean_ctor_release(x_16, 9);
 lean_ctor_release(x_16, 10);
 lean_ctor_release(x_16, 11);
 lean_ctor_release(x_16, 12);
 lean_ctor_release(x_16, 13);
 lean_ctor_release(x_16, 14);
 x_89 = x_16;
} else {
 lean_dec_ref(x_16);
 x_89 = lean_box(0);
}
x_90 = lean_ctor_get(x_17, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_17, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_17, 2);
lean_inc(x_92);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 x_93 = x_17;
} else {
 lean_dec_ref(x_17);
 x_93 = lean_box(0);
}
lean_inc(x_1);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_1);
lean_ctor_set(x_94, 1, x_2);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_3);
x_96 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__9(x_90, x_4, x_95);
lean_inc_n(x_1, 2);
x_97 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_91, x_1, x_1);
if (lean_is_scalar(x_93)) {
 x_98 = lean_alloc_ctor(0, 3, 0);
} else {
 x_98 = x_93;
}
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set(x_98, 2, x_92);
if (lean_is_scalar(x_89)) {
 x_99 = lean_alloc_ctor(0, 15, 1);
} else {
 x_99 = x_89;
}
lean_ctor_set(x_99, 0, x_74);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set(x_99, 2, x_75);
lean_ctor_set(x_99, 3, x_76);
lean_ctor_set(x_99, 4, x_77);
lean_ctor_set(x_99, 5, x_78);
lean_ctor_set(x_99, 6, x_79);
lean_ctor_set(x_99, 7, x_81);
lean_ctor_set(x_99, 8, x_82);
lean_ctor_set(x_99, 9, x_83);
lean_ctor_set(x_99, 10, x_84);
lean_ctor_set(x_99, 11, x_85);
lean_ctor_set(x_99, 12, x_86);
lean_ctor_set(x_99, 13, x_87);
lean_ctor_set(x_99, 14, x_88);
lean_ctor_set_uint8(x_99, sizeof(void*)*15, x_80);
x_100 = lean_st_ref_set(x_6, x_99, x_73);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_1);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__1;
x_2 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__1;
x_3 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(") ↦ ", 6, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__2;
x_18 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
lean_dec(x_5);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_box(0);
x_23 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__1(x_1, x_2, x_3, x_4, x_22, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_21);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 1);
x_26 = lean_ctor_get(x_18, 0);
lean_dec(x_26);
x_27 = l_Lean_Meta_Grind_updateLastTag(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_MessageData_ofExpr(x_5);
x_30 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__4;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_29);
lean_ctor_set(x_18, 0, x_30);
x_31 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__6;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_18);
lean_ctor_set(x_32, 1, x_31);
x_33 = l___private_Init_Data_Repr_0__Nat_reprFast(x_6);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Lean_MessageData_ofFormat(x_34);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__8;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_inc(x_1);
x_39 = l_Lean_MessageData_ofExpr(x_1);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_17, x_42, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_28);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__1(x_1, x_2, x_3, x_4, x_44, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_45);
lean_dec(x_44);
return x_46;
}
else
{
uint8_t x_47; 
lean_free_object(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_27);
if (x_47 == 0)
{
return x_27;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_27, 0);
x_49 = lean_ctor_get(x_27, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_27);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_18, 1);
lean_inc(x_51);
lean_dec(x_18);
x_52 = l_Lean_Meta_Grind_updateLastTag(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_Lean_MessageData_ofExpr(x_5);
x_55 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__4;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__6;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l___private_Init_Data_Repr_0__Nat_reprFast(x_6);
x_60 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = l_Lean_MessageData_ofFormat(x_60);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__8;
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
lean_inc(x_1);
x_65 = l_Lean_MessageData_ofExpr(x_1);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10;
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_17, x_68, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_53);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__1(x_1, x_2, x_3, x_4, x_70, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_71);
lean_dec(x_70);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = lean_ctor_get(x_52, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_52, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_75 = x_52;
} else {
 lean_dec_ref(x_52);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; 
lean_inc(x_2);
lean_inc(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_3);
x_18 = lean_infer_type(x_3, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
lean_dec(x_4);
x_22 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__1(x_21, x_17);
x_23 = lean_box(0);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_43; 
x_43 = lean_box(0);
x_24 = x_43;
goto block_42;
}
else
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_22, 0);
lean_inc(x_44);
lean_dec(x_22);
x_24 = x_44;
goto block_42;
}
block_42:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__3___closed__1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_24);
lean_inc(x_19);
lean_inc(x_3);
x_26 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8(x_5, x_3, x_6, x_19, x_23, x_25, x_24, x_24, x_24, x_25, lean_box(0), x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_box(0);
x_31 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2(x_3, x_19, x_24, x_17, x_1, x_2, x_30, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_29);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_26, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_34);
return x_26;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_dec(x_26);
x_36 = lean_ctor_get(x_28, 0);
lean_inc(x_36);
lean_dec(x_28);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_26);
if (x_38 == 0)
{
return x_26;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_26, 0);
x_40 = lean_ctor_get(x_26, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_26);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_18);
if (x_45 == 0)
{
return x_18;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_18, 0);
x_47 = lean_ctor_get(x_18, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_18);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_st_ref_get(x_6, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_20, x_4);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_free_object(x_15);
x_22 = lean_box(0);
x_23 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__3(x_2, x_3, x_4, x_19, x_1, x_5, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_18);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_15, 0, x_24);
return x_15;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_28, x_4);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_box(0);
x_31 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__3(x_2, x_3, x_4, x_27, x_1, x_5, x_30, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_26);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_1);
lean_dec(x_1);
x_17 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
return x_17;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; lean_object* x_22; 
x_21 = lean_unbox(x_3);
lean_dec(x_3);
x_22 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8(x_1, x_2, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__11(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__14(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__3(x_1, x_2, x_3, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Lean_Meta_Grind_Canon_canonElemCore(x_1, x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
uint64_t x_17; uint8_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint8_t x_24; lean_object* x_25; 
x_17 = lean_ctor_get_uint64(x_9, sizeof(void*)*7);
x_18 = 1;
lean_ctor_set_uint8(x_15, 9, x_18);
x_19 = 2;
x_20 = lean_uint64_shift_right(x_17, x_19);
x_21 = lean_uint64_shift_left(x_20, x_19);
x_22 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__3___closed__1;
x_23 = lean_uint64_lor(x_21, x_22);
lean_ctor_set_uint64(x_9, sizeof(void*)*7, x_23);
x_24 = 0;
x_25 = l_Lean_Meta_Grind_Canon_canonElemCore(x_1, x_2, x_3, x_4, x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_25);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint64_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; uint64_t x_58; uint8_t x_59; lean_object* x_60; 
x_34 = lean_ctor_get_uint64(x_9, sizeof(void*)*7);
x_35 = lean_ctor_get_uint8(x_15, 0);
x_36 = lean_ctor_get_uint8(x_15, 1);
x_37 = lean_ctor_get_uint8(x_15, 2);
x_38 = lean_ctor_get_uint8(x_15, 3);
x_39 = lean_ctor_get_uint8(x_15, 4);
x_40 = lean_ctor_get_uint8(x_15, 5);
x_41 = lean_ctor_get_uint8(x_15, 6);
x_42 = lean_ctor_get_uint8(x_15, 7);
x_43 = lean_ctor_get_uint8(x_15, 8);
x_44 = lean_ctor_get_uint8(x_15, 10);
x_45 = lean_ctor_get_uint8(x_15, 11);
x_46 = lean_ctor_get_uint8(x_15, 12);
x_47 = lean_ctor_get_uint8(x_15, 13);
x_48 = lean_ctor_get_uint8(x_15, 14);
x_49 = lean_ctor_get_uint8(x_15, 15);
x_50 = lean_ctor_get_uint8(x_15, 16);
x_51 = lean_ctor_get_uint8(x_15, 17);
lean_dec(x_15);
x_52 = 1;
x_53 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_53, 0, x_35);
lean_ctor_set_uint8(x_53, 1, x_36);
lean_ctor_set_uint8(x_53, 2, x_37);
lean_ctor_set_uint8(x_53, 3, x_38);
lean_ctor_set_uint8(x_53, 4, x_39);
lean_ctor_set_uint8(x_53, 5, x_40);
lean_ctor_set_uint8(x_53, 6, x_41);
lean_ctor_set_uint8(x_53, 7, x_42);
lean_ctor_set_uint8(x_53, 8, x_43);
lean_ctor_set_uint8(x_53, 9, x_52);
lean_ctor_set_uint8(x_53, 10, x_44);
lean_ctor_set_uint8(x_53, 11, x_45);
lean_ctor_set_uint8(x_53, 12, x_46);
lean_ctor_set_uint8(x_53, 13, x_47);
lean_ctor_set_uint8(x_53, 14, x_48);
lean_ctor_set_uint8(x_53, 15, x_49);
lean_ctor_set_uint8(x_53, 16, x_50);
lean_ctor_set_uint8(x_53, 17, x_51);
x_54 = 2;
x_55 = lean_uint64_shift_right(x_34, x_54);
x_56 = lean_uint64_shift_left(x_55, x_54);
x_57 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__3___closed__1;
x_58 = lean_uint64_lor(x_56, x_57);
lean_ctor_set(x_9, 0, x_53);
lean_ctor_set_uint64(x_9, sizeof(void*)*7, x_58);
x_59 = 0;
x_60 = l_Lean_Meta_Grind_Canon_canonElemCore(x_1, x_2, x_3, x_4, x_59, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_67 = x_60;
} else {
 lean_dec_ref(x_60);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
else
{
lean_object* x_69; uint64_t x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; uint64_t x_100; uint64_t x_101; uint64_t x_102; uint64_t x_103; uint64_t x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; 
x_69 = lean_ctor_get(x_9, 0);
x_70 = lean_ctor_get_uint64(x_9, sizeof(void*)*7);
x_71 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 8);
x_72 = lean_ctor_get(x_9, 1);
x_73 = lean_ctor_get(x_9, 2);
x_74 = lean_ctor_get(x_9, 3);
x_75 = lean_ctor_get(x_9, 4);
x_76 = lean_ctor_get(x_9, 5);
x_77 = lean_ctor_get(x_9, 6);
x_78 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 9);
x_79 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 10);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_69);
lean_dec(x_9);
x_80 = lean_ctor_get_uint8(x_69, 0);
x_81 = lean_ctor_get_uint8(x_69, 1);
x_82 = lean_ctor_get_uint8(x_69, 2);
x_83 = lean_ctor_get_uint8(x_69, 3);
x_84 = lean_ctor_get_uint8(x_69, 4);
x_85 = lean_ctor_get_uint8(x_69, 5);
x_86 = lean_ctor_get_uint8(x_69, 6);
x_87 = lean_ctor_get_uint8(x_69, 7);
x_88 = lean_ctor_get_uint8(x_69, 8);
x_89 = lean_ctor_get_uint8(x_69, 10);
x_90 = lean_ctor_get_uint8(x_69, 11);
x_91 = lean_ctor_get_uint8(x_69, 12);
x_92 = lean_ctor_get_uint8(x_69, 13);
x_93 = lean_ctor_get_uint8(x_69, 14);
x_94 = lean_ctor_get_uint8(x_69, 15);
x_95 = lean_ctor_get_uint8(x_69, 16);
x_96 = lean_ctor_get_uint8(x_69, 17);
if (lean_is_exclusive(x_69)) {
 x_97 = x_69;
} else {
 lean_dec_ref(x_69);
 x_97 = lean_box(0);
}
x_98 = 1;
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 0, 18);
} else {
 x_99 = x_97;
}
lean_ctor_set_uint8(x_99, 0, x_80);
lean_ctor_set_uint8(x_99, 1, x_81);
lean_ctor_set_uint8(x_99, 2, x_82);
lean_ctor_set_uint8(x_99, 3, x_83);
lean_ctor_set_uint8(x_99, 4, x_84);
lean_ctor_set_uint8(x_99, 5, x_85);
lean_ctor_set_uint8(x_99, 6, x_86);
lean_ctor_set_uint8(x_99, 7, x_87);
lean_ctor_set_uint8(x_99, 8, x_88);
lean_ctor_set_uint8(x_99, 9, x_98);
lean_ctor_set_uint8(x_99, 10, x_89);
lean_ctor_set_uint8(x_99, 11, x_90);
lean_ctor_set_uint8(x_99, 12, x_91);
lean_ctor_set_uint8(x_99, 13, x_92);
lean_ctor_set_uint8(x_99, 14, x_93);
lean_ctor_set_uint8(x_99, 15, x_94);
lean_ctor_set_uint8(x_99, 16, x_95);
lean_ctor_set_uint8(x_99, 17, x_96);
x_100 = 2;
x_101 = lean_uint64_shift_right(x_70, x_100);
x_102 = lean_uint64_shift_left(x_101, x_100);
x_103 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__3___closed__1;
x_104 = lean_uint64_lor(x_102, x_103);
x_105 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_105, 0, x_99);
lean_ctor_set(x_105, 1, x_72);
lean_ctor_set(x_105, 2, x_73);
lean_ctor_set(x_105, 3, x_74);
lean_ctor_set(x_105, 4, x_75);
lean_ctor_set(x_105, 5, x_76);
lean_ctor_set(x_105, 6, x_77);
lean_ctor_set_uint64(x_105, sizeof(void*)*7, x_104);
lean_ctor_set_uint8(x_105, sizeof(void*)*7 + 8, x_71);
lean_ctor_set_uint8(x_105, sizeof(void*)*7 + 9, x_78);
lean_ctor_set_uint8(x_105, sizeof(void*)*7 + 10, x_79);
x_106 = 0;
x_107 = l_Lean_Meta_Grind_Canon_canonElemCore(x_1, x_2, x_3, x_4, x_106, x_5, x_6, x_7, x_8, x_105, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_114 = x_107;
} else {
 lean_dec_ref(x_107);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
}
static uint64_t _init_l_Lean_Meta_Grind_Canon_canonInst___closed__1() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 3;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonInst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
uint64_t x_17; uint8_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint8_t x_24; lean_object* x_25; 
x_17 = lean_ctor_get_uint64(x_9, sizeof(void*)*7);
x_18 = 3;
lean_ctor_set_uint8(x_15, 9, x_18);
x_19 = 2;
x_20 = lean_uint64_shift_right(x_17, x_19);
x_21 = lean_uint64_shift_left(x_20, x_19);
x_22 = l_Lean_Meta_Grind_Canon_canonInst___closed__1;
x_23 = lean_uint64_lor(x_21, x_22);
lean_ctor_set_uint64(x_9, sizeof(void*)*7, x_23);
x_24 = 1;
x_25 = l_Lean_Meta_Grind_Canon_canonElemCore(x_1, x_2, x_3, x_4, x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_25);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint64_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; uint64_t x_58; uint8_t x_59; lean_object* x_60; 
x_34 = lean_ctor_get_uint64(x_9, sizeof(void*)*7);
x_35 = lean_ctor_get_uint8(x_15, 0);
x_36 = lean_ctor_get_uint8(x_15, 1);
x_37 = lean_ctor_get_uint8(x_15, 2);
x_38 = lean_ctor_get_uint8(x_15, 3);
x_39 = lean_ctor_get_uint8(x_15, 4);
x_40 = lean_ctor_get_uint8(x_15, 5);
x_41 = lean_ctor_get_uint8(x_15, 6);
x_42 = lean_ctor_get_uint8(x_15, 7);
x_43 = lean_ctor_get_uint8(x_15, 8);
x_44 = lean_ctor_get_uint8(x_15, 10);
x_45 = lean_ctor_get_uint8(x_15, 11);
x_46 = lean_ctor_get_uint8(x_15, 12);
x_47 = lean_ctor_get_uint8(x_15, 13);
x_48 = lean_ctor_get_uint8(x_15, 14);
x_49 = lean_ctor_get_uint8(x_15, 15);
x_50 = lean_ctor_get_uint8(x_15, 16);
x_51 = lean_ctor_get_uint8(x_15, 17);
lean_dec(x_15);
x_52 = 3;
x_53 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_53, 0, x_35);
lean_ctor_set_uint8(x_53, 1, x_36);
lean_ctor_set_uint8(x_53, 2, x_37);
lean_ctor_set_uint8(x_53, 3, x_38);
lean_ctor_set_uint8(x_53, 4, x_39);
lean_ctor_set_uint8(x_53, 5, x_40);
lean_ctor_set_uint8(x_53, 6, x_41);
lean_ctor_set_uint8(x_53, 7, x_42);
lean_ctor_set_uint8(x_53, 8, x_43);
lean_ctor_set_uint8(x_53, 9, x_52);
lean_ctor_set_uint8(x_53, 10, x_44);
lean_ctor_set_uint8(x_53, 11, x_45);
lean_ctor_set_uint8(x_53, 12, x_46);
lean_ctor_set_uint8(x_53, 13, x_47);
lean_ctor_set_uint8(x_53, 14, x_48);
lean_ctor_set_uint8(x_53, 15, x_49);
lean_ctor_set_uint8(x_53, 16, x_50);
lean_ctor_set_uint8(x_53, 17, x_51);
x_54 = 2;
x_55 = lean_uint64_shift_right(x_34, x_54);
x_56 = lean_uint64_shift_left(x_55, x_54);
x_57 = l_Lean_Meta_Grind_Canon_canonInst___closed__1;
x_58 = lean_uint64_lor(x_56, x_57);
lean_ctor_set(x_9, 0, x_53);
lean_ctor_set_uint64(x_9, sizeof(void*)*7, x_58);
x_59 = 1;
x_60 = l_Lean_Meta_Grind_Canon_canonElemCore(x_1, x_2, x_3, x_4, x_59, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_67 = x_60;
} else {
 lean_dec_ref(x_60);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
else
{
lean_object* x_69; uint64_t x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; uint64_t x_100; uint64_t x_101; uint64_t x_102; uint64_t x_103; uint64_t x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; 
x_69 = lean_ctor_get(x_9, 0);
x_70 = lean_ctor_get_uint64(x_9, sizeof(void*)*7);
x_71 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 8);
x_72 = lean_ctor_get(x_9, 1);
x_73 = lean_ctor_get(x_9, 2);
x_74 = lean_ctor_get(x_9, 3);
x_75 = lean_ctor_get(x_9, 4);
x_76 = lean_ctor_get(x_9, 5);
x_77 = lean_ctor_get(x_9, 6);
x_78 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 9);
x_79 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 10);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_69);
lean_dec(x_9);
x_80 = lean_ctor_get_uint8(x_69, 0);
x_81 = lean_ctor_get_uint8(x_69, 1);
x_82 = lean_ctor_get_uint8(x_69, 2);
x_83 = lean_ctor_get_uint8(x_69, 3);
x_84 = lean_ctor_get_uint8(x_69, 4);
x_85 = lean_ctor_get_uint8(x_69, 5);
x_86 = lean_ctor_get_uint8(x_69, 6);
x_87 = lean_ctor_get_uint8(x_69, 7);
x_88 = lean_ctor_get_uint8(x_69, 8);
x_89 = lean_ctor_get_uint8(x_69, 10);
x_90 = lean_ctor_get_uint8(x_69, 11);
x_91 = lean_ctor_get_uint8(x_69, 12);
x_92 = lean_ctor_get_uint8(x_69, 13);
x_93 = lean_ctor_get_uint8(x_69, 14);
x_94 = lean_ctor_get_uint8(x_69, 15);
x_95 = lean_ctor_get_uint8(x_69, 16);
x_96 = lean_ctor_get_uint8(x_69, 17);
if (lean_is_exclusive(x_69)) {
 x_97 = x_69;
} else {
 lean_dec_ref(x_69);
 x_97 = lean_box(0);
}
x_98 = 3;
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 0, 18);
} else {
 x_99 = x_97;
}
lean_ctor_set_uint8(x_99, 0, x_80);
lean_ctor_set_uint8(x_99, 1, x_81);
lean_ctor_set_uint8(x_99, 2, x_82);
lean_ctor_set_uint8(x_99, 3, x_83);
lean_ctor_set_uint8(x_99, 4, x_84);
lean_ctor_set_uint8(x_99, 5, x_85);
lean_ctor_set_uint8(x_99, 6, x_86);
lean_ctor_set_uint8(x_99, 7, x_87);
lean_ctor_set_uint8(x_99, 8, x_88);
lean_ctor_set_uint8(x_99, 9, x_98);
lean_ctor_set_uint8(x_99, 10, x_89);
lean_ctor_set_uint8(x_99, 11, x_90);
lean_ctor_set_uint8(x_99, 12, x_91);
lean_ctor_set_uint8(x_99, 13, x_92);
lean_ctor_set_uint8(x_99, 14, x_93);
lean_ctor_set_uint8(x_99, 15, x_94);
lean_ctor_set_uint8(x_99, 16, x_95);
lean_ctor_set_uint8(x_99, 17, x_96);
x_100 = 2;
x_101 = lean_uint64_shift_right(x_70, x_100);
x_102 = lean_uint64_shift_left(x_101, x_100);
x_103 = l_Lean_Meta_Grind_Canon_canonInst___closed__1;
x_104 = lean_uint64_lor(x_102, x_103);
x_105 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_105, 0, x_99);
lean_ctor_set(x_105, 1, x_72);
lean_ctor_set(x_105, 2, x_73);
lean_ctor_set(x_105, 3, x_74);
lean_ctor_set(x_105, 4, x_75);
lean_ctor_set(x_105, 5, x_76);
lean_ctor_set(x_105, 6, x_77);
lean_ctor_set_uint64(x_105, sizeof(void*)*7, x_104);
lean_ctor_set_uint8(x_105, sizeof(void*)*7 + 8, x_71);
lean_ctor_set_uint8(x_105, sizeof(void*)*7 + 9, x_78);
lean_ctor_set_uint8(x_105, sizeof(void*)*7 + 10, x_79);
x_106 = 1;
x_107 = l_Lean_Meta_Grind_Canon_canonElemCore(x_1, x_2, x_3, x_4, x_106, x_5, x_6, x_7, x_8, x_105, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_114 = x_107;
} else {
 lean_dec_ref(x_107);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
}
static uint64_t _init_l_Lean_Meta_Grind_Canon_canonImplicit___closed__1() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 2;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImplicit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
uint64_t x_17; uint8_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint8_t x_24; lean_object* x_25; 
x_17 = lean_ctor_get_uint64(x_9, sizeof(void*)*7);
x_18 = 2;
lean_ctor_set_uint8(x_15, 9, x_18);
x_19 = 2;
x_20 = lean_uint64_shift_right(x_17, x_19);
x_21 = lean_uint64_shift_left(x_20, x_19);
x_22 = l_Lean_Meta_Grind_Canon_canonImplicit___closed__1;
x_23 = lean_uint64_lor(x_21, x_22);
lean_ctor_set_uint64(x_9, sizeof(void*)*7, x_23);
x_24 = 1;
x_25 = l_Lean_Meta_Grind_Canon_canonElemCore(x_1, x_2, x_3, x_4, x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_25);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint64_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; uint64_t x_58; uint8_t x_59; lean_object* x_60; 
x_34 = lean_ctor_get_uint64(x_9, sizeof(void*)*7);
x_35 = lean_ctor_get_uint8(x_15, 0);
x_36 = lean_ctor_get_uint8(x_15, 1);
x_37 = lean_ctor_get_uint8(x_15, 2);
x_38 = lean_ctor_get_uint8(x_15, 3);
x_39 = lean_ctor_get_uint8(x_15, 4);
x_40 = lean_ctor_get_uint8(x_15, 5);
x_41 = lean_ctor_get_uint8(x_15, 6);
x_42 = lean_ctor_get_uint8(x_15, 7);
x_43 = lean_ctor_get_uint8(x_15, 8);
x_44 = lean_ctor_get_uint8(x_15, 10);
x_45 = lean_ctor_get_uint8(x_15, 11);
x_46 = lean_ctor_get_uint8(x_15, 12);
x_47 = lean_ctor_get_uint8(x_15, 13);
x_48 = lean_ctor_get_uint8(x_15, 14);
x_49 = lean_ctor_get_uint8(x_15, 15);
x_50 = lean_ctor_get_uint8(x_15, 16);
x_51 = lean_ctor_get_uint8(x_15, 17);
lean_dec(x_15);
x_52 = 2;
x_53 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_53, 0, x_35);
lean_ctor_set_uint8(x_53, 1, x_36);
lean_ctor_set_uint8(x_53, 2, x_37);
lean_ctor_set_uint8(x_53, 3, x_38);
lean_ctor_set_uint8(x_53, 4, x_39);
lean_ctor_set_uint8(x_53, 5, x_40);
lean_ctor_set_uint8(x_53, 6, x_41);
lean_ctor_set_uint8(x_53, 7, x_42);
lean_ctor_set_uint8(x_53, 8, x_43);
lean_ctor_set_uint8(x_53, 9, x_52);
lean_ctor_set_uint8(x_53, 10, x_44);
lean_ctor_set_uint8(x_53, 11, x_45);
lean_ctor_set_uint8(x_53, 12, x_46);
lean_ctor_set_uint8(x_53, 13, x_47);
lean_ctor_set_uint8(x_53, 14, x_48);
lean_ctor_set_uint8(x_53, 15, x_49);
lean_ctor_set_uint8(x_53, 16, x_50);
lean_ctor_set_uint8(x_53, 17, x_51);
x_54 = 2;
x_55 = lean_uint64_shift_right(x_34, x_54);
x_56 = lean_uint64_shift_left(x_55, x_54);
x_57 = l_Lean_Meta_Grind_Canon_canonImplicit___closed__1;
x_58 = lean_uint64_lor(x_56, x_57);
lean_ctor_set(x_9, 0, x_53);
lean_ctor_set_uint64(x_9, sizeof(void*)*7, x_58);
x_59 = 1;
x_60 = l_Lean_Meta_Grind_Canon_canonElemCore(x_1, x_2, x_3, x_4, x_59, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_67 = x_60;
} else {
 lean_dec_ref(x_60);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
else
{
lean_object* x_69; uint64_t x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; uint64_t x_100; uint64_t x_101; uint64_t x_102; uint64_t x_103; uint64_t x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; 
x_69 = lean_ctor_get(x_9, 0);
x_70 = lean_ctor_get_uint64(x_9, sizeof(void*)*7);
x_71 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 8);
x_72 = lean_ctor_get(x_9, 1);
x_73 = lean_ctor_get(x_9, 2);
x_74 = lean_ctor_get(x_9, 3);
x_75 = lean_ctor_get(x_9, 4);
x_76 = lean_ctor_get(x_9, 5);
x_77 = lean_ctor_get(x_9, 6);
x_78 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 9);
x_79 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 10);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_69);
lean_dec(x_9);
x_80 = lean_ctor_get_uint8(x_69, 0);
x_81 = lean_ctor_get_uint8(x_69, 1);
x_82 = lean_ctor_get_uint8(x_69, 2);
x_83 = lean_ctor_get_uint8(x_69, 3);
x_84 = lean_ctor_get_uint8(x_69, 4);
x_85 = lean_ctor_get_uint8(x_69, 5);
x_86 = lean_ctor_get_uint8(x_69, 6);
x_87 = lean_ctor_get_uint8(x_69, 7);
x_88 = lean_ctor_get_uint8(x_69, 8);
x_89 = lean_ctor_get_uint8(x_69, 10);
x_90 = lean_ctor_get_uint8(x_69, 11);
x_91 = lean_ctor_get_uint8(x_69, 12);
x_92 = lean_ctor_get_uint8(x_69, 13);
x_93 = lean_ctor_get_uint8(x_69, 14);
x_94 = lean_ctor_get_uint8(x_69, 15);
x_95 = lean_ctor_get_uint8(x_69, 16);
x_96 = lean_ctor_get_uint8(x_69, 17);
if (lean_is_exclusive(x_69)) {
 x_97 = x_69;
} else {
 lean_dec_ref(x_69);
 x_97 = lean_box(0);
}
x_98 = 2;
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 0, 18);
} else {
 x_99 = x_97;
}
lean_ctor_set_uint8(x_99, 0, x_80);
lean_ctor_set_uint8(x_99, 1, x_81);
lean_ctor_set_uint8(x_99, 2, x_82);
lean_ctor_set_uint8(x_99, 3, x_83);
lean_ctor_set_uint8(x_99, 4, x_84);
lean_ctor_set_uint8(x_99, 5, x_85);
lean_ctor_set_uint8(x_99, 6, x_86);
lean_ctor_set_uint8(x_99, 7, x_87);
lean_ctor_set_uint8(x_99, 8, x_88);
lean_ctor_set_uint8(x_99, 9, x_98);
lean_ctor_set_uint8(x_99, 10, x_89);
lean_ctor_set_uint8(x_99, 11, x_90);
lean_ctor_set_uint8(x_99, 12, x_91);
lean_ctor_set_uint8(x_99, 13, x_92);
lean_ctor_set_uint8(x_99, 14, x_93);
lean_ctor_set_uint8(x_99, 15, x_94);
lean_ctor_set_uint8(x_99, 16, x_95);
lean_ctor_set_uint8(x_99, 17, x_96);
x_100 = 2;
x_101 = lean_uint64_shift_right(x_70, x_100);
x_102 = lean_uint64_shift_left(x_101, x_100);
x_103 = l_Lean_Meta_Grind_Canon_canonImplicit___closed__1;
x_104 = lean_uint64_lor(x_102, x_103);
x_105 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_105, 0, x_99);
lean_ctor_set(x_105, 1, x_72);
lean_ctor_set(x_105, 2, x_73);
lean_ctor_set(x_105, 3, x_74);
lean_ctor_set(x_105, 4, x_75);
lean_ctor_set(x_105, 5, x_76);
lean_ctor_set(x_105, 6, x_77);
lean_ctor_set_uint64(x_105, sizeof(void*)*7, x_104);
lean_ctor_set_uint8(x_105, sizeof(void*)*7 + 8, x_71);
lean_ctor_set_uint8(x_105, sizeof(void*)*7 + 9, x_78);
lean_ctor_set_uint8(x_105, sizeof(void*)*7 + 10, x_79);
x_106 = 1;
x_107 = l_Lean_Meta_Grind_Canon_canonElemCore(x_1, x_2, x_3, x_4, x_106, x_5, x_6, x_7, x_8, x_105, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_114 = x_107;
} else {
 lean_dec_ref(x_107);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
static uint8_t _init_l_Lean_Meta_Grind_Canon_instInhabitedShouldCanonResult() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("canonType", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("canonInst", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("canonImplicit", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("visit", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult(uint8_t x_1, lean_object* x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__2;
return x_3;
}
case 1:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__4;
return x_4;
}
case 2:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__6;
return x_5;
}
default: 
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__8;
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Meta_Grind_Canon_instReprShouldCanonResult(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_shouldCanon___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Meta_isProp(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Lean_Meta_isTypeFormer(x_1, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = 3;
x_18 = lean_box(x_17);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = 3;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_12, 0);
lean_dec(x_24);
x_25 = 0;
x_26 = lean_box(x_25);
lean_ctor_set(x_12, 0, x_26);
return x_12;
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_dec(x_12);
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_12);
if (x_31 == 0)
{
return x_12;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_12, 0);
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_12);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_8);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_8, 0);
lean_dec(x_36);
x_37 = 3;
x_38 = lean_box(x_37);
lean_ctor_set(x_8, 0, x_38);
return x_8;
}
else
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_8, 1);
lean_inc(x_39);
lean_dec(x_8);
x_40 = 3;
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_8);
if (x_43 == 0)
{
return x_8;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_8, 0);
x_45 = lean_ctor_get(x_8, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_8);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_shouldCanon(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_nat_dec_lt(x_2, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Meta_Grind_Canon_shouldCanon___lambda__1(x_3, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_fget(x_1, x_2);
x_14 = l_Lean_Meta_ParamInfo_isInstImplicit(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 2);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Lean_Meta_ParamInfo_isImplicit(x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Lean_Meta_Grind_Canon_shouldCanon___lambda__1(x_3, x_17, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = l_Lean_Meta_isTypeFormer(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
x_24 = 2;
x_25 = lean_box(x_24);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec(x_19);
x_27 = 2;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_19);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_19, 0);
lean_dec(x_31);
x_32 = 0;
x_33 = lean_box(x_32);
lean_ctor_set(x_19, 0, x_33);
return x_19;
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_dec(x_19);
x_35 = 0;
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_19);
if (x_38 == 0)
{
return x_19;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_19, 0);
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_19);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_42 = 3;
x_43 = lean_box(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_8);
return x_44;
}
}
else
{
uint8_t x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_45 = 1;
x_46 = lean_box(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_8);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_shouldCanon___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Canon_shouldCanon___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_shouldCanon___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_Canon_shouldCanon(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ptr_addr(x_4);
x_7 = lean_ptr_addr(x_1);
x_8 = lean_usize_dec_eq(x_6, x_7);
if (x_8 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_2, x_20);
lean_ctor_set(x_3, 2, x_21);
x_22 = lean_array_uset(x_2, x_20, x_3);
x_2 = x_22;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_ctor_get(x_3, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_27 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_24);
x_28 = lean_apply_1(x_1, x_24);
x_29 = lean_unbox_uint64(x_28);
lean_dec(x_28);
x_30 = 32;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = 16;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_38 = 1;
x_39 = lean_usize_sub(x_37, x_38);
x_40 = lean_usize_land(x_36, x_39);
x_41 = lean_array_uget(x_2, x_40);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_24);
lean_ctor_set(x_42, 1, x_25);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_array_uset(x_2, x_40, x_42);
x_2 = x_43;
x_3 = x_26;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__4___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_ptr_addr(x_4);
x_8 = lean_usize_to_uint64(x_7);
x_9 = 11;
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = 32;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = 16;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_19 = 1;
x_20 = lean_usize_sub(x_18, x_19);
x_21 = lean_usize_land(x_17, x_20);
x_22 = lean_array_uget(x_1, x_21);
lean_ctor_set(x_2, 2, x_22);
x_23 = lean_array_uset(x_1, x_21, x_2);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; size_t x_39; size_t x_40; size_t x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
x_28 = lean_array_get_size(x_1);
x_29 = lean_ptr_addr(x_25);
x_30 = lean_usize_to_uint64(x_29);
x_31 = 11;
x_32 = lean_uint64_mix_hash(x_30, x_31);
x_33 = 32;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = 16;
x_37 = lean_uint64_shift_right(x_35, x_36);
x_38 = lean_uint64_xor(x_35, x_37);
x_39 = lean_uint64_to_usize(x_38);
x_40 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_41 = 1;
x_42 = lean_usize_sub(x_40, x_41);
x_43 = lean_usize_land(x_39, x_42);
x_44 = lean_array_uget(x_1, x_43);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_25);
lean_ctor_set(x_45, 1, x_26);
lean_ctor_set(x_45, 2, x_44);
x_46 = lean_array_uset(x_1, x_43, x_45);
x_1 = x_46;
x_2 = x_27;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__4___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__5(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__3(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_ptr_addr(x_6);
x_10 = lean_ptr_addr(x_1);
x_11 = lean_usize_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__6(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_12);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_16 = lean_ptr_addr(x_13);
x_17 = lean_ptr_addr(x_1);
x_18 = lean_usize_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__6(x_1, x_2, x_15);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_19);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_2);
lean_ctor_set(x_21, 2, x_15);
return x_21;
}
}
}
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instMonadMetaM;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__1;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__2;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__3;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__4;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__5;
x_2 = l_Lean_instInhabitedExpr;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__6;
x_13 = lean_panic_fn(x_12, x_1);
x_14 = lean_apply_10(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_9, 2);
x_13 = l_Lean_isTracingEnabledForCore(x_1, x_12, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
static double _init_l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = l_Float_ofScientific(x_1, x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_10, 5);
x_14 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_8, x_9, x_10, x_11, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_take(x_11, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_17, 1);
x_22 = lean_ctor_get(x_17, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_18, 3);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; double x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__1;
x_28 = 0;
x_29 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__9;
x_30 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_float(x_30, sizeof(void*)*2, x_27);
lean_ctor_set_float(x_30, sizeof(void*)*2 + 8, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*2 + 16, x_28);
x_31 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__2;
x_32 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_15);
lean_ctor_set(x_32, 2, x_31);
lean_inc(x_13);
lean_ctor_set(x_17, 1, x_32);
lean_ctor_set(x_17, 0, x_13);
x_33 = l_Lean_PersistentArray_push___rarg(x_26, x_17);
lean_ctor_set(x_19, 0, x_33);
x_34 = lean_st_ref_set(x_11, x_18, x_21);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
uint64_t x_41; lean_object* x_42; double x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_41 = lean_ctor_get_uint64(x_19, sizeof(void*)*1);
x_42 = lean_ctor_get(x_19, 0);
lean_inc(x_42);
lean_dec(x_19);
x_43 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__1;
x_44 = 0;
x_45 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__9;
x_46 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set_float(x_46, sizeof(void*)*2, x_43);
lean_ctor_set_float(x_46, sizeof(void*)*2 + 8, x_43);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 16, x_44);
x_47 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__2;
x_48 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_15);
lean_ctor_set(x_48, 2, x_47);
lean_inc(x_13);
lean_ctor_set(x_17, 1, x_48);
lean_ctor_set(x_17, 0, x_13);
x_49 = l_Lean_PersistentArray_push___rarg(x_42, x_17);
x_50 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set_uint64(x_50, sizeof(void*)*1, x_41);
lean_ctor_set(x_18, 3, x_50);
x_51 = lean_st_ref_set(x_11, x_18, x_21);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
x_54 = lean_box(0);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint64_t x_63; lean_object* x_64; lean_object* x_65; double x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_56 = lean_ctor_get(x_18, 0);
x_57 = lean_ctor_get(x_18, 1);
x_58 = lean_ctor_get(x_18, 2);
x_59 = lean_ctor_get(x_18, 4);
x_60 = lean_ctor_get(x_18, 5);
x_61 = lean_ctor_get(x_18, 6);
x_62 = lean_ctor_get(x_18, 7);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_18);
x_63 = lean_ctor_get_uint64(x_19, sizeof(void*)*1);
x_64 = lean_ctor_get(x_19, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_65 = x_19;
} else {
 lean_dec_ref(x_19);
 x_65 = lean_box(0);
}
x_66 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__1;
x_67 = 0;
x_68 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__9;
x_69 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set_float(x_69, sizeof(void*)*2, x_66);
lean_ctor_set_float(x_69, sizeof(void*)*2 + 8, x_66);
lean_ctor_set_uint8(x_69, sizeof(void*)*2 + 16, x_67);
x_70 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__2;
x_71 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_15);
lean_ctor_set(x_71, 2, x_70);
lean_inc(x_13);
lean_ctor_set(x_17, 1, x_71);
lean_ctor_set(x_17, 0, x_13);
x_72 = l_Lean_PersistentArray_push___rarg(x_64, x_17);
if (lean_is_scalar(x_65)) {
 x_73 = lean_alloc_ctor(0, 1, 8);
} else {
 x_73 = x_65;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set_uint64(x_73, sizeof(void*)*1, x_63);
x_74 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_74, 0, x_56);
lean_ctor_set(x_74, 1, x_57);
lean_ctor_set(x_74, 2, x_58);
lean_ctor_set(x_74, 3, x_73);
lean_ctor_set(x_74, 4, x_59);
lean_ctor_set(x_74, 5, x_60);
lean_ctor_set(x_74, 6, x_61);
lean_ctor_set(x_74, 7, x_62);
x_75 = lean_st_ref_set(x_11, x_74, x_21);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
x_78 = lean_box(0);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_76);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint64_t x_89; lean_object* x_90; lean_object* x_91; double x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_80 = lean_ctor_get(x_17, 1);
lean_inc(x_80);
lean_dec(x_17);
x_81 = lean_ctor_get(x_18, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_18, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_18, 2);
lean_inc(x_83);
x_84 = lean_ctor_get(x_18, 4);
lean_inc(x_84);
x_85 = lean_ctor_get(x_18, 5);
lean_inc(x_85);
x_86 = lean_ctor_get(x_18, 6);
lean_inc(x_86);
x_87 = lean_ctor_get(x_18, 7);
lean_inc(x_87);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 lean_ctor_release(x_18, 5);
 lean_ctor_release(x_18, 6);
 lean_ctor_release(x_18, 7);
 x_88 = x_18;
} else {
 lean_dec_ref(x_18);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get_uint64(x_19, sizeof(void*)*1);
x_90 = lean_ctor_get(x_19, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_91 = x_19;
} else {
 lean_dec_ref(x_19);
 x_91 = lean_box(0);
}
x_92 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__1;
x_93 = 0;
x_94 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__9;
x_95 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_95, 0, x_1);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set_float(x_95, sizeof(void*)*2, x_92);
lean_ctor_set_float(x_95, sizeof(void*)*2 + 8, x_92);
lean_ctor_set_uint8(x_95, sizeof(void*)*2 + 16, x_93);
x_96 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__2;
x_97 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_15);
lean_ctor_set(x_97, 2, x_96);
lean_inc(x_13);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_13);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_PersistentArray_push___rarg(x_90, x_98);
if (lean_is_scalar(x_91)) {
 x_100 = lean_alloc_ctor(0, 1, 8);
} else {
 x_100 = x_91;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set_uint64(x_100, sizeof(void*)*1, x_89);
if (lean_is_scalar(x_88)) {
 x_101 = lean_alloc_ctor(0, 8, 0);
} else {
 x_101 = x_88;
}
lean_ctor_set(x_101, 0, x_81);
lean_ctor_set(x_101, 1, x_82);
lean_ctor_set(x_101, 2, x_83);
lean_ctor_set(x_101, 3, x_100);
lean_ctor_set(x_101, 4, x_84);
lean_ctor_set(x_101, 5, x_85);
lean_ctor_set(x_101, 6, x_86);
lean_ctor_set(x_101, 7, x_87);
x_102 = lean_st_ref_set(x_11, x_101, x_80);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
x_105 = lean_box(0);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_103);
return x_106;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = lean_ptr_addr(x_1);
x_17 = lean_ptr_addr(x_5);
x_18 = lean_usize_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_array_fset(x_3, x_2, x_5);
x_20 = 1;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_15);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_5);
x_25 = lean_box(x_4);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_15);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_3);
x_19 = l_Lean_Meta_Grind_Canon_shouldCanon(x_1, x_2, x_3, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
switch (x_21) {
case 0:
{
lean_object* x_22; lean_object* x_23; uint64_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_ctor_get_uint64(x_14, sizeof(void*)*7);
x_25 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 8);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_14, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_14, 3);
lean_inc(x_28);
x_29 = lean_ctor_get(x_14, 4);
lean_inc(x_29);
x_30 = lean_ctor_get(x_14, 5);
lean_inc(x_30);
x_31 = lean_ctor_get(x_14, 6);
lean_inc(x_31);
x_32 = !lean_is_exclusive(x_22);
if (x_32 == 0)
{
uint8_t x_33; uint8_t x_34; uint8_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_33 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 9);
x_34 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 10);
x_35 = 1;
lean_ctor_set_uint8(x_22, 9, x_35);
x_36 = 2;
x_37 = lean_uint64_shift_right(x_24, x_36);
x_38 = lean_uint64_shift_left(x_37, x_36);
x_39 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__3___closed__1;
x_40 = lean_uint64_lor(x_38, x_39);
x_41 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_41, 0, x_22);
lean_ctor_set(x_41, 1, x_26);
lean_ctor_set(x_41, 2, x_27);
lean_ctor_set(x_41, 3, x_28);
lean_ctor_set(x_41, 4, x_29);
lean_ctor_set(x_41, 5, x_30);
lean_ctor_set(x_41, 6, x_31);
lean_ctor_set_uint64(x_41, sizeof(void*)*7, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*7 + 8, x_25);
lean_ctor_set_uint8(x_41, sizeof(void*)*7 + 9, x_33);
lean_ctor_set_uint8(x_41, sizeof(void*)*7 + 10, x_34);
x_42 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_2);
x_43 = l_Lean_Meta_Grind_Canon_canonElemCore(x_4, x_5, x_2, x_3, x_42, x_10, x_11, x_12, x_13, x_41, x_15, x_16, x_17, x_23);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__1(x_3, x_2, x_6, x_7, x_44, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_45);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_3);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_43);
if (x_47 == 0)
{
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_43, 0);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_43);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; lean_object* x_71; uint64_t x_72; uint64_t x_73; uint64_t x_74; uint64_t x_75; uint64_t x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_51 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 9);
x_52 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 10);
x_53 = lean_ctor_get_uint8(x_22, 0);
x_54 = lean_ctor_get_uint8(x_22, 1);
x_55 = lean_ctor_get_uint8(x_22, 2);
x_56 = lean_ctor_get_uint8(x_22, 3);
x_57 = lean_ctor_get_uint8(x_22, 4);
x_58 = lean_ctor_get_uint8(x_22, 5);
x_59 = lean_ctor_get_uint8(x_22, 6);
x_60 = lean_ctor_get_uint8(x_22, 7);
x_61 = lean_ctor_get_uint8(x_22, 8);
x_62 = lean_ctor_get_uint8(x_22, 10);
x_63 = lean_ctor_get_uint8(x_22, 11);
x_64 = lean_ctor_get_uint8(x_22, 12);
x_65 = lean_ctor_get_uint8(x_22, 13);
x_66 = lean_ctor_get_uint8(x_22, 14);
x_67 = lean_ctor_get_uint8(x_22, 15);
x_68 = lean_ctor_get_uint8(x_22, 16);
x_69 = lean_ctor_get_uint8(x_22, 17);
lean_dec(x_22);
x_70 = 1;
x_71 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_71, 0, x_53);
lean_ctor_set_uint8(x_71, 1, x_54);
lean_ctor_set_uint8(x_71, 2, x_55);
lean_ctor_set_uint8(x_71, 3, x_56);
lean_ctor_set_uint8(x_71, 4, x_57);
lean_ctor_set_uint8(x_71, 5, x_58);
lean_ctor_set_uint8(x_71, 6, x_59);
lean_ctor_set_uint8(x_71, 7, x_60);
lean_ctor_set_uint8(x_71, 8, x_61);
lean_ctor_set_uint8(x_71, 9, x_70);
lean_ctor_set_uint8(x_71, 10, x_62);
lean_ctor_set_uint8(x_71, 11, x_63);
lean_ctor_set_uint8(x_71, 12, x_64);
lean_ctor_set_uint8(x_71, 13, x_65);
lean_ctor_set_uint8(x_71, 14, x_66);
lean_ctor_set_uint8(x_71, 15, x_67);
lean_ctor_set_uint8(x_71, 16, x_68);
lean_ctor_set_uint8(x_71, 17, x_69);
x_72 = 2;
x_73 = lean_uint64_shift_right(x_24, x_72);
x_74 = lean_uint64_shift_left(x_73, x_72);
x_75 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__3___closed__1;
x_76 = lean_uint64_lor(x_74, x_75);
x_77 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_77, 0, x_71);
lean_ctor_set(x_77, 1, x_26);
lean_ctor_set(x_77, 2, x_27);
lean_ctor_set(x_77, 3, x_28);
lean_ctor_set(x_77, 4, x_29);
lean_ctor_set(x_77, 5, x_30);
lean_ctor_set(x_77, 6, x_31);
lean_ctor_set_uint64(x_77, sizeof(void*)*7, x_76);
lean_ctor_set_uint8(x_77, sizeof(void*)*7 + 8, x_25);
lean_ctor_set_uint8(x_77, sizeof(void*)*7 + 9, x_51);
lean_ctor_set_uint8(x_77, sizeof(void*)*7 + 10, x_52);
x_78 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_2);
x_79 = l_Lean_Meta_Grind_Canon_canonElemCore(x_4, x_5, x_2, x_3, x_78, x_10, x_11, x_12, x_13, x_77, x_15, x_16, x_17, x_23);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__1(x_3, x_2, x_6, x_7, x_80, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_81);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_3);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_83 = lean_ctor_get(x_79, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_79, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_85 = x_79;
} else {
 lean_dec_ref(x_79);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
}
case 1:
{
lean_object* x_87; lean_object* x_88; uint64_t x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_87 = lean_ctor_get(x_14, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_19, 1);
lean_inc(x_88);
lean_dec(x_19);
x_89 = lean_ctor_get_uint64(x_14, sizeof(void*)*7);
x_90 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 8);
x_91 = lean_ctor_get(x_14, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_14, 2);
lean_inc(x_92);
x_93 = lean_ctor_get(x_14, 3);
lean_inc(x_93);
x_94 = lean_ctor_get(x_14, 4);
lean_inc(x_94);
x_95 = lean_ctor_get(x_14, 5);
lean_inc(x_95);
x_96 = lean_ctor_get(x_14, 6);
lean_inc(x_96);
x_97 = !lean_is_exclusive(x_87);
if (x_97 == 0)
{
uint8_t x_98; uint8_t x_99; uint8_t x_100; uint64_t x_101; uint64_t x_102; uint64_t x_103; uint64_t x_104; uint64_t x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; 
x_98 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 9);
x_99 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 10);
x_100 = 3;
lean_ctor_set_uint8(x_87, 9, x_100);
x_101 = 2;
x_102 = lean_uint64_shift_right(x_89, x_101);
x_103 = lean_uint64_shift_left(x_102, x_101);
x_104 = l_Lean_Meta_Grind_Canon_canonInst___closed__1;
x_105 = lean_uint64_lor(x_103, x_104);
x_106 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_106, 0, x_87);
lean_ctor_set(x_106, 1, x_91);
lean_ctor_set(x_106, 2, x_92);
lean_ctor_set(x_106, 3, x_93);
lean_ctor_set(x_106, 4, x_94);
lean_ctor_set(x_106, 5, x_95);
lean_ctor_set(x_106, 6, x_96);
lean_ctor_set_uint64(x_106, sizeof(void*)*7, x_105);
lean_ctor_set_uint8(x_106, sizeof(void*)*7 + 8, x_90);
lean_ctor_set_uint8(x_106, sizeof(void*)*7 + 9, x_98);
lean_ctor_set_uint8(x_106, sizeof(void*)*7 + 10, x_99);
x_107 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_2);
x_108 = l_Lean_Meta_Grind_Canon_canonElemCore(x_4, x_5, x_2, x_3, x_107, x_10, x_11, x_12, x_13, x_106, x_15, x_16, x_17, x_88);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__1(x_3, x_2, x_6, x_7, x_109, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_110);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_3);
return x_111;
}
else
{
uint8_t x_112; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_112 = !lean_is_exclusive(x_108);
if (x_112 == 0)
{
return x_108;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_108, 0);
x_114 = lean_ctor_get(x_108, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_108);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; uint8_t x_132; uint8_t x_133; uint8_t x_134; uint8_t x_135; lean_object* x_136; uint64_t x_137; uint64_t x_138; uint64_t x_139; uint64_t x_140; uint64_t x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; 
x_116 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 9);
x_117 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 10);
x_118 = lean_ctor_get_uint8(x_87, 0);
x_119 = lean_ctor_get_uint8(x_87, 1);
x_120 = lean_ctor_get_uint8(x_87, 2);
x_121 = lean_ctor_get_uint8(x_87, 3);
x_122 = lean_ctor_get_uint8(x_87, 4);
x_123 = lean_ctor_get_uint8(x_87, 5);
x_124 = lean_ctor_get_uint8(x_87, 6);
x_125 = lean_ctor_get_uint8(x_87, 7);
x_126 = lean_ctor_get_uint8(x_87, 8);
x_127 = lean_ctor_get_uint8(x_87, 10);
x_128 = lean_ctor_get_uint8(x_87, 11);
x_129 = lean_ctor_get_uint8(x_87, 12);
x_130 = lean_ctor_get_uint8(x_87, 13);
x_131 = lean_ctor_get_uint8(x_87, 14);
x_132 = lean_ctor_get_uint8(x_87, 15);
x_133 = lean_ctor_get_uint8(x_87, 16);
x_134 = lean_ctor_get_uint8(x_87, 17);
lean_dec(x_87);
x_135 = 3;
x_136 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_136, 0, x_118);
lean_ctor_set_uint8(x_136, 1, x_119);
lean_ctor_set_uint8(x_136, 2, x_120);
lean_ctor_set_uint8(x_136, 3, x_121);
lean_ctor_set_uint8(x_136, 4, x_122);
lean_ctor_set_uint8(x_136, 5, x_123);
lean_ctor_set_uint8(x_136, 6, x_124);
lean_ctor_set_uint8(x_136, 7, x_125);
lean_ctor_set_uint8(x_136, 8, x_126);
lean_ctor_set_uint8(x_136, 9, x_135);
lean_ctor_set_uint8(x_136, 10, x_127);
lean_ctor_set_uint8(x_136, 11, x_128);
lean_ctor_set_uint8(x_136, 12, x_129);
lean_ctor_set_uint8(x_136, 13, x_130);
lean_ctor_set_uint8(x_136, 14, x_131);
lean_ctor_set_uint8(x_136, 15, x_132);
lean_ctor_set_uint8(x_136, 16, x_133);
lean_ctor_set_uint8(x_136, 17, x_134);
x_137 = 2;
x_138 = lean_uint64_shift_right(x_89, x_137);
x_139 = lean_uint64_shift_left(x_138, x_137);
x_140 = l_Lean_Meta_Grind_Canon_canonInst___closed__1;
x_141 = lean_uint64_lor(x_139, x_140);
x_142 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_142, 0, x_136);
lean_ctor_set(x_142, 1, x_91);
lean_ctor_set(x_142, 2, x_92);
lean_ctor_set(x_142, 3, x_93);
lean_ctor_set(x_142, 4, x_94);
lean_ctor_set(x_142, 5, x_95);
lean_ctor_set(x_142, 6, x_96);
lean_ctor_set_uint64(x_142, sizeof(void*)*7, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*7 + 8, x_90);
lean_ctor_set_uint8(x_142, sizeof(void*)*7 + 9, x_116);
lean_ctor_set_uint8(x_142, sizeof(void*)*7 + 10, x_117);
x_143 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_2);
x_144 = l_Lean_Meta_Grind_Canon_canonElemCore(x_4, x_5, x_2, x_3, x_143, x_10, x_11, x_12, x_13, x_142, x_15, x_16, x_17, x_88);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__1(x_3, x_2, x_6, x_7, x_145, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_146);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_3);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_148 = lean_ctor_get(x_144, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_144, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_150 = x_144;
} else {
 lean_dec_ref(x_144);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
}
case 2:
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_19, 1);
lean_inc(x_152);
lean_dec(x_19);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_3);
x_153 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_3, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_152);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint64_t x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_154 = lean_ctor_get(x_14, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
lean_dec(x_153);
x_157 = lean_ctor_get_uint64(x_14, sizeof(void*)*7);
x_158 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 8);
x_159 = lean_ctor_get(x_14, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_14, 2);
lean_inc(x_160);
x_161 = lean_ctor_get(x_14, 3);
lean_inc(x_161);
x_162 = lean_ctor_get(x_14, 4);
lean_inc(x_162);
x_163 = lean_ctor_get(x_14, 5);
lean_inc(x_163);
x_164 = lean_ctor_get(x_14, 6);
lean_inc(x_164);
x_165 = !lean_is_exclusive(x_154);
if (x_165 == 0)
{
uint8_t x_166; uint8_t x_167; uint8_t x_168; uint64_t x_169; uint64_t x_170; uint64_t x_171; uint64_t x_172; uint64_t x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; 
x_166 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 9);
x_167 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 10);
x_168 = 2;
lean_ctor_set_uint8(x_154, 9, x_168);
x_169 = 2;
x_170 = lean_uint64_shift_right(x_157, x_169);
x_171 = lean_uint64_shift_left(x_170, x_169);
x_172 = l_Lean_Meta_Grind_Canon_canonImplicit___closed__1;
x_173 = lean_uint64_lor(x_171, x_172);
x_174 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_174, 0, x_154);
lean_ctor_set(x_174, 1, x_159);
lean_ctor_set(x_174, 2, x_160);
lean_ctor_set(x_174, 3, x_161);
lean_ctor_set(x_174, 4, x_162);
lean_ctor_set(x_174, 5, x_163);
lean_ctor_set(x_174, 6, x_164);
lean_ctor_set_uint64(x_174, sizeof(void*)*7, x_173);
lean_ctor_set_uint8(x_174, sizeof(void*)*7 + 8, x_158);
lean_ctor_set_uint8(x_174, sizeof(void*)*7 + 9, x_166);
lean_ctor_set_uint8(x_174, sizeof(void*)*7 + 10, x_167);
x_175 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
x_176 = l_Lean_Meta_Grind_Canon_canonElemCore(x_4, x_5, x_2, x_155, x_175, x_10, x_11, x_12, x_13, x_174, x_15, x_16, x_17, x_156);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__1(x_3, x_2, x_6, x_7, x_177, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_178);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_3);
return x_179;
}
else
{
uint8_t x_180; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_180 = !lean_is_exclusive(x_176);
if (x_180 == 0)
{
return x_176;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_176, 0);
x_182 = lean_ctor_get(x_176, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_176);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
else
{
uint8_t x_184; uint8_t x_185; uint8_t x_186; uint8_t x_187; uint8_t x_188; uint8_t x_189; uint8_t x_190; uint8_t x_191; uint8_t x_192; uint8_t x_193; uint8_t x_194; uint8_t x_195; uint8_t x_196; uint8_t x_197; uint8_t x_198; uint8_t x_199; uint8_t x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; lean_object* x_204; uint64_t x_205; uint64_t x_206; uint64_t x_207; uint64_t x_208; uint64_t x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; 
x_184 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 9);
x_185 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 10);
x_186 = lean_ctor_get_uint8(x_154, 0);
x_187 = lean_ctor_get_uint8(x_154, 1);
x_188 = lean_ctor_get_uint8(x_154, 2);
x_189 = lean_ctor_get_uint8(x_154, 3);
x_190 = lean_ctor_get_uint8(x_154, 4);
x_191 = lean_ctor_get_uint8(x_154, 5);
x_192 = lean_ctor_get_uint8(x_154, 6);
x_193 = lean_ctor_get_uint8(x_154, 7);
x_194 = lean_ctor_get_uint8(x_154, 8);
x_195 = lean_ctor_get_uint8(x_154, 10);
x_196 = lean_ctor_get_uint8(x_154, 11);
x_197 = lean_ctor_get_uint8(x_154, 12);
x_198 = lean_ctor_get_uint8(x_154, 13);
x_199 = lean_ctor_get_uint8(x_154, 14);
x_200 = lean_ctor_get_uint8(x_154, 15);
x_201 = lean_ctor_get_uint8(x_154, 16);
x_202 = lean_ctor_get_uint8(x_154, 17);
lean_dec(x_154);
x_203 = 2;
x_204 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_204, 0, x_186);
lean_ctor_set_uint8(x_204, 1, x_187);
lean_ctor_set_uint8(x_204, 2, x_188);
lean_ctor_set_uint8(x_204, 3, x_189);
lean_ctor_set_uint8(x_204, 4, x_190);
lean_ctor_set_uint8(x_204, 5, x_191);
lean_ctor_set_uint8(x_204, 6, x_192);
lean_ctor_set_uint8(x_204, 7, x_193);
lean_ctor_set_uint8(x_204, 8, x_194);
lean_ctor_set_uint8(x_204, 9, x_203);
lean_ctor_set_uint8(x_204, 10, x_195);
lean_ctor_set_uint8(x_204, 11, x_196);
lean_ctor_set_uint8(x_204, 12, x_197);
lean_ctor_set_uint8(x_204, 13, x_198);
lean_ctor_set_uint8(x_204, 14, x_199);
lean_ctor_set_uint8(x_204, 15, x_200);
lean_ctor_set_uint8(x_204, 16, x_201);
lean_ctor_set_uint8(x_204, 17, x_202);
x_205 = 2;
x_206 = lean_uint64_shift_right(x_157, x_205);
x_207 = lean_uint64_shift_left(x_206, x_205);
x_208 = l_Lean_Meta_Grind_Canon_canonImplicit___closed__1;
x_209 = lean_uint64_lor(x_207, x_208);
x_210 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_210, 0, x_204);
lean_ctor_set(x_210, 1, x_159);
lean_ctor_set(x_210, 2, x_160);
lean_ctor_set(x_210, 3, x_161);
lean_ctor_set(x_210, 4, x_162);
lean_ctor_set(x_210, 5, x_163);
lean_ctor_set(x_210, 6, x_164);
lean_ctor_set_uint64(x_210, sizeof(void*)*7, x_209);
lean_ctor_set_uint8(x_210, sizeof(void*)*7 + 8, x_158);
lean_ctor_set_uint8(x_210, sizeof(void*)*7 + 9, x_184);
lean_ctor_set_uint8(x_210, sizeof(void*)*7 + 10, x_185);
x_211 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
x_212 = l_Lean_Meta_Grind_Canon_canonElemCore(x_4, x_5, x_2, x_155, x_211, x_10, x_11, x_12, x_13, x_210, x_15, x_16, x_17, x_156);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__1(x_3, x_2, x_6, x_7, x_213, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_214);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_3);
return x_215;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_216 = lean_ctor_get(x_212, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_212, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_218 = x_212;
} else {
 lean_dec_ref(x_212);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(1, 2, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_217);
return x_219;
}
}
}
else
{
uint8_t x_220; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_220 = !lean_is_exclusive(x_153);
if (x_220 == 0)
{
return x_153;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_153, 0);
x_222 = lean_ctor_get(x_153, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_153);
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
return x_223;
}
}
}
default: 
{
lean_object* x_224; lean_object* x_225; 
lean_dec(x_5);
lean_dec(x_4);
x_224 = lean_ctor_get(x_19, 1);
lean_inc(x_224);
lean_dec(x_19);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_3);
x_225 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_3, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_224);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec(x_225);
x_228 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__1(x_3, x_2, x_6, x_7, x_226, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_227);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_3);
return x_228;
}
else
{
uint8_t x_229; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_229 = !lean_is_exclusive(x_225);
if (x_229 == 0)
{
return x_225;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_225, 0);
x_231 = lean_ctor_get(x_225, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_225);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
}
}
else
{
uint8_t x_233; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_233 = !lean_is_exclusive(x_19);
if (x_233 == 0)
{
return x_19;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_19, 0);
x_235 = lean_ctor_get(x_19, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_19);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]: ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" : ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_array_fget(x_16, x_2);
x_19 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__2;
x_20 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8(x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = lean_unbox(x_17);
lean_dec(x_17);
x_26 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__2(x_3, x_2, x_18, x_4, x_5, x_16, x_25, x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_23);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_28 = x_20;
} else {
 lean_dec_ref(x_20);
 x_28 = lean_box(0);
}
x_29 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_18);
x_31 = l_Lean_Meta_Grind_Canon_shouldCanon(x_3, x_2, x_18, x_11, x_12, x_13, x_14, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_18);
x_34 = lean_infer_type(x_18, x_11, x_12, x_13, x_14, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_57; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_18);
x_37 = l_Lean_MessageData_ofExpr(x_18);
x_38 = l_Lean_MessageData_ofExpr(x_35);
x_57 = lean_unbox(x_32);
lean_dec(x_32);
switch (x_57) {
case 0:
{
lean_object* x_58; 
x_58 = l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__2;
x_39 = x_58;
goto block_56;
}
case 1:
{
lean_object* x_59; 
x_59 = l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__4;
x_39 = x_59;
goto block_56;
}
case 2:
{
lean_object* x_60; 
x_60 = l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__6;
x_39 = x_60;
goto block_56;
}
default: 
{
lean_object* x_61; 
x_61 = l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__8;
x_39 = x_61;
goto block_56;
}
}
block_56:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_40 = l_Lean_MessageData_ofFormat(x_39);
x_41 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__2;
if (lean_is_scalar(x_28)) {
 x_42 = lean_alloc_ctor(7, 2, 0);
} else {
 x_42 = x_28;
 lean_ctor_set_tag(x_42, 7);
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__4;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_37);
x_46 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__6;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_38);
x_49 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10;
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9(x_19, x_50, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_36);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_unbox(x_17);
lean_dec(x_17);
x_55 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__2(x_3, x_2, x_18, x_4, x_5, x_16, x_54, x_52, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_53);
lean_dec(x_52);
return x_55;
}
}
else
{
uint8_t x_62; 
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_34);
if (x_62 == 0)
{
return x_34;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_34, 0);
x_64 = lean_ctor_get(x_34, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_34);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_28);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_31);
if (x_66 == 0)
{
return x_31;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_31, 0);
x_68 = lean_ctor_get(x_31, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_31);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_28);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_29);
if (x_70 == 0)
{
return x_29;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_29, 0);
x_72 = lean_ctor_get(x_29, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_29);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27) {
_start:
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_28 = lean_ctor_get(x_17, 0);
lean_inc(x_28);
lean_dec(x_17);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_apply_12(x_30, lean_box(0), x_28, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_17, 0);
lean_inc(x_32);
lean_dec(x_17);
x_33 = lean_ctor_get(x_2, 2);
lean_inc(x_33);
x_34 = lean_nat_add(x_3, x_33);
lean_dec(x_33);
x_35 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_4, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_2, x_32, x_34, lean_box(0), lean_box(0), x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29) {
_start:
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
x_31 = lean_nat_dec_lt(x_17, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = lean_ctor_get(x_2, 0);
lean_inc(x_32);
lean_dec(x_2);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_apply_12(x_33, lean_box(0), x_16, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
lean_inc(x_9);
lean_inc(x_1);
lean_inc(x_12);
lean_inc(x_17);
x_36 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___boxed), 15, 5);
lean_closure_set(x_36, 0, x_16);
lean_closure_set(x_36, 1, x_17);
lean_closure_set(x_36, 2, x_12);
lean_closure_set(x_36, 3, x_1);
lean_closure_set(x_36, 4, x_9);
x_37 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__4___boxed), 27, 16);
lean_closure_set(x_37, 0, x_2);
lean_closure_set(x_37, 1, x_15);
lean_closure_set(x_37, 2, x_17);
lean_closure_set(x_37, 3, x_1);
lean_closure_set(x_37, 4, x_3);
lean_closure_set(x_37, 5, x_4);
lean_closure_set(x_37, 6, x_5);
lean_closure_set(x_37, 7, x_6);
lean_closure_set(x_37, 8, x_7);
lean_closure_set(x_37, 9, x_8);
lean_closure_set(x_37, 10, x_9);
lean_closure_set(x_37, 11, x_10);
lean_closure_set(x_37, 12, x_11);
lean_closure_set(x_37, 13, x_12);
lean_closure_set(x_37, 14, x_13);
lean_closure_set(x_37, 15, x_14);
x_38 = lean_apply_14(x_35, lean_box(0), lean_box(0), x_36, x_37, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29);
return x_38;
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_lift), 4, 3);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
lean_closure_set(x_1, 2, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("nestedProof", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__2;
x_2 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__3;
x_3 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__4;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_22; lean_object* x_176; lean_object* x_214; uint8_t x_215; 
lean_dec(x_11);
x_214 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_215 = l_Lean_Expr_isConstOf(x_9, x_214);
if (x_215 == 0)
{
lean_object* x_216; 
x_216 = lean_box(0);
x_176 = x_216;
goto block_213;
}
else
{
lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_217 = lean_array_get_size(x_10);
x_218 = lean_unsigned_to_nat(2u);
x_219 = lean_nat_dec_eq(x_217, x_218);
if (x_219 == 0)
{
lean_object* x_220; 
lean_dec(x_217);
x_220 = lean_box(0);
x_176 = x_220;
goto block_213;
}
else
{
lean_object* x_221; uint8_t x_222; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_221 = lean_unsigned_to_nat(0u);
x_222 = lean_nat_dec_lt(x_221, x_217);
lean_dec(x_217);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; 
x_223 = l_Lean_instInhabitedExpr;
x_224 = l_outOfBounds___rarg(x_223);
x_22 = x_224;
goto block_175;
}
else
{
lean_object* x_225; 
x_225 = lean_array_fget(x_10, x_221);
x_22 = x_225;
goto block_175;
}
}
}
block_175:
{
lean_object* x_23; 
lean_inc(x_13);
lean_inc(x_22);
x_23 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_22, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_get(x_13, x_25);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_30, 2);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_31, x_24);
if (lean_obj_tag(x_32) == 0)
{
size_t x_33; size_t x_34; uint8_t x_35; 
lean_free_object(x_26);
x_33 = lean_ptr_addr(x_22);
lean_dec(x_22);
x_34 = lean_ptr_addr(x_24);
x_35 = lean_usize_dec_eq(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_1);
x_36 = lean_unsigned_to_nat(0u);
lean_inc(x_24);
x_37 = lean_array_set(x_10, x_36, x_24);
x_38 = l_Lean_mkAppN(x_9, x_37);
lean_dec(x_37);
x_39 = lean_st_ref_take(x_13, x_29);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 2);
lean_inc(x_46);
lean_dec(x_43);
lean_inc(x_38);
x_47 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_46, x_24, x_38);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_45);
lean_ctor_set(x_48, 2, x_47);
x_49 = lean_ctor_get(x_40, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_40, 3);
lean_inc(x_50);
x_51 = lean_ctor_get(x_40, 4);
lean_inc(x_51);
x_52 = lean_ctor_get(x_40, 5);
lean_inc(x_52);
x_53 = lean_ctor_get(x_40, 6);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_40, sizeof(void*)*15);
x_55 = lean_ctor_get(x_40, 7);
lean_inc(x_55);
x_56 = lean_ctor_get(x_40, 8);
lean_inc(x_56);
x_57 = lean_ctor_get(x_40, 9);
lean_inc(x_57);
x_58 = lean_ctor_get(x_40, 10);
lean_inc(x_58);
x_59 = lean_ctor_get(x_40, 11);
lean_inc(x_59);
x_60 = lean_ctor_get(x_40, 12);
lean_inc(x_60);
x_61 = lean_ctor_get(x_40, 13);
lean_inc(x_61);
x_62 = lean_ctor_get(x_40, 14);
lean_inc(x_62);
lean_dec(x_40);
x_63 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_63, 0, x_42);
lean_ctor_set(x_63, 1, x_48);
lean_ctor_set(x_63, 2, x_49);
lean_ctor_set(x_63, 3, x_50);
lean_ctor_set(x_63, 4, x_51);
lean_ctor_set(x_63, 5, x_52);
lean_ctor_set(x_63, 6, x_53);
lean_ctor_set(x_63, 7, x_55);
lean_ctor_set(x_63, 8, x_56);
lean_ctor_set(x_63, 9, x_57);
lean_ctor_set(x_63, 10, x_58);
lean_ctor_set(x_63, 11, x_59);
lean_ctor_set(x_63, 12, x_60);
lean_ctor_set(x_63, 13, x_61);
lean_ctor_set(x_63, 14, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*15, x_54);
x_64 = lean_st_ref_set(x_13, x_63, x_41);
lean_dec(x_13);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
lean_ctor_set(x_64, 0, x_38);
return x_64;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_38);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
lean_dec(x_10);
lean_dec(x_9);
x_69 = lean_st_ref_take(x_13, x_29);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 2);
lean_inc(x_76);
lean_dec(x_73);
lean_inc(x_1);
x_77 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_76, x_24, x_1);
x_78 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_78, 0, x_74);
lean_ctor_set(x_78, 1, x_75);
lean_ctor_set(x_78, 2, x_77);
x_79 = lean_ctor_get(x_70, 2);
lean_inc(x_79);
x_80 = lean_ctor_get(x_70, 3);
lean_inc(x_80);
x_81 = lean_ctor_get(x_70, 4);
lean_inc(x_81);
x_82 = lean_ctor_get(x_70, 5);
lean_inc(x_82);
x_83 = lean_ctor_get(x_70, 6);
lean_inc(x_83);
x_84 = lean_ctor_get_uint8(x_70, sizeof(void*)*15);
x_85 = lean_ctor_get(x_70, 7);
lean_inc(x_85);
x_86 = lean_ctor_get(x_70, 8);
lean_inc(x_86);
x_87 = lean_ctor_get(x_70, 9);
lean_inc(x_87);
x_88 = lean_ctor_get(x_70, 10);
lean_inc(x_88);
x_89 = lean_ctor_get(x_70, 11);
lean_inc(x_89);
x_90 = lean_ctor_get(x_70, 12);
lean_inc(x_90);
x_91 = lean_ctor_get(x_70, 13);
lean_inc(x_91);
x_92 = lean_ctor_get(x_70, 14);
lean_inc(x_92);
lean_dec(x_70);
x_93 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_93, 0, x_72);
lean_ctor_set(x_93, 1, x_78);
lean_ctor_set(x_93, 2, x_79);
lean_ctor_set(x_93, 3, x_80);
lean_ctor_set(x_93, 4, x_81);
lean_ctor_set(x_93, 5, x_82);
lean_ctor_set(x_93, 6, x_83);
lean_ctor_set(x_93, 7, x_85);
lean_ctor_set(x_93, 8, x_86);
lean_ctor_set(x_93, 9, x_87);
lean_ctor_set(x_93, 10, x_88);
lean_ctor_set(x_93, 11, x_89);
lean_ctor_set(x_93, 12, x_90);
lean_ctor_set(x_93, 13, x_91);
lean_ctor_set(x_93, 14, x_92);
lean_ctor_set_uint8(x_93, sizeof(void*)*15, x_84);
x_94 = lean_st_ref_set(x_13, x_93, x_71);
lean_dec(x_13);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_94, 0);
lean_dec(x_96);
lean_ctor_set(x_94, 0, x_1);
return x_94;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_1);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
lean_object* x_99; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_99 = lean_ctor_get(x_32, 0);
lean_inc(x_99);
lean_dec(x_32);
lean_ctor_set(x_26, 0, x_99);
return x_26;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_26, 0);
x_101 = lean_ctor_get(x_26, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_26);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_ctor_get(x_102, 2);
lean_inc(x_103);
lean_dec(x_102);
x_104 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_103, x_24);
if (lean_obj_tag(x_104) == 0)
{
size_t x_105; size_t x_106; uint8_t x_107; 
x_105 = lean_ptr_addr(x_22);
lean_dec(x_22);
x_106 = lean_ptr_addr(x_24);
x_107 = lean_usize_dec_eq(x_105, x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_1);
x_108 = lean_unsigned_to_nat(0u);
lean_inc(x_24);
x_109 = lean_array_set(x_10, x_108, x_24);
x_110 = l_Lean_mkAppN(x_9, x_109);
lean_dec(x_109);
x_111 = lean_st_ref_take(x_13, x_101);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_115, 2);
lean_inc(x_118);
lean_dec(x_115);
lean_inc(x_110);
x_119 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_118, x_24, x_110);
x_120 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_120, 0, x_116);
lean_ctor_set(x_120, 1, x_117);
lean_ctor_set(x_120, 2, x_119);
x_121 = lean_ctor_get(x_112, 2);
lean_inc(x_121);
x_122 = lean_ctor_get(x_112, 3);
lean_inc(x_122);
x_123 = lean_ctor_get(x_112, 4);
lean_inc(x_123);
x_124 = lean_ctor_get(x_112, 5);
lean_inc(x_124);
x_125 = lean_ctor_get(x_112, 6);
lean_inc(x_125);
x_126 = lean_ctor_get_uint8(x_112, sizeof(void*)*15);
x_127 = lean_ctor_get(x_112, 7);
lean_inc(x_127);
x_128 = lean_ctor_get(x_112, 8);
lean_inc(x_128);
x_129 = lean_ctor_get(x_112, 9);
lean_inc(x_129);
x_130 = lean_ctor_get(x_112, 10);
lean_inc(x_130);
x_131 = lean_ctor_get(x_112, 11);
lean_inc(x_131);
x_132 = lean_ctor_get(x_112, 12);
lean_inc(x_132);
x_133 = lean_ctor_get(x_112, 13);
lean_inc(x_133);
x_134 = lean_ctor_get(x_112, 14);
lean_inc(x_134);
lean_dec(x_112);
x_135 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_135, 0, x_114);
lean_ctor_set(x_135, 1, x_120);
lean_ctor_set(x_135, 2, x_121);
lean_ctor_set(x_135, 3, x_122);
lean_ctor_set(x_135, 4, x_123);
lean_ctor_set(x_135, 5, x_124);
lean_ctor_set(x_135, 6, x_125);
lean_ctor_set(x_135, 7, x_127);
lean_ctor_set(x_135, 8, x_128);
lean_ctor_set(x_135, 9, x_129);
lean_ctor_set(x_135, 10, x_130);
lean_ctor_set(x_135, 11, x_131);
lean_ctor_set(x_135, 12, x_132);
lean_ctor_set(x_135, 13, x_133);
lean_ctor_set(x_135, 14, x_134);
lean_ctor_set_uint8(x_135, sizeof(void*)*15, x_126);
x_136 = lean_st_ref_set(x_13, x_135, x_113);
lean_dec(x_13);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_138 = x_136;
} else {
 lean_dec_ref(x_136);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_110);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_10);
lean_dec(x_9);
x_140 = lean_st_ref_take(x_13, x_101);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_ctor_get(x_141, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_144, 2);
lean_inc(x_147);
lean_dec(x_144);
lean_inc(x_1);
x_148 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_147, x_24, x_1);
x_149 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_149, 0, x_145);
lean_ctor_set(x_149, 1, x_146);
lean_ctor_set(x_149, 2, x_148);
x_150 = lean_ctor_get(x_141, 2);
lean_inc(x_150);
x_151 = lean_ctor_get(x_141, 3);
lean_inc(x_151);
x_152 = lean_ctor_get(x_141, 4);
lean_inc(x_152);
x_153 = lean_ctor_get(x_141, 5);
lean_inc(x_153);
x_154 = lean_ctor_get(x_141, 6);
lean_inc(x_154);
x_155 = lean_ctor_get_uint8(x_141, sizeof(void*)*15);
x_156 = lean_ctor_get(x_141, 7);
lean_inc(x_156);
x_157 = lean_ctor_get(x_141, 8);
lean_inc(x_157);
x_158 = lean_ctor_get(x_141, 9);
lean_inc(x_158);
x_159 = lean_ctor_get(x_141, 10);
lean_inc(x_159);
x_160 = lean_ctor_get(x_141, 11);
lean_inc(x_160);
x_161 = lean_ctor_get(x_141, 12);
lean_inc(x_161);
x_162 = lean_ctor_get(x_141, 13);
lean_inc(x_162);
x_163 = lean_ctor_get(x_141, 14);
lean_inc(x_163);
lean_dec(x_141);
x_164 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_164, 0, x_143);
lean_ctor_set(x_164, 1, x_149);
lean_ctor_set(x_164, 2, x_150);
lean_ctor_set(x_164, 3, x_151);
lean_ctor_set(x_164, 4, x_152);
lean_ctor_set(x_164, 5, x_153);
lean_ctor_set(x_164, 6, x_154);
lean_ctor_set(x_164, 7, x_156);
lean_ctor_set(x_164, 8, x_157);
lean_ctor_set(x_164, 9, x_158);
lean_ctor_set(x_164, 10, x_159);
lean_ctor_set(x_164, 11, x_160);
lean_ctor_set(x_164, 12, x_161);
lean_ctor_set(x_164, 13, x_162);
lean_ctor_set(x_164, 14, x_163);
lean_ctor_set_uint8(x_164, sizeof(void*)*15, x_155);
x_165 = lean_st_ref_set(x_13, x_164, x_142);
lean_dec(x_13);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_167 = x_165;
} else {
 lean_dec_ref(x_165);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_1);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_169 = lean_ctor_get(x_104, 0);
lean_inc(x_169);
lean_dec(x_104);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_101);
return x_170;
}
}
}
else
{
uint8_t x_171; 
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_171 = !lean_is_exclusive(x_23);
if (x_171 == 0)
{
return x_23;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_23, 0);
x_173 = lean_ctor_get(x_23, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_23);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
block_213:
{
lean_object* x_177; 
lean_dec(x_176);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_9);
x_177 = l_Lean_Meta_getFunInfo(x_9, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_ctor_get(x_178, 0);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_array_get_size(x_10);
x_182 = lean_unsigned_to_nat(0u);
x_183 = lean_unsigned_to_nat(1u);
lean_inc(x_181);
x_184 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_181);
lean_ctor_set(x_184, 2, x_183);
x_185 = 0;
x_186 = lean_box(x_185);
lean_inc(x_10);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_10);
lean_ctor_set(x_187, 1, x_186);
x_188 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_184);
lean_inc(x_9);
lean_inc(x_1);
x_189 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_188, x_180, x_181, x_184, x_184, x_187, x_182, lean_box(0), lean_box(0), x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_179);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
x_192 = lean_unbox(x_191);
lean_dec(x_191);
if (x_192 == 0)
{
uint8_t x_193; 
lean_dec(x_190);
lean_dec(x_9);
x_193 = !lean_is_exclusive(x_189);
if (x_193 == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_189, 0);
lean_dec(x_194);
lean_ctor_set(x_189, 0, x_1);
return x_189;
}
else
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_189, 1);
lean_inc(x_195);
lean_dec(x_189);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_1);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
else
{
uint8_t x_197; 
lean_dec(x_1);
x_197 = !lean_is_exclusive(x_189);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_189, 0);
lean_dec(x_198);
x_199 = lean_ctor_get(x_190, 0);
lean_inc(x_199);
lean_dec(x_190);
x_200 = l_Lean_mkAppN(x_9, x_199);
lean_dec(x_199);
lean_ctor_set(x_189, 0, x_200);
return x_189;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_201 = lean_ctor_get(x_189, 1);
lean_inc(x_201);
lean_dec(x_189);
x_202 = lean_ctor_get(x_190, 0);
lean_inc(x_202);
lean_dec(x_190);
x_203 = l_Lean_mkAppN(x_9, x_202);
lean_dec(x_202);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_201);
return x_204;
}
}
}
else
{
uint8_t x_205; 
lean_dec(x_9);
lean_dec(x_1);
x_205 = !lean_is_exclusive(x_189);
if (x_205 == 0)
{
return x_189;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_189, 0);
x_207 = lean_ctor_get(x_189, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_189);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
else
{
uint8_t x_209; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_209 = !lean_is_exclusive(x_177);
if (x_209 == 0)
{
return x_177;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_177, 0);
x_211 = lean_ctor_get(x_177, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_177);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
}
}
case 1:
{
lean_object* x_226; lean_object* x_380; lean_object* x_418; uint8_t x_419; 
lean_dec(x_11);
x_418 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_419 = l_Lean_Expr_isConstOf(x_9, x_418);
if (x_419 == 0)
{
lean_object* x_420; 
x_420 = lean_box(0);
x_380 = x_420;
goto block_417;
}
else
{
lean_object* x_421; lean_object* x_422; uint8_t x_423; 
x_421 = lean_array_get_size(x_10);
x_422 = lean_unsigned_to_nat(2u);
x_423 = lean_nat_dec_eq(x_421, x_422);
if (x_423 == 0)
{
lean_object* x_424; 
lean_dec(x_421);
x_424 = lean_box(0);
x_380 = x_424;
goto block_417;
}
else
{
lean_object* x_425; uint8_t x_426; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_425 = lean_unsigned_to_nat(0u);
x_426 = lean_nat_dec_lt(x_425, x_421);
lean_dec(x_421);
if (x_426 == 0)
{
lean_object* x_427; lean_object* x_428; 
x_427 = l_Lean_instInhabitedExpr;
x_428 = l_outOfBounds___rarg(x_427);
x_226 = x_428;
goto block_379;
}
else
{
lean_object* x_429; 
x_429 = lean_array_fget(x_10, x_425);
x_226 = x_429;
goto block_379;
}
}
}
block_379:
{
lean_object* x_227; 
lean_inc(x_13);
lean_inc(x_226);
x_227 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_226, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = lean_st_ref_get(x_13, x_229);
x_231 = !lean_is_exclusive(x_230);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_232 = lean_ctor_get(x_230, 0);
x_233 = lean_ctor_get(x_230, 1);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = lean_ctor_get(x_234, 2);
lean_inc(x_235);
lean_dec(x_234);
x_236 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_235, x_228);
if (lean_obj_tag(x_236) == 0)
{
size_t x_237; size_t x_238; uint8_t x_239; 
lean_free_object(x_230);
x_237 = lean_ptr_addr(x_226);
lean_dec(x_226);
x_238 = lean_ptr_addr(x_228);
x_239 = lean_usize_dec_eq(x_237, x_238);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
lean_dec(x_1);
x_240 = lean_unsigned_to_nat(0u);
lean_inc(x_228);
x_241 = lean_array_set(x_10, x_240, x_228);
x_242 = l_Lean_mkAppN(x_9, x_241);
lean_dec(x_241);
x_243 = lean_st_ref_take(x_13, x_233);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
x_246 = lean_ctor_get(x_244, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_244, 1);
lean_inc(x_247);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
x_250 = lean_ctor_get(x_247, 2);
lean_inc(x_250);
lean_dec(x_247);
lean_inc(x_242);
x_251 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_250, x_228, x_242);
x_252 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_252, 0, x_248);
lean_ctor_set(x_252, 1, x_249);
lean_ctor_set(x_252, 2, x_251);
x_253 = lean_ctor_get(x_244, 2);
lean_inc(x_253);
x_254 = lean_ctor_get(x_244, 3);
lean_inc(x_254);
x_255 = lean_ctor_get(x_244, 4);
lean_inc(x_255);
x_256 = lean_ctor_get(x_244, 5);
lean_inc(x_256);
x_257 = lean_ctor_get(x_244, 6);
lean_inc(x_257);
x_258 = lean_ctor_get_uint8(x_244, sizeof(void*)*15);
x_259 = lean_ctor_get(x_244, 7);
lean_inc(x_259);
x_260 = lean_ctor_get(x_244, 8);
lean_inc(x_260);
x_261 = lean_ctor_get(x_244, 9);
lean_inc(x_261);
x_262 = lean_ctor_get(x_244, 10);
lean_inc(x_262);
x_263 = lean_ctor_get(x_244, 11);
lean_inc(x_263);
x_264 = lean_ctor_get(x_244, 12);
lean_inc(x_264);
x_265 = lean_ctor_get(x_244, 13);
lean_inc(x_265);
x_266 = lean_ctor_get(x_244, 14);
lean_inc(x_266);
lean_dec(x_244);
x_267 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_267, 0, x_246);
lean_ctor_set(x_267, 1, x_252);
lean_ctor_set(x_267, 2, x_253);
lean_ctor_set(x_267, 3, x_254);
lean_ctor_set(x_267, 4, x_255);
lean_ctor_set(x_267, 5, x_256);
lean_ctor_set(x_267, 6, x_257);
lean_ctor_set(x_267, 7, x_259);
lean_ctor_set(x_267, 8, x_260);
lean_ctor_set(x_267, 9, x_261);
lean_ctor_set(x_267, 10, x_262);
lean_ctor_set(x_267, 11, x_263);
lean_ctor_set(x_267, 12, x_264);
lean_ctor_set(x_267, 13, x_265);
lean_ctor_set(x_267, 14, x_266);
lean_ctor_set_uint8(x_267, sizeof(void*)*15, x_258);
x_268 = lean_st_ref_set(x_13, x_267, x_245);
lean_dec(x_13);
x_269 = !lean_is_exclusive(x_268);
if (x_269 == 0)
{
lean_object* x_270; 
x_270 = lean_ctor_get(x_268, 0);
lean_dec(x_270);
lean_ctor_set(x_268, 0, x_242);
return x_268;
}
else
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_268, 1);
lean_inc(x_271);
lean_dec(x_268);
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_242);
lean_ctor_set(x_272, 1, x_271);
return x_272;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
lean_dec(x_10);
lean_dec(x_9);
x_273 = lean_st_ref_take(x_13, x_233);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec(x_273);
x_276 = lean_ctor_get(x_274, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_274, 1);
lean_inc(x_277);
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
x_280 = lean_ctor_get(x_277, 2);
lean_inc(x_280);
lean_dec(x_277);
lean_inc(x_1);
x_281 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_280, x_228, x_1);
x_282 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_282, 0, x_278);
lean_ctor_set(x_282, 1, x_279);
lean_ctor_set(x_282, 2, x_281);
x_283 = lean_ctor_get(x_274, 2);
lean_inc(x_283);
x_284 = lean_ctor_get(x_274, 3);
lean_inc(x_284);
x_285 = lean_ctor_get(x_274, 4);
lean_inc(x_285);
x_286 = lean_ctor_get(x_274, 5);
lean_inc(x_286);
x_287 = lean_ctor_get(x_274, 6);
lean_inc(x_287);
x_288 = lean_ctor_get_uint8(x_274, sizeof(void*)*15);
x_289 = lean_ctor_get(x_274, 7);
lean_inc(x_289);
x_290 = lean_ctor_get(x_274, 8);
lean_inc(x_290);
x_291 = lean_ctor_get(x_274, 9);
lean_inc(x_291);
x_292 = lean_ctor_get(x_274, 10);
lean_inc(x_292);
x_293 = lean_ctor_get(x_274, 11);
lean_inc(x_293);
x_294 = lean_ctor_get(x_274, 12);
lean_inc(x_294);
x_295 = lean_ctor_get(x_274, 13);
lean_inc(x_295);
x_296 = lean_ctor_get(x_274, 14);
lean_inc(x_296);
lean_dec(x_274);
x_297 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_297, 0, x_276);
lean_ctor_set(x_297, 1, x_282);
lean_ctor_set(x_297, 2, x_283);
lean_ctor_set(x_297, 3, x_284);
lean_ctor_set(x_297, 4, x_285);
lean_ctor_set(x_297, 5, x_286);
lean_ctor_set(x_297, 6, x_287);
lean_ctor_set(x_297, 7, x_289);
lean_ctor_set(x_297, 8, x_290);
lean_ctor_set(x_297, 9, x_291);
lean_ctor_set(x_297, 10, x_292);
lean_ctor_set(x_297, 11, x_293);
lean_ctor_set(x_297, 12, x_294);
lean_ctor_set(x_297, 13, x_295);
lean_ctor_set(x_297, 14, x_296);
lean_ctor_set_uint8(x_297, sizeof(void*)*15, x_288);
x_298 = lean_st_ref_set(x_13, x_297, x_275);
lean_dec(x_13);
x_299 = !lean_is_exclusive(x_298);
if (x_299 == 0)
{
lean_object* x_300; 
x_300 = lean_ctor_get(x_298, 0);
lean_dec(x_300);
lean_ctor_set(x_298, 0, x_1);
return x_298;
}
else
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_ctor_get(x_298, 1);
lean_inc(x_301);
lean_dec(x_298);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_1);
lean_ctor_set(x_302, 1, x_301);
return x_302;
}
}
}
else
{
lean_object* x_303; 
lean_dec(x_228);
lean_dec(x_226);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_303 = lean_ctor_get(x_236, 0);
lean_inc(x_303);
lean_dec(x_236);
lean_ctor_set(x_230, 0, x_303);
return x_230;
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_304 = lean_ctor_get(x_230, 0);
x_305 = lean_ctor_get(x_230, 1);
lean_inc(x_305);
lean_inc(x_304);
lean_dec(x_230);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
lean_dec(x_304);
x_307 = lean_ctor_get(x_306, 2);
lean_inc(x_307);
lean_dec(x_306);
x_308 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_307, x_228);
if (lean_obj_tag(x_308) == 0)
{
size_t x_309; size_t x_310; uint8_t x_311; 
x_309 = lean_ptr_addr(x_226);
lean_dec(x_226);
x_310 = lean_ptr_addr(x_228);
x_311 = lean_usize_dec_eq(x_309, x_310);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
lean_dec(x_1);
x_312 = lean_unsigned_to_nat(0u);
lean_inc(x_228);
x_313 = lean_array_set(x_10, x_312, x_228);
x_314 = l_Lean_mkAppN(x_9, x_313);
lean_dec(x_313);
x_315 = lean_st_ref_take(x_13, x_305);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
x_318 = lean_ctor_get(x_316, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_316, 1);
lean_inc(x_319);
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_319, 1);
lean_inc(x_321);
x_322 = lean_ctor_get(x_319, 2);
lean_inc(x_322);
lean_dec(x_319);
lean_inc(x_314);
x_323 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_322, x_228, x_314);
x_324 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_324, 0, x_320);
lean_ctor_set(x_324, 1, x_321);
lean_ctor_set(x_324, 2, x_323);
x_325 = lean_ctor_get(x_316, 2);
lean_inc(x_325);
x_326 = lean_ctor_get(x_316, 3);
lean_inc(x_326);
x_327 = lean_ctor_get(x_316, 4);
lean_inc(x_327);
x_328 = lean_ctor_get(x_316, 5);
lean_inc(x_328);
x_329 = lean_ctor_get(x_316, 6);
lean_inc(x_329);
x_330 = lean_ctor_get_uint8(x_316, sizeof(void*)*15);
x_331 = lean_ctor_get(x_316, 7);
lean_inc(x_331);
x_332 = lean_ctor_get(x_316, 8);
lean_inc(x_332);
x_333 = lean_ctor_get(x_316, 9);
lean_inc(x_333);
x_334 = lean_ctor_get(x_316, 10);
lean_inc(x_334);
x_335 = lean_ctor_get(x_316, 11);
lean_inc(x_335);
x_336 = lean_ctor_get(x_316, 12);
lean_inc(x_336);
x_337 = lean_ctor_get(x_316, 13);
lean_inc(x_337);
x_338 = lean_ctor_get(x_316, 14);
lean_inc(x_338);
lean_dec(x_316);
x_339 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_339, 0, x_318);
lean_ctor_set(x_339, 1, x_324);
lean_ctor_set(x_339, 2, x_325);
lean_ctor_set(x_339, 3, x_326);
lean_ctor_set(x_339, 4, x_327);
lean_ctor_set(x_339, 5, x_328);
lean_ctor_set(x_339, 6, x_329);
lean_ctor_set(x_339, 7, x_331);
lean_ctor_set(x_339, 8, x_332);
lean_ctor_set(x_339, 9, x_333);
lean_ctor_set(x_339, 10, x_334);
lean_ctor_set(x_339, 11, x_335);
lean_ctor_set(x_339, 12, x_336);
lean_ctor_set(x_339, 13, x_337);
lean_ctor_set(x_339, 14, x_338);
lean_ctor_set_uint8(x_339, sizeof(void*)*15, x_330);
x_340 = lean_st_ref_set(x_13, x_339, x_317);
lean_dec(x_13);
x_341 = lean_ctor_get(x_340, 1);
lean_inc(x_341);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 x_342 = x_340;
} else {
 lean_dec_ref(x_340);
 x_342 = lean_box(0);
}
if (lean_is_scalar(x_342)) {
 x_343 = lean_alloc_ctor(0, 2, 0);
} else {
 x_343 = x_342;
}
lean_ctor_set(x_343, 0, x_314);
lean_ctor_set(x_343, 1, x_341);
return x_343;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
lean_dec(x_10);
lean_dec(x_9);
x_344 = lean_st_ref_take(x_13, x_305);
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_344, 1);
lean_inc(x_346);
lean_dec(x_344);
x_347 = lean_ctor_get(x_345, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_345, 1);
lean_inc(x_348);
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
x_351 = lean_ctor_get(x_348, 2);
lean_inc(x_351);
lean_dec(x_348);
lean_inc(x_1);
x_352 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_351, x_228, x_1);
x_353 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_353, 0, x_349);
lean_ctor_set(x_353, 1, x_350);
lean_ctor_set(x_353, 2, x_352);
x_354 = lean_ctor_get(x_345, 2);
lean_inc(x_354);
x_355 = lean_ctor_get(x_345, 3);
lean_inc(x_355);
x_356 = lean_ctor_get(x_345, 4);
lean_inc(x_356);
x_357 = lean_ctor_get(x_345, 5);
lean_inc(x_357);
x_358 = lean_ctor_get(x_345, 6);
lean_inc(x_358);
x_359 = lean_ctor_get_uint8(x_345, sizeof(void*)*15);
x_360 = lean_ctor_get(x_345, 7);
lean_inc(x_360);
x_361 = lean_ctor_get(x_345, 8);
lean_inc(x_361);
x_362 = lean_ctor_get(x_345, 9);
lean_inc(x_362);
x_363 = lean_ctor_get(x_345, 10);
lean_inc(x_363);
x_364 = lean_ctor_get(x_345, 11);
lean_inc(x_364);
x_365 = lean_ctor_get(x_345, 12);
lean_inc(x_365);
x_366 = lean_ctor_get(x_345, 13);
lean_inc(x_366);
x_367 = lean_ctor_get(x_345, 14);
lean_inc(x_367);
lean_dec(x_345);
x_368 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_368, 0, x_347);
lean_ctor_set(x_368, 1, x_353);
lean_ctor_set(x_368, 2, x_354);
lean_ctor_set(x_368, 3, x_355);
lean_ctor_set(x_368, 4, x_356);
lean_ctor_set(x_368, 5, x_357);
lean_ctor_set(x_368, 6, x_358);
lean_ctor_set(x_368, 7, x_360);
lean_ctor_set(x_368, 8, x_361);
lean_ctor_set(x_368, 9, x_362);
lean_ctor_set(x_368, 10, x_363);
lean_ctor_set(x_368, 11, x_364);
lean_ctor_set(x_368, 12, x_365);
lean_ctor_set(x_368, 13, x_366);
lean_ctor_set(x_368, 14, x_367);
lean_ctor_set_uint8(x_368, sizeof(void*)*15, x_359);
x_369 = lean_st_ref_set(x_13, x_368, x_346);
lean_dec(x_13);
x_370 = lean_ctor_get(x_369, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 x_371 = x_369;
} else {
 lean_dec_ref(x_369);
 x_371 = lean_box(0);
}
if (lean_is_scalar(x_371)) {
 x_372 = lean_alloc_ctor(0, 2, 0);
} else {
 x_372 = x_371;
}
lean_ctor_set(x_372, 0, x_1);
lean_ctor_set(x_372, 1, x_370);
return x_372;
}
}
else
{
lean_object* x_373; lean_object* x_374; 
lean_dec(x_228);
lean_dec(x_226);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_373 = lean_ctor_get(x_308, 0);
lean_inc(x_373);
lean_dec(x_308);
x_374 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_305);
return x_374;
}
}
}
else
{
uint8_t x_375; 
lean_dec(x_226);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_375 = !lean_is_exclusive(x_227);
if (x_375 == 0)
{
return x_227;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_227, 0);
x_377 = lean_ctor_get(x_227, 1);
lean_inc(x_377);
lean_inc(x_376);
lean_dec(x_227);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
return x_378;
}
}
}
block_417:
{
lean_object* x_381; 
lean_dec(x_380);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_9);
x_381 = l_Lean_Meta_getFunInfo(x_9, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; uint8_t x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
lean_dec(x_381);
x_384 = lean_ctor_get(x_382, 0);
lean_inc(x_384);
lean_dec(x_382);
x_385 = lean_array_get_size(x_10);
x_386 = lean_unsigned_to_nat(0u);
x_387 = lean_unsigned_to_nat(1u);
lean_inc(x_385);
x_388 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set(x_388, 1, x_385);
lean_ctor_set(x_388, 2, x_387);
x_389 = 0;
x_390 = lean_box(x_389);
lean_inc(x_10);
x_391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_391, 0, x_10);
lean_ctor_set(x_391, 1, x_390);
x_392 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_388);
lean_inc(x_9);
lean_inc(x_1);
x_393 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_392, x_384, x_385, x_388, x_388, x_391, x_386, lean_box(0), lean_box(0), x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_383);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; lean_object* x_395; uint8_t x_396; 
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_394, 1);
lean_inc(x_395);
x_396 = lean_unbox(x_395);
lean_dec(x_395);
if (x_396 == 0)
{
uint8_t x_397; 
lean_dec(x_394);
lean_dec(x_9);
x_397 = !lean_is_exclusive(x_393);
if (x_397 == 0)
{
lean_object* x_398; 
x_398 = lean_ctor_get(x_393, 0);
lean_dec(x_398);
lean_ctor_set(x_393, 0, x_1);
return x_393;
}
else
{
lean_object* x_399; lean_object* x_400; 
x_399 = lean_ctor_get(x_393, 1);
lean_inc(x_399);
lean_dec(x_393);
x_400 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_400, 0, x_1);
lean_ctor_set(x_400, 1, x_399);
return x_400;
}
}
else
{
uint8_t x_401; 
lean_dec(x_1);
x_401 = !lean_is_exclusive(x_393);
if (x_401 == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_402 = lean_ctor_get(x_393, 0);
lean_dec(x_402);
x_403 = lean_ctor_get(x_394, 0);
lean_inc(x_403);
lean_dec(x_394);
x_404 = l_Lean_mkAppN(x_9, x_403);
lean_dec(x_403);
lean_ctor_set(x_393, 0, x_404);
return x_393;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_405 = lean_ctor_get(x_393, 1);
lean_inc(x_405);
lean_dec(x_393);
x_406 = lean_ctor_get(x_394, 0);
lean_inc(x_406);
lean_dec(x_394);
x_407 = l_Lean_mkAppN(x_9, x_406);
lean_dec(x_406);
x_408 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_408, 0, x_407);
lean_ctor_set(x_408, 1, x_405);
return x_408;
}
}
}
else
{
uint8_t x_409; 
lean_dec(x_9);
lean_dec(x_1);
x_409 = !lean_is_exclusive(x_393);
if (x_409 == 0)
{
return x_393;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_410 = lean_ctor_get(x_393, 0);
x_411 = lean_ctor_get(x_393, 1);
lean_inc(x_411);
lean_inc(x_410);
lean_dec(x_393);
x_412 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set(x_412, 1, x_411);
return x_412;
}
}
}
else
{
uint8_t x_413; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_413 = !lean_is_exclusive(x_381);
if (x_413 == 0)
{
return x_381;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_414 = lean_ctor_get(x_381, 0);
x_415 = lean_ctor_get(x_381, 1);
lean_inc(x_415);
lean_inc(x_414);
lean_dec(x_381);
x_416 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_416, 0, x_414);
lean_ctor_set(x_416, 1, x_415);
return x_416;
}
}
}
}
case 2:
{
lean_object* x_430; lean_object* x_584; lean_object* x_622; uint8_t x_623; 
lean_dec(x_11);
x_622 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_623 = l_Lean_Expr_isConstOf(x_9, x_622);
if (x_623 == 0)
{
lean_object* x_624; 
x_624 = lean_box(0);
x_584 = x_624;
goto block_621;
}
else
{
lean_object* x_625; lean_object* x_626; uint8_t x_627; 
x_625 = lean_array_get_size(x_10);
x_626 = lean_unsigned_to_nat(2u);
x_627 = lean_nat_dec_eq(x_625, x_626);
if (x_627 == 0)
{
lean_object* x_628; 
lean_dec(x_625);
x_628 = lean_box(0);
x_584 = x_628;
goto block_621;
}
else
{
lean_object* x_629; uint8_t x_630; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_629 = lean_unsigned_to_nat(0u);
x_630 = lean_nat_dec_lt(x_629, x_625);
lean_dec(x_625);
if (x_630 == 0)
{
lean_object* x_631; lean_object* x_632; 
x_631 = l_Lean_instInhabitedExpr;
x_632 = l_outOfBounds___rarg(x_631);
x_430 = x_632;
goto block_583;
}
else
{
lean_object* x_633; 
x_633 = lean_array_fget(x_10, x_629);
x_430 = x_633;
goto block_583;
}
}
}
block_583:
{
lean_object* x_431; 
lean_inc(x_13);
lean_inc(x_430);
x_431 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_430, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; uint8_t x_435; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_431, 1);
lean_inc(x_433);
lean_dec(x_431);
x_434 = lean_st_ref_get(x_13, x_433);
x_435 = !lean_is_exclusive(x_434);
if (x_435 == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_436 = lean_ctor_get(x_434, 0);
x_437 = lean_ctor_get(x_434, 1);
x_438 = lean_ctor_get(x_436, 1);
lean_inc(x_438);
lean_dec(x_436);
x_439 = lean_ctor_get(x_438, 2);
lean_inc(x_439);
lean_dec(x_438);
x_440 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_439, x_432);
if (lean_obj_tag(x_440) == 0)
{
size_t x_441; size_t x_442; uint8_t x_443; 
lean_free_object(x_434);
x_441 = lean_ptr_addr(x_430);
lean_dec(x_430);
x_442 = lean_ptr_addr(x_432);
x_443 = lean_usize_dec_eq(x_441, x_442);
if (x_443 == 0)
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; uint8_t x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; uint8_t x_473; 
lean_dec(x_1);
x_444 = lean_unsigned_to_nat(0u);
lean_inc(x_432);
x_445 = lean_array_set(x_10, x_444, x_432);
x_446 = l_Lean_mkAppN(x_9, x_445);
lean_dec(x_445);
x_447 = lean_st_ref_take(x_13, x_437);
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_447, 1);
lean_inc(x_449);
lean_dec(x_447);
x_450 = lean_ctor_get(x_448, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_448, 1);
lean_inc(x_451);
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_451, 1);
lean_inc(x_453);
x_454 = lean_ctor_get(x_451, 2);
lean_inc(x_454);
lean_dec(x_451);
lean_inc(x_446);
x_455 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_454, x_432, x_446);
x_456 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_456, 0, x_452);
lean_ctor_set(x_456, 1, x_453);
lean_ctor_set(x_456, 2, x_455);
x_457 = lean_ctor_get(x_448, 2);
lean_inc(x_457);
x_458 = lean_ctor_get(x_448, 3);
lean_inc(x_458);
x_459 = lean_ctor_get(x_448, 4);
lean_inc(x_459);
x_460 = lean_ctor_get(x_448, 5);
lean_inc(x_460);
x_461 = lean_ctor_get(x_448, 6);
lean_inc(x_461);
x_462 = lean_ctor_get_uint8(x_448, sizeof(void*)*15);
x_463 = lean_ctor_get(x_448, 7);
lean_inc(x_463);
x_464 = lean_ctor_get(x_448, 8);
lean_inc(x_464);
x_465 = lean_ctor_get(x_448, 9);
lean_inc(x_465);
x_466 = lean_ctor_get(x_448, 10);
lean_inc(x_466);
x_467 = lean_ctor_get(x_448, 11);
lean_inc(x_467);
x_468 = lean_ctor_get(x_448, 12);
lean_inc(x_468);
x_469 = lean_ctor_get(x_448, 13);
lean_inc(x_469);
x_470 = lean_ctor_get(x_448, 14);
lean_inc(x_470);
lean_dec(x_448);
x_471 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_471, 0, x_450);
lean_ctor_set(x_471, 1, x_456);
lean_ctor_set(x_471, 2, x_457);
lean_ctor_set(x_471, 3, x_458);
lean_ctor_set(x_471, 4, x_459);
lean_ctor_set(x_471, 5, x_460);
lean_ctor_set(x_471, 6, x_461);
lean_ctor_set(x_471, 7, x_463);
lean_ctor_set(x_471, 8, x_464);
lean_ctor_set(x_471, 9, x_465);
lean_ctor_set(x_471, 10, x_466);
lean_ctor_set(x_471, 11, x_467);
lean_ctor_set(x_471, 12, x_468);
lean_ctor_set(x_471, 13, x_469);
lean_ctor_set(x_471, 14, x_470);
lean_ctor_set_uint8(x_471, sizeof(void*)*15, x_462);
x_472 = lean_st_ref_set(x_13, x_471, x_449);
lean_dec(x_13);
x_473 = !lean_is_exclusive(x_472);
if (x_473 == 0)
{
lean_object* x_474; 
x_474 = lean_ctor_get(x_472, 0);
lean_dec(x_474);
lean_ctor_set(x_472, 0, x_446);
return x_472;
}
else
{
lean_object* x_475; lean_object* x_476; 
x_475 = lean_ctor_get(x_472, 1);
lean_inc(x_475);
lean_dec(x_472);
x_476 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_476, 0, x_446);
lean_ctor_set(x_476, 1, x_475);
return x_476;
}
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; uint8_t x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; 
lean_dec(x_10);
lean_dec(x_9);
x_477 = lean_st_ref_take(x_13, x_437);
x_478 = lean_ctor_get(x_477, 0);
lean_inc(x_478);
x_479 = lean_ctor_get(x_477, 1);
lean_inc(x_479);
lean_dec(x_477);
x_480 = lean_ctor_get(x_478, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_478, 1);
lean_inc(x_481);
x_482 = lean_ctor_get(x_481, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_481, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_481, 2);
lean_inc(x_484);
lean_dec(x_481);
lean_inc(x_1);
x_485 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_484, x_432, x_1);
x_486 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_486, 0, x_482);
lean_ctor_set(x_486, 1, x_483);
lean_ctor_set(x_486, 2, x_485);
x_487 = lean_ctor_get(x_478, 2);
lean_inc(x_487);
x_488 = lean_ctor_get(x_478, 3);
lean_inc(x_488);
x_489 = lean_ctor_get(x_478, 4);
lean_inc(x_489);
x_490 = lean_ctor_get(x_478, 5);
lean_inc(x_490);
x_491 = lean_ctor_get(x_478, 6);
lean_inc(x_491);
x_492 = lean_ctor_get_uint8(x_478, sizeof(void*)*15);
x_493 = lean_ctor_get(x_478, 7);
lean_inc(x_493);
x_494 = lean_ctor_get(x_478, 8);
lean_inc(x_494);
x_495 = lean_ctor_get(x_478, 9);
lean_inc(x_495);
x_496 = lean_ctor_get(x_478, 10);
lean_inc(x_496);
x_497 = lean_ctor_get(x_478, 11);
lean_inc(x_497);
x_498 = lean_ctor_get(x_478, 12);
lean_inc(x_498);
x_499 = lean_ctor_get(x_478, 13);
lean_inc(x_499);
x_500 = lean_ctor_get(x_478, 14);
lean_inc(x_500);
lean_dec(x_478);
x_501 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_501, 0, x_480);
lean_ctor_set(x_501, 1, x_486);
lean_ctor_set(x_501, 2, x_487);
lean_ctor_set(x_501, 3, x_488);
lean_ctor_set(x_501, 4, x_489);
lean_ctor_set(x_501, 5, x_490);
lean_ctor_set(x_501, 6, x_491);
lean_ctor_set(x_501, 7, x_493);
lean_ctor_set(x_501, 8, x_494);
lean_ctor_set(x_501, 9, x_495);
lean_ctor_set(x_501, 10, x_496);
lean_ctor_set(x_501, 11, x_497);
lean_ctor_set(x_501, 12, x_498);
lean_ctor_set(x_501, 13, x_499);
lean_ctor_set(x_501, 14, x_500);
lean_ctor_set_uint8(x_501, sizeof(void*)*15, x_492);
x_502 = lean_st_ref_set(x_13, x_501, x_479);
lean_dec(x_13);
x_503 = !lean_is_exclusive(x_502);
if (x_503 == 0)
{
lean_object* x_504; 
x_504 = lean_ctor_get(x_502, 0);
lean_dec(x_504);
lean_ctor_set(x_502, 0, x_1);
return x_502;
}
else
{
lean_object* x_505; lean_object* x_506; 
x_505 = lean_ctor_get(x_502, 1);
lean_inc(x_505);
lean_dec(x_502);
x_506 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_506, 0, x_1);
lean_ctor_set(x_506, 1, x_505);
return x_506;
}
}
}
else
{
lean_object* x_507; 
lean_dec(x_432);
lean_dec(x_430);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_507 = lean_ctor_get(x_440, 0);
lean_inc(x_507);
lean_dec(x_440);
lean_ctor_set(x_434, 0, x_507);
return x_434;
}
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_508 = lean_ctor_get(x_434, 0);
x_509 = lean_ctor_get(x_434, 1);
lean_inc(x_509);
lean_inc(x_508);
lean_dec(x_434);
x_510 = lean_ctor_get(x_508, 1);
lean_inc(x_510);
lean_dec(x_508);
x_511 = lean_ctor_get(x_510, 2);
lean_inc(x_511);
lean_dec(x_510);
x_512 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_511, x_432);
if (lean_obj_tag(x_512) == 0)
{
size_t x_513; size_t x_514; uint8_t x_515; 
x_513 = lean_ptr_addr(x_430);
lean_dec(x_430);
x_514 = lean_ptr_addr(x_432);
x_515 = lean_usize_dec_eq(x_513, x_514);
if (x_515 == 0)
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; uint8_t x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; 
lean_dec(x_1);
x_516 = lean_unsigned_to_nat(0u);
lean_inc(x_432);
x_517 = lean_array_set(x_10, x_516, x_432);
x_518 = l_Lean_mkAppN(x_9, x_517);
lean_dec(x_517);
x_519 = lean_st_ref_take(x_13, x_509);
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_519, 1);
lean_inc(x_521);
lean_dec(x_519);
x_522 = lean_ctor_get(x_520, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_520, 1);
lean_inc(x_523);
x_524 = lean_ctor_get(x_523, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_523, 1);
lean_inc(x_525);
x_526 = lean_ctor_get(x_523, 2);
lean_inc(x_526);
lean_dec(x_523);
lean_inc(x_518);
x_527 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_526, x_432, x_518);
x_528 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_528, 0, x_524);
lean_ctor_set(x_528, 1, x_525);
lean_ctor_set(x_528, 2, x_527);
x_529 = lean_ctor_get(x_520, 2);
lean_inc(x_529);
x_530 = lean_ctor_get(x_520, 3);
lean_inc(x_530);
x_531 = lean_ctor_get(x_520, 4);
lean_inc(x_531);
x_532 = lean_ctor_get(x_520, 5);
lean_inc(x_532);
x_533 = lean_ctor_get(x_520, 6);
lean_inc(x_533);
x_534 = lean_ctor_get_uint8(x_520, sizeof(void*)*15);
x_535 = lean_ctor_get(x_520, 7);
lean_inc(x_535);
x_536 = lean_ctor_get(x_520, 8);
lean_inc(x_536);
x_537 = lean_ctor_get(x_520, 9);
lean_inc(x_537);
x_538 = lean_ctor_get(x_520, 10);
lean_inc(x_538);
x_539 = lean_ctor_get(x_520, 11);
lean_inc(x_539);
x_540 = lean_ctor_get(x_520, 12);
lean_inc(x_540);
x_541 = lean_ctor_get(x_520, 13);
lean_inc(x_541);
x_542 = lean_ctor_get(x_520, 14);
lean_inc(x_542);
lean_dec(x_520);
x_543 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_543, 0, x_522);
lean_ctor_set(x_543, 1, x_528);
lean_ctor_set(x_543, 2, x_529);
lean_ctor_set(x_543, 3, x_530);
lean_ctor_set(x_543, 4, x_531);
lean_ctor_set(x_543, 5, x_532);
lean_ctor_set(x_543, 6, x_533);
lean_ctor_set(x_543, 7, x_535);
lean_ctor_set(x_543, 8, x_536);
lean_ctor_set(x_543, 9, x_537);
lean_ctor_set(x_543, 10, x_538);
lean_ctor_set(x_543, 11, x_539);
lean_ctor_set(x_543, 12, x_540);
lean_ctor_set(x_543, 13, x_541);
lean_ctor_set(x_543, 14, x_542);
lean_ctor_set_uint8(x_543, sizeof(void*)*15, x_534);
x_544 = lean_st_ref_set(x_13, x_543, x_521);
lean_dec(x_13);
x_545 = lean_ctor_get(x_544, 1);
lean_inc(x_545);
if (lean_is_exclusive(x_544)) {
 lean_ctor_release(x_544, 0);
 lean_ctor_release(x_544, 1);
 x_546 = x_544;
} else {
 lean_dec_ref(x_544);
 x_546 = lean_box(0);
}
if (lean_is_scalar(x_546)) {
 x_547 = lean_alloc_ctor(0, 2, 0);
} else {
 x_547 = x_546;
}
lean_ctor_set(x_547, 0, x_518);
lean_ctor_set(x_547, 1, x_545);
return x_547;
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; uint8_t x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
lean_dec(x_10);
lean_dec(x_9);
x_548 = lean_st_ref_take(x_13, x_509);
x_549 = lean_ctor_get(x_548, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_548, 1);
lean_inc(x_550);
lean_dec(x_548);
x_551 = lean_ctor_get(x_549, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_549, 1);
lean_inc(x_552);
x_553 = lean_ctor_get(x_552, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_552, 1);
lean_inc(x_554);
x_555 = lean_ctor_get(x_552, 2);
lean_inc(x_555);
lean_dec(x_552);
lean_inc(x_1);
x_556 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_555, x_432, x_1);
x_557 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_557, 0, x_553);
lean_ctor_set(x_557, 1, x_554);
lean_ctor_set(x_557, 2, x_556);
x_558 = lean_ctor_get(x_549, 2);
lean_inc(x_558);
x_559 = lean_ctor_get(x_549, 3);
lean_inc(x_559);
x_560 = lean_ctor_get(x_549, 4);
lean_inc(x_560);
x_561 = lean_ctor_get(x_549, 5);
lean_inc(x_561);
x_562 = lean_ctor_get(x_549, 6);
lean_inc(x_562);
x_563 = lean_ctor_get_uint8(x_549, sizeof(void*)*15);
x_564 = lean_ctor_get(x_549, 7);
lean_inc(x_564);
x_565 = lean_ctor_get(x_549, 8);
lean_inc(x_565);
x_566 = lean_ctor_get(x_549, 9);
lean_inc(x_566);
x_567 = lean_ctor_get(x_549, 10);
lean_inc(x_567);
x_568 = lean_ctor_get(x_549, 11);
lean_inc(x_568);
x_569 = lean_ctor_get(x_549, 12);
lean_inc(x_569);
x_570 = lean_ctor_get(x_549, 13);
lean_inc(x_570);
x_571 = lean_ctor_get(x_549, 14);
lean_inc(x_571);
lean_dec(x_549);
x_572 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_572, 0, x_551);
lean_ctor_set(x_572, 1, x_557);
lean_ctor_set(x_572, 2, x_558);
lean_ctor_set(x_572, 3, x_559);
lean_ctor_set(x_572, 4, x_560);
lean_ctor_set(x_572, 5, x_561);
lean_ctor_set(x_572, 6, x_562);
lean_ctor_set(x_572, 7, x_564);
lean_ctor_set(x_572, 8, x_565);
lean_ctor_set(x_572, 9, x_566);
lean_ctor_set(x_572, 10, x_567);
lean_ctor_set(x_572, 11, x_568);
lean_ctor_set(x_572, 12, x_569);
lean_ctor_set(x_572, 13, x_570);
lean_ctor_set(x_572, 14, x_571);
lean_ctor_set_uint8(x_572, sizeof(void*)*15, x_563);
x_573 = lean_st_ref_set(x_13, x_572, x_550);
lean_dec(x_13);
x_574 = lean_ctor_get(x_573, 1);
lean_inc(x_574);
if (lean_is_exclusive(x_573)) {
 lean_ctor_release(x_573, 0);
 lean_ctor_release(x_573, 1);
 x_575 = x_573;
} else {
 lean_dec_ref(x_573);
 x_575 = lean_box(0);
}
if (lean_is_scalar(x_575)) {
 x_576 = lean_alloc_ctor(0, 2, 0);
} else {
 x_576 = x_575;
}
lean_ctor_set(x_576, 0, x_1);
lean_ctor_set(x_576, 1, x_574);
return x_576;
}
}
else
{
lean_object* x_577; lean_object* x_578; 
lean_dec(x_432);
lean_dec(x_430);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_577 = lean_ctor_get(x_512, 0);
lean_inc(x_577);
lean_dec(x_512);
x_578 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_578, 0, x_577);
lean_ctor_set(x_578, 1, x_509);
return x_578;
}
}
}
else
{
uint8_t x_579; 
lean_dec(x_430);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_579 = !lean_is_exclusive(x_431);
if (x_579 == 0)
{
return x_431;
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_580 = lean_ctor_get(x_431, 0);
x_581 = lean_ctor_get(x_431, 1);
lean_inc(x_581);
lean_inc(x_580);
lean_dec(x_431);
x_582 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_582, 0, x_580);
lean_ctor_set(x_582, 1, x_581);
return x_582;
}
}
}
block_621:
{
lean_object* x_585; 
lean_dec(x_584);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_9);
x_585 = l_Lean_Meta_getFunInfo(x_9, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_585) == 0)
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; uint8_t x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
x_586 = lean_ctor_get(x_585, 0);
lean_inc(x_586);
x_587 = lean_ctor_get(x_585, 1);
lean_inc(x_587);
lean_dec(x_585);
x_588 = lean_ctor_get(x_586, 0);
lean_inc(x_588);
lean_dec(x_586);
x_589 = lean_array_get_size(x_10);
x_590 = lean_unsigned_to_nat(0u);
x_591 = lean_unsigned_to_nat(1u);
lean_inc(x_589);
x_592 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_592, 0, x_590);
lean_ctor_set(x_592, 1, x_589);
lean_ctor_set(x_592, 2, x_591);
x_593 = 0;
x_594 = lean_box(x_593);
lean_inc(x_10);
x_595 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_595, 0, x_10);
lean_ctor_set(x_595, 1, x_594);
x_596 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_592);
lean_inc(x_9);
lean_inc(x_1);
x_597 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_596, x_588, x_589, x_592, x_592, x_595, x_590, lean_box(0), lean_box(0), x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_587);
if (lean_obj_tag(x_597) == 0)
{
lean_object* x_598; lean_object* x_599; uint8_t x_600; 
x_598 = lean_ctor_get(x_597, 0);
lean_inc(x_598);
x_599 = lean_ctor_get(x_598, 1);
lean_inc(x_599);
x_600 = lean_unbox(x_599);
lean_dec(x_599);
if (x_600 == 0)
{
uint8_t x_601; 
lean_dec(x_598);
lean_dec(x_9);
x_601 = !lean_is_exclusive(x_597);
if (x_601 == 0)
{
lean_object* x_602; 
x_602 = lean_ctor_get(x_597, 0);
lean_dec(x_602);
lean_ctor_set(x_597, 0, x_1);
return x_597;
}
else
{
lean_object* x_603; lean_object* x_604; 
x_603 = lean_ctor_get(x_597, 1);
lean_inc(x_603);
lean_dec(x_597);
x_604 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_604, 0, x_1);
lean_ctor_set(x_604, 1, x_603);
return x_604;
}
}
else
{
uint8_t x_605; 
lean_dec(x_1);
x_605 = !lean_is_exclusive(x_597);
if (x_605 == 0)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_606 = lean_ctor_get(x_597, 0);
lean_dec(x_606);
x_607 = lean_ctor_get(x_598, 0);
lean_inc(x_607);
lean_dec(x_598);
x_608 = l_Lean_mkAppN(x_9, x_607);
lean_dec(x_607);
lean_ctor_set(x_597, 0, x_608);
return x_597;
}
else
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
x_609 = lean_ctor_get(x_597, 1);
lean_inc(x_609);
lean_dec(x_597);
x_610 = lean_ctor_get(x_598, 0);
lean_inc(x_610);
lean_dec(x_598);
x_611 = l_Lean_mkAppN(x_9, x_610);
lean_dec(x_610);
x_612 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_612, 0, x_611);
lean_ctor_set(x_612, 1, x_609);
return x_612;
}
}
}
else
{
uint8_t x_613; 
lean_dec(x_9);
lean_dec(x_1);
x_613 = !lean_is_exclusive(x_597);
if (x_613 == 0)
{
return x_597;
}
else
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_614 = lean_ctor_get(x_597, 0);
x_615 = lean_ctor_get(x_597, 1);
lean_inc(x_615);
lean_inc(x_614);
lean_dec(x_597);
x_616 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_616, 0, x_614);
lean_ctor_set(x_616, 1, x_615);
return x_616;
}
}
}
else
{
uint8_t x_617; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_617 = !lean_is_exclusive(x_585);
if (x_617 == 0)
{
return x_585;
}
else
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_618 = lean_ctor_get(x_585, 0);
x_619 = lean_ctor_get(x_585, 1);
lean_inc(x_619);
lean_inc(x_618);
lean_dec(x_585);
x_620 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_620, 0, x_618);
lean_ctor_set(x_620, 1, x_619);
return x_620;
}
}
}
}
case 3:
{
lean_object* x_634; lean_object* x_788; lean_object* x_826; uint8_t x_827; 
lean_dec(x_11);
x_826 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_827 = l_Lean_Expr_isConstOf(x_9, x_826);
if (x_827 == 0)
{
lean_object* x_828; 
x_828 = lean_box(0);
x_788 = x_828;
goto block_825;
}
else
{
lean_object* x_829; lean_object* x_830; uint8_t x_831; 
x_829 = lean_array_get_size(x_10);
x_830 = lean_unsigned_to_nat(2u);
x_831 = lean_nat_dec_eq(x_829, x_830);
if (x_831 == 0)
{
lean_object* x_832; 
lean_dec(x_829);
x_832 = lean_box(0);
x_788 = x_832;
goto block_825;
}
else
{
lean_object* x_833; uint8_t x_834; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_833 = lean_unsigned_to_nat(0u);
x_834 = lean_nat_dec_lt(x_833, x_829);
lean_dec(x_829);
if (x_834 == 0)
{
lean_object* x_835; lean_object* x_836; 
x_835 = l_Lean_instInhabitedExpr;
x_836 = l_outOfBounds___rarg(x_835);
x_634 = x_836;
goto block_787;
}
else
{
lean_object* x_837; 
x_837 = lean_array_fget(x_10, x_833);
x_634 = x_837;
goto block_787;
}
}
}
block_787:
{
lean_object* x_635; 
lean_inc(x_13);
lean_inc(x_634);
x_635 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_634, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_635) == 0)
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; uint8_t x_639; 
x_636 = lean_ctor_get(x_635, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_635, 1);
lean_inc(x_637);
lean_dec(x_635);
x_638 = lean_st_ref_get(x_13, x_637);
x_639 = !lean_is_exclusive(x_638);
if (x_639 == 0)
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; 
x_640 = lean_ctor_get(x_638, 0);
x_641 = lean_ctor_get(x_638, 1);
x_642 = lean_ctor_get(x_640, 1);
lean_inc(x_642);
lean_dec(x_640);
x_643 = lean_ctor_get(x_642, 2);
lean_inc(x_643);
lean_dec(x_642);
x_644 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_643, x_636);
if (lean_obj_tag(x_644) == 0)
{
size_t x_645; size_t x_646; uint8_t x_647; 
lean_free_object(x_638);
x_645 = lean_ptr_addr(x_634);
lean_dec(x_634);
x_646 = lean_ptr_addr(x_636);
x_647 = lean_usize_dec_eq(x_645, x_646);
if (x_647 == 0)
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; uint8_t x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; uint8_t x_677; 
lean_dec(x_1);
x_648 = lean_unsigned_to_nat(0u);
lean_inc(x_636);
x_649 = lean_array_set(x_10, x_648, x_636);
x_650 = l_Lean_mkAppN(x_9, x_649);
lean_dec(x_649);
x_651 = lean_st_ref_take(x_13, x_641);
x_652 = lean_ctor_get(x_651, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_651, 1);
lean_inc(x_653);
lean_dec(x_651);
x_654 = lean_ctor_get(x_652, 0);
lean_inc(x_654);
x_655 = lean_ctor_get(x_652, 1);
lean_inc(x_655);
x_656 = lean_ctor_get(x_655, 0);
lean_inc(x_656);
x_657 = lean_ctor_get(x_655, 1);
lean_inc(x_657);
x_658 = lean_ctor_get(x_655, 2);
lean_inc(x_658);
lean_dec(x_655);
lean_inc(x_650);
x_659 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_658, x_636, x_650);
x_660 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_660, 0, x_656);
lean_ctor_set(x_660, 1, x_657);
lean_ctor_set(x_660, 2, x_659);
x_661 = lean_ctor_get(x_652, 2);
lean_inc(x_661);
x_662 = lean_ctor_get(x_652, 3);
lean_inc(x_662);
x_663 = lean_ctor_get(x_652, 4);
lean_inc(x_663);
x_664 = lean_ctor_get(x_652, 5);
lean_inc(x_664);
x_665 = lean_ctor_get(x_652, 6);
lean_inc(x_665);
x_666 = lean_ctor_get_uint8(x_652, sizeof(void*)*15);
x_667 = lean_ctor_get(x_652, 7);
lean_inc(x_667);
x_668 = lean_ctor_get(x_652, 8);
lean_inc(x_668);
x_669 = lean_ctor_get(x_652, 9);
lean_inc(x_669);
x_670 = lean_ctor_get(x_652, 10);
lean_inc(x_670);
x_671 = lean_ctor_get(x_652, 11);
lean_inc(x_671);
x_672 = lean_ctor_get(x_652, 12);
lean_inc(x_672);
x_673 = lean_ctor_get(x_652, 13);
lean_inc(x_673);
x_674 = lean_ctor_get(x_652, 14);
lean_inc(x_674);
lean_dec(x_652);
x_675 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_675, 0, x_654);
lean_ctor_set(x_675, 1, x_660);
lean_ctor_set(x_675, 2, x_661);
lean_ctor_set(x_675, 3, x_662);
lean_ctor_set(x_675, 4, x_663);
lean_ctor_set(x_675, 5, x_664);
lean_ctor_set(x_675, 6, x_665);
lean_ctor_set(x_675, 7, x_667);
lean_ctor_set(x_675, 8, x_668);
lean_ctor_set(x_675, 9, x_669);
lean_ctor_set(x_675, 10, x_670);
lean_ctor_set(x_675, 11, x_671);
lean_ctor_set(x_675, 12, x_672);
lean_ctor_set(x_675, 13, x_673);
lean_ctor_set(x_675, 14, x_674);
lean_ctor_set_uint8(x_675, sizeof(void*)*15, x_666);
x_676 = lean_st_ref_set(x_13, x_675, x_653);
lean_dec(x_13);
x_677 = !lean_is_exclusive(x_676);
if (x_677 == 0)
{
lean_object* x_678; 
x_678 = lean_ctor_get(x_676, 0);
lean_dec(x_678);
lean_ctor_set(x_676, 0, x_650);
return x_676;
}
else
{
lean_object* x_679; lean_object* x_680; 
x_679 = lean_ctor_get(x_676, 1);
lean_inc(x_679);
lean_dec(x_676);
x_680 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_680, 0, x_650);
lean_ctor_set(x_680, 1, x_679);
return x_680;
}
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; uint8_t x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; uint8_t x_707; 
lean_dec(x_10);
lean_dec(x_9);
x_681 = lean_st_ref_take(x_13, x_641);
x_682 = lean_ctor_get(x_681, 0);
lean_inc(x_682);
x_683 = lean_ctor_get(x_681, 1);
lean_inc(x_683);
lean_dec(x_681);
x_684 = lean_ctor_get(x_682, 0);
lean_inc(x_684);
x_685 = lean_ctor_get(x_682, 1);
lean_inc(x_685);
x_686 = lean_ctor_get(x_685, 0);
lean_inc(x_686);
x_687 = lean_ctor_get(x_685, 1);
lean_inc(x_687);
x_688 = lean_ctor_get(x_685, 2);
lean_inc(x_688);
lean_dec(x_685);
lean_inc(x_1);
x_689 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_688, x_636, x_1);
x_690 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_690, 0, x_686);
lean_ctor_set(x_690, 1, x_687);
lean_ctor_set(x_690, 2, x_689);
x_691 = lean_ctor_get(x_682, 2);
lean_inc(x_691);
x_692 = lean_ctor_get(x_682, 3);
lean_inc(x_692);
x_693 = lean_ctor_get(x_682, 4);
lean_inc(x_693);
x_694 = lean_ctor_get(x_682, 5);
lean_inc(x_694);
x_695 = lean_ctor_get(x_682, 6);
lean_inc(x_695);
x_696 = lean_ctor_get_uint8(x_682, sizeof(void*)*15);
x_697 = lean_ctor_get(x_682, 7);
lean_inc(x_697);
x_698 = lean_ctor_get(x_682, 8);
lean_inc(x_698);
x_699 = lean_ctor_get(x_682, 9);
lean_inc(x_699);
x_700 = lean_ctor_get(x_682, 10);
lean_inc(x_700);
x_701 = lean_ctor_get(x_682, 11);
lean_inc(x_701);
x_702 = lean_ctor_get(x_682, 12);
lean_inc(x_702);
x_703 = lean_ctor_get(x_682, 13);
lean_inc(x_703);
x_704 = lean_ctor_get(x_682, 14);
lean_inc(x_704);
lean_dec(x_682);
x_705 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_705, 0, x_684);
lean_ctor_set(x_705, 1, x_690);
lean_ctor_set(x_705, 2, x_691);
lean_ctor_set(x_705, 3, x_692);
lean_ctor_set(x_705, 4, x_693);
lean_ctor_set(x_705, 5, x_694);
lean_ctor_set(x_705, 6, x_695);
lean_ctor_set(x_705, 7, x_697);
lean_ctor_set(x_705, 8, x_698);
lean_ctor_set(x_705, 9, x_699);
lean_ctor_set(x_705, 10, x_700);
lean_ctor_set(x_705, 11, x_701);
lean_ctor_set(x_705, 12, x_702);
lean_ctor_set(x_705, 13, x_703);
lean_ctor_set(x_705, 14, x_704);
lean_ctor_set_uint8(x_705, sizeof(void*)*15, x_696);
x_706 = lean_st_ref_set(x_13, x_705, x_683);
lean_dec(x_13);
x_707 = !lean_is_exclusive(x_706);
if (x_707 == 0)
{
lean_object* x_708; 
x_708 = lean_ctor_get(x_706, 0);
lean_dec(x_708);
lean_ctor_set(x_706, 0, x_1);
return x_706;
}
else
{
lean_object* x_709; lean_object* x_710; 
x_709 = lean_ctor_get(x_706, 1);
lean_inc(x_709);
lean_dec(x_706);
x_710 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_710, 0, x_1);
lean_ctor_set(x_710, 1, x_709);
return x_710;
}
}
}
else
{
lean_object* x_711; 
lean_dec(x_636);
lean_dec(x_634);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_711 = lean_ctor_get(x_644, 0);
lean_inc(x_711);
lean_dec(x_644);
lean_ctor_set(x_638, 0, x_711);
return x_638;
}
}
else
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; 
x_712 = lean_ctor_get(x_638, 0);
x_713 = lean_ctor_get(x_638, 1);
lean_inc(x_713);
lean_inc(x_712);
lean_dec(x_638);
x_714 = lean_ctor_get(x_712, 1);
lean_inc(x_714);
lean_dec(x_712);
x_715 = lean_ctor_get(x_714, 2);
lean_inc(x_715);
lean_dec(x_714);
x_716 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_715, x_636);
if (lean_obj_tag(x_716) == 0)
{
size_t x_717; size_t x_718; uint8_t x_719; 
x_717 = lean_ptr_addr(x_634);
lean_dec(x_634);
x_718 = lean_ptr_addr(x_636);
x_719 = lean_usize_dec_eq(x_717, x_718);
if (x_719 == 0)
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; uint8_t x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; 
lean_dec(x_1);
x_720 = lean_unsigned_to_nat(0u);
lean_inc(x_636);
x_721 = lean_array_set(x_10, x_720, x_636);
x_722 = l_Lean_mkAppN(x_9, x_721);
lean_dec(x_721);
x_723 = lean_st_ref_take(x_13, x_713);
x_724 = lean_ctor_get(x_723, 0);
lean_inc(x_724);
x_725 = lean_ctor_get(x_723, 1);
lean_inc(x_725);
lean_dec(x_723);
x_726 = lean_ctor_get(x_724, 0);
lean_inc(x_726);
x_727 = lean_ctor_get(x_724, 1);
lean_inc(x_727);
x_728 = lean_ctor_get(x_727, 0);
lean_inc(x_728);
x_729 = lean_ctor_get(x_727, 1);
lean_inc(x_729);
x_730 = lean_ctor_get(x_727, 2);
lean_inc(x_730);
lean_dec(x_727);
lean_inc(x_722);
x_731 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_730, x_636, x_722);
x_732 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_732, 0, x_728);
lean_ctor_set(x_732, 1, x_729);
lean_ctor_set(x_732, 2, x_731);
x_733 = lean_ctor_get(x_724, 2);
lean_inc(x_733);
x_734 = lean_ctor_get(x_724, 3);
lean_inc(x_734);
x_735 = lean_ctor_get(x_724, 4);
lean_inc(x_735);
x_736 = lean_ctor_get(x_724, 5);
lean_inc(x_736);
x_737 = lean_ctor_get(x_724, 6);
lean_inc(x_737);
x_738 = lean_ctor_get_uint8(x_724, sizeof(void*)*15);
x_739 = lean_ctor_get(x_724, 7);
lean_inc(x_739);
x_740 = lean_ctor_get(x_724, 8);
lean_inc(x_740);
x_741 = lean_ctor_get(x_724, 9);
lean_inc(x_741);
x_742 = lean_ctor_get(x_724, 10);
lean_inc(x_742);
x_743 = lean_ctor_get(x_724, 11);
lean_inc(x_743);
x_744 = lean_ctor_get(x_724, 12);
lean_inc(x_744);
x_745 = lean_ctor_get(x_724, 13);
lean_inc(x_745);
x_746 = lean_ctor_get(x_724, 14);
lean_inc(x_746);
lean_dec(x_724);
x_747 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_747, 0, x_726);
lean_ctor_set(x_747, 1, x_732);
lean_ctor_set(x_747, 2, x_733);
lean_ctor_set(x_747, 3, x_734);
lean_ctor_set(x_747, 4, x_735);
lean_ctor_set(x_747, 5, x_736);
lean_ctor_set(x_747, 6, x_737);
lean_ctor_set(x_747, 7, x_739);
lean_ctor_set(x_747, 8, x_740);
lean_ctor_set(x_747, 9, x_741);
lean_ctor_set(x_747, 10, x_742);
lean_ctor_set(x_747, 11, x_743);
lean_ctor_set(x_747, 12, x_744);
lean_ctor_set(x_747, 13, x_745);
lean_ctor_set(x_747, 14, x_746);
lean_ctor_set_uint8(x_747, sizeof(void*)*15, x_738);
x_748 = lean_st_ref_set(x_13, x_747, x_725);
lean_dec(x_13);
x_749 = lean_ctor_get(x_748, 1);
lean_inc(x_749);
if (lean_is_exclusive(x_748)) {
 lean_ctor_release(x_748, 0);
 lean_ctor_release(x_748, 1);
 x_750 = x_748;
} else {
 lean_dec_ref(x_748);
 x_750 = lean_box(0);
}
if (lean_is_scalar(x_750)) {
 x_751 = lean_alloc_ctor(0, 2, 0);
} else {
 x_751 = x_750;
}
lean_ctor_set(x_751, 0, x_722);
lean_ctor_set(x_751, 1, x_749);
return x_751;
}
else
{
lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; uint8_t x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; 
lean_dec(x_10);
lean_dec(x_9);
x_752 = lean_st_ref_take(x_13, x_713);
x_753 = lean_ctor_get(x_752, 0);
lean_inc(x_753);
x_754 = lean_ctor_get(x_752, 1);
lean_inc(x_754);
lean_dec(x_752);
x_755 = lean_ctor_get(x_753, 0);
lean_inc(x_755);
x_756 = lean_ctor_get(x_753, 1);
lean_inc(x_756);
x_757 = lean_ctor_get(x_756, 0);
lean_inc(x_757);
x_758 = lean_ctor_get(x_756, 1);
lean_inc(x_758);
x_759 = lean_ctor_get(x_756, 2);
lean_inc(x_759);
lean_dec(x_756);
lean_inc(x_1);
x_760 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_759, x_636, x_1);
x_761 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_761, 0, x_757);
lean_ctor_set(x_761, 1, x_758);
lean_ctor_set(x_761, 2, x_760);
x_762 = lean_ctor_get(x_753, 2);
lean_inc(x_762);
x_763 = lean_ctor_get(x_753, 3);
lean_inc(x_763);
x_764 = lean_ctor_get(x_753, 4);
lean_inc(x_764);
x_765 = lean_ctor_get(x_753, 5);
lean_inc(x_765);
x_766 = lean_ctor_get(x_753, 6);
lean_inc(x_766);
x_767 = lean_ctor_get_uint8(x_753, sizeof(void*)*15);
x_768 = lean_ctor_get(x_753, 7);
lean_inc(x_768);
x_769 = lean_ctor_get(x_753, 8);
lean_inc(x_769);
x_770 = lean_ctor_get(x_753, 9);
lean_inc(x_770);
x_771 = lean_ctor_get(x_753, 10);
lean_inc(x_771);
x_772 = lean_ctor_get(x_753, 11);
lean_inc(x_772);
x_773 = lean_ctor_get(x_753, 12);
lean_inc(x_773);
x_774 = lean_ctor_get(x_753, 13);
lean_inc(x_774);
x_775 = lean_ctor_get(x_753, 14);
lean_inc(x_775);
lean_dec(x_753);
x_776 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_776, 0, x_755);
lean_ctor_set(x_776, 1, x_761);
lean_ctor_set(x_776, 2, x_762);
lean_ctor_set(x_776, 3, x_763);
lean_ctor_set(x_776, 4, x_764);
lean_ctor_set(x_776, 5, x_765);
lean_ctor_set(x_776, 6, x_766);
lean_ctor_set(x_776, 7, x_768);
lean_ctor_set(x_776, 8, x_769);
lean_ctor_set(x_776, 9, x_770);
lean_ctor_set(x_776, 10, x_771);
lean_ctor_set(x_776, 11, x_772);
lean_ctor_set(x_776, 12, x_773);
lean_ctor_set(x_776, 13, x_774);
lean_ctor_set(x_776, 14, x_775);
lean_ctor_set_uint8(x_776, sizeof(void*)*15, x_767);
x_777 = lean_st_ref_set(x_13, x_776, x_754);
lean_dec(x_13);
x_778 = lean_ctor_get(x_777, 1);
lean_inc(x_778);
if (lean_is_exclusive(x_777)) {
 lean_ctor_release(x_777, 0);
 lean_ctor_release(x_777, 1);
 x_779 = x_777;
} else {
 lean_dec_ref(x_777);
 x_779 = lean_box(0);
}
if (lean_is_scalar(x_779)) {
 x_780 = lean_alloc_ctor(0, 2, 0);
} else {
 x_780 = x_779;
}
lean_ctor_set(x_780, 0, x_1);
lean_ctor_set(x_780, 1, x_778);
return x_780;
}
}
else
{
lean_object* x_781; lean_object* x_782; 
lean_dec(x_636);
lean_dec(x_634);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_781 = lean_ctor_get(x_716, 0);
lean_inc(x_781);
lean_dec(x_716);
x_782 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_782, 0, x_781);
lean_ctor_set(x_782, 1, x_713);
return x_782;
}
}
}
else
{
uint8_t x_783; 
lean_dec(x_634);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_783 = !lean_is_exclusive(x_635);
if (x_783 == 0)
{
return x_635;
}
else
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; 
x_784 = lean_ctor_get(x_635, 0);
x_785 = lean_ctor_get(x_635, 1);
lean_inc(x_785);
lean_inc(x_784);
lean_dec(x_635);
x_786 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_786, 0, x_784);
lean_ctor_set(x_786, 1, x_785);
return x_786;
}
}
}
block_825:
{
lean_object* x_789; 
lean_dec(x_788);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_9);
x_789 = l_Lean_Meta_getFunInfo(x_9, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_789) == 0)
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; uint8_t x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; 
x_790 = lean_ctor_get(x_789, 0);
lean_inc(x_790);
x_791 = lean_ctor_get(x_789, 1);
lean_inc(x_791);
lean_dec(x_789);
x_792 = lean_ctor_get(x_790, 0);
lean_inc(x_792);
lean_dec(x_790);
x_793 = lean_array_get_size(x_10);
x_794 = lean_unsigned_to_nat(0u);
x_795 = lean_unsigned_to_nat(1u);
lean_inc(x_793);
x_796 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_796, 0, x_794);
lean_ctor_set(x_796, 1, x_793);
lean_ctor_set(x_796, 2, x_795);
x_797 = 0;
x_798 = lean_box(x_797);
lean_inc(x_10);
x_799 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_799, 0, x_10);
lean_ctor_set(x_799, 1, x_798);
x_800 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_796);
lean_inc(x_9);
lean_inc(x_1);
x_801 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_800, x_792, x_793, x_796, x_796, x_799, x_794, lean_box(0), lean_box(0), x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_791);
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_802; lean_object* x_803; uint8_t x_804; 
x_802 = lean_ctor_get(x_801, 0);
lean_inc(x_802);
x_803 = lean_ctor_get(x_802, 1);
lean_inc(x_803);
x_804 = lean_unbox(x_803);
lean_dec(x_803);
if (x_804 == 0)
{
uint8_t x_805; 
lean_dec(x_802);
lean_dec(x_9);
x_805 = !lean_is_exclusive(x_801);
if (x_805 == 0)
{
lean_object* x_806; 
x_806 = lean_ctor_get(x_801, 0);
lean_dec(x_806);
lean_ctor_set(x_801, 0, x_1);
return x_801;
}
else
{
lean_object* x_807; lean_object* x_808; 
x_807 = lean_ctor_get(x_801, 1);
lean_inc(x_807);
lean_dec(x_801);
x_808 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_808, 0, x_1);
lean_ctor_set(x_808, 1, x_807);
return x_808;
}
}
else
{
uint8_t x_809; 
lean_dec(x_1);
x_809 = !lean_is_exclusive(x_801);
if (x_809 == 0)
{
lean_object* x_810; lean_object* x_811; lean_object* x_812; 
x_810 = lean_ctor_get(x_801, 0);
lean_dec(x_810);
x_811 = lean_ctor_get(x_802, 0);
lean_inc(x_811);
lean_dec(x_802);
x_812 = l_Lean_mkAppN(x_9, x_811);
lean_dec(x_811);
lean_ctor_set(x_801, 0, x_812);
return x_801;
}
else
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; 
x_813 = lean_ctor_get(x_801, 1);
lean_inc(x_813);
lean_dec(x_801);
x_814 = lean_ctor_get(x_802, 0);
lean_inc(x_814);
lean_dec(x_802);
x_815 = l_Lean_mkAppN(x_9, x_814);
lean_dec(x_814);
x_816 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_816, 0, x_815);
lean_ctor_set(x_816, 1, x_813);
return x_816;
}
}
}
else
{
uint8_t x_817; 
lean_dec(x_9);
lean_dec(x_1);
x_817 = !lean_is_exclusive(x_801);
if (x_817 == 0)
{
return x_801;
}
else
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; 
x_818 = lean_ctor_get(x_801, 0);
x_819 = lean_ctor_get(x_801, 1);
lean_inc(x_819);
lean_inc(x_818);
lean_dec(x_801);
x_820 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_820, 0, x_818);
lean_ctor_set(x_820, 1, x_819);
return x_820;
}
}
}
else
{
uint8_t x_821; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_821 = !lean_is_exclusive(x_789);
if (x_821 == 0)
{
return x_789;
}
else
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; 
x_822 = lean_ctor_get(x_789, 0);
x_823 = lean_ctor_get(x_789, 1);
lean_inc(x_823);
lean_inc(x_822);
lean_dec(x_789);
x_824 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_824, 0, x_822);
lean_ctor_set(x_824, 1, x_823);
return x_824;
}
}
}
}
case 4:
{
lean_object* x_838; lean_object* x_992; lean_object* x_1030; uint8_t x_1031; 
lean_dec(x_11);
x_1030 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_1031 = l_Lean_Expr_isConstOf(x_9, x_1030);
if (x_1031 == 0)
{
lean_object* x_1032; 
x_1032 = lean_box(0);
x_992 = x_1032;
goto block_1029;
}
else
{
lean_object* x_1033; lean_object* x_1034; uint8_t x_1035; 
x_1033 = lean_array_get_size(x_10);
x_1034 = lean_unsigned_to_nat(2u);
x_1035 = lean_nat_dec_eq(x_1033, x_1034);
if (x_1035 == 0)
{
lean_object* x_1036; 
lean_dec(x_1033);
x_1036 = lean_box(0);
x_992 = x_1036;
goto block_1029;
}
else
{
lean_object* x_1037; uint8_t x_1038; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1037 = lean_unsigned_to_nat(0u);
x_1038 = lean_nat_dec_lt(x_1037, x_1033);
lean_dec(x_1033);
if (x_1038 == 0)
{
lean_object* x_1039; lean_object* x_1040; 
x_1039 = l_Lean_instInhabitedExpr;
x_1040 = l_outOfBounds___rarg(x_1039);
x_838 = x_1040;
goto block_991;
}
else
{
lean_object* x_1041; 
x_1041 = lean_array_fget(x_10, x_1037);
x_838 = x_1041;
goto block_991;
}
}
}
block_991:
{
lean_object* x_839; 
lean_inc(x_13);
lean_inc(x_838);
x_839 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_838, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_839) == 0)
{
lean_object* x_840; lean_object* x_841; lean_object* x_842; uint8_t x_843; 
x_840 = lean_ctor_get(x_839, 0);
lean_inc(x_840);
x_841 = lean_ctor_get(x_839, 1);
lean_inc(x_841);
lean_dec(x_839);
x_842 = lean_st_ref_get(x_13, x_841);
x_843 = !lean_is_exclusive(x_842);
if (x_843 == 0)
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; 
x_844 = lean_ctor_get(x_842, 0);
x_845 = lean_ctor_get(x_842, 1);
x_846 = lean_ctor_get(x_844, 1);
lean_inc(x_846);
lean_dec(x_844);
x_847 = lean_ctor_get(x_846, 2);
lean_inc(x_847);
lean_dec(x_846);
x_848 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_847, x_840);
if (lean_obj_tag(x_848) == 0)
{
size_t x_849; size_t x_850; uint8_t x_851; 
lean_free_object(x_842);
x_849 = lean_ptr_addr(x_838);
lean_dec(x_838);
x_850 = lean_ptr_addr(x_840);
x_851 = lean_usize_dec_eq(x_849, x_850);
if (x_851 == 0)
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; uint8_t x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; uint8_t x_881; 
lean_dec(x_1);
x_852 = lean_unsigned_to_nat(0u);
lean_inc(x_840);
x_853 = lean_array_set(x_10, x_852, x_840);
x_854 = l_Lean_mkAppN(x_9, x_853);
lean_dec(x_853);
x_855 = lean_st_ref_take(x_13, x_845);
x_856 = lean_ctor_get(x_855, 0);
lean_inc(x_856);
x_857 = lean_ctor_get(x_855, 1);
lean_inc(x_857);
lean_dec(x_855);
x_858 = lean_ctor_get(x_856, 0);
lean_inc(x_858);
x_859 = lean_ctor_get(x_856, 1);
lean_inc(x_859);
x_860 = lean_ctor_get(x_859, 0);
lean_inc(x_860);
x_861 = lean_ctor_get(x_859, 1);
lean_inc(x_861);
x_862 = lean_ctor_get(x_859, 2);
lean_inc(x_862);
lean_dec(x_859);
lean_inc(x_854);
x_863 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_862, x_840, x_854);
x_864 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_864, 0, x_860);
lean_ctor_set(x_864, 1, x_861);
lean_ctor_set(x_864, 2, x_863);
x_865 = lean_ctor_get(x_856, 2);
lean_inc(x_865);
x_866 = lean_ctor_get(x_856, 3);
lean_inc(x_866);
x_867 = lean_ctor_get(x_856, 4);
lean_inc(x_867);
x_868 = lean_ctor_get(x_856, 5);
lean_inc(x_868);
x_869 = lean_ctor_get(x_856, 6);
lean_inc(x_869);
x_870 = lean_ctor_get_uint8(x_856, sizeof(void*)*15);
x_871 = lean_ctor_get(x_856, 7);
lean_inc(x_871);
x_872 = lean_ctor_get(x_856, 8);
lean_inc(x_872);
x_873 = lean_ctor_get(x_856, 9);
lean_inc(x_873);
x_874 = lean_ctor_get(x_856, 10);
lean_inc(x_874);
x_875 = lean_ctor_get(x_856, 11);
lean_inc(x_875);
x_876 = lean_ctor_get(x_856, 12);
lean_inc(x_876);
x_877 = lean_ctor_get(x_856, 13);
lean_inc(x_877);
x_878 = lean_ctor_get(x_856, 14);
lean_inc(x_878);
lean_dec(x_856);
x_879 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_879, 0, x_858);
lean_ctor_set(x_879, 1, x_864);
lean_ctor_set(x_879, 2, x_865);
lean_ctor_set(x_879, 3, x_866);
lean_ctor_set(x_879, 4, x_867);
lean_ctor_set(x_879, 5, x_868);
lean_ctor_set(x_879, 6, x_869);
lean_ctor_set(x_879, 7, x_871);
lean_ctor_set(x_879, 8, x_872);
lean_ctor_set(x_879, 9, x_873);
lean_ctor_set(x_879, 10, x_874);
lean_ctor_set(x_879, 11, x_875);
lean_ctor_set(x_879, 12, x_876);
lean_ctor_set(x_879, 13, x_877);
lean_ctor_set(x_879, 14, x_878);
lean_ctor_set_uint8(x_879, sizeof(void*)*15, x_870);
x_880 = lean_st_ref_set(x_13, x_879, x_857);
lean_dec(x_13);
x_881 = !lean_is_exclusive(x_880);
if (x_881 == 0)
{
lean_object* x_882; 
x_882 = lean_ctor_get(x_880, 0);
lean_dec(x_882);
lean_ctor_set(x_880, 0, x_854);
return x_880;
}
else
{
lean_object* x_883; lean_object* x_884; 
x_883 = lean_ctor_get(x_880, 1);
lean_inc(x_883);
lean_dec(x_880);
x_884 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_884, 0, x_854);
lean_ctor_set(x_884, 1, x_883);
return x_884;
}
}
else
{
lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; uint8_t x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; uint8_t x_911; 
lean_dec(x_10);
lean_dec(x_9);
x_885 = lean_st_ref_take(x_13, x_845);
x_886 = lean_ctor_get(x_885, 0);
lean_inc(x_886);
x_887 = lean_ctor_get(x_885, 1);
lean_inc(x_887);
lean_dec(x_885);
x_888 = lean_ctor_get(x_886, 0);
lean_inc(x_888);
x_889 = lean_ctor_get(x_886, 1);
lean_inc(x_889);
x_890 = lean_ctor_get(x_889, 0);
lean_inc(x_890);
x_891 = lean_ctor_get(x_889, 1);
lean_inc(x_891);
x_892 = lean_ctor_get(x_889, 2);
lean_inc(x_892);
lean_dec(x_889);
lean_inc(x_1);
x_893 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_892, x_840, x_1);
x_894 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_894, 0, x_890);
lean_ctor_set(x_894, 1, x_891);
lean_ctor_set(x_894, 2, x_893);
x_895 = lean_ctor_get(x_886, 2);
lean_inc(x_895);
x_896 = lean_ctor_get(x_886, 3);
lean_inc(x_896);
x_897 = lean_ctor_get(x_886, 4);
lean_inc(x_897);
x_898 = lean_ctor_get(x_886, 5);
lean_inc(x_898);
x_899 = lean_ctor_get(x_886, 6);
lean_inc(x_899);
x_900 = lean_ctor_get_uint8(x_886, sizeof(void*)*15);
x_901 = lean_ctor_get(x_886, 7);
lean_inc(x_901);
x_902 = lean_ctor_get(x_886, 8);
lean_inc(x_902);
x_903 = lean_ctor_get(x_886, 9);
lean_inc(x_903);
x_904 = lean_ctor_get(x_886, 10);
lean_inc(x_904);
x_905 = lean_ctor_get(x_886, 11);
lean_inc(x_905);
x_906 = lean_ctor_get(x_886, 12);
lean_inc(x_906);
x_907 = lean_ctor_get(x_886, 13);
lean_inc(x_907);
x_908 = lean_ctor_get(x_886, 14);
lean_inc(x_908);
lean_dec(x_886);
x_909 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_909, 0, x_888);
lean_ctor_set(x_909, 1, x_894);
lean_ctor_set(x_909, 2, x_895);
lean_ctor_set(x_909, 3, x_896);
lean_ctor_set(x_909, 4, x_897);
lean_ctor_set(x_909, 5, x_898);
lean_ctor_set(x_909, 6, x_899);
lean_ctor_set(x_909, 7, x_901);
lean_ctor_set(x_909, 8, x_902);
lean_ctor_set(x_909, 9, x_903);
lean_ctor_set(x_909, 10, x_904);
lean_ctor_set(x_909, 11, x_905);
lean_ctor_set(x_909, 12, x_906);
lean_ctor_set(x_909, 13, x_907);
lean_ctor_set(x_909, 14, x_908);
lean_ctor_set_uint8(x_909, sizeof(void*)*15, x_900);
x_910 = lean_st_ref_set(x_13, x_909, x_887);
lean_dec(x_13);
x_911 = !lean_is_exclusive(x_910);
if (x_911 == 0)
{
lean_object* x_912; 
x_912 = lean_ctor_get(x_910, 0);
lean_dec(x_912);
lean_ctor_set(x_910, 0, x_1);
return x_910;
}
else
{
lean_object* x_913; lean_object* x_914; 
x_913 = lean_ctor_get(x_910, 1);
lean_inc(x_913);
lean_dec(x_910);
x_914 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_914, 0, x_1);
lean_ctor_set(x_914, 1, x_913);
return x_914;
}
}
}
else
{
lean_object* x_915; 
lean_dec(x_840);
lean_dec(x_838);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_915 = lean_ctor_get(x_848, 0);
lean_inc(x_915);
lean_dec(x_848);
lean_ctor_set(x_842, 0, x_915);
return x_842;
}
}
else
{
lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; 
x_916 = lean_ctor_get(x_842, 0);
x_917 = lean_ctor_get(x_842, 1);
lean_inc(x_917);
lean_inc(x_916);
lean_dec(x_842);
x_918 = lean_ctor_get(x_916, 1);
lean_inc(x_918);
lean_dec(x_916);
x_919 = lean_ctor_get(x_918, 2);
lean_inc(x_919);
lean_dec(x_918);
x_920 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_919, x_840);
if (lean_obj_tag(x_920) == 0)
{
size_t x_921; size_t x_922; uint8_t x_923; 
x_921 = lean_ptr_addr(x_838);
lean_dec(x_838);
x_922 = lean_ptr_addr(x_840);
x_923 = lean_usize_dec_eq(x_921, x_922);
if (x_923 == 0)
{
lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; uint8_t x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; 
lean_dec(x_1);
x_924 = lean_unsigned_to_nat(0u);
lean_inc(x_840);
x_925 = lean_array_set(x_10, x_924, x_840);
x_926 = l_Lean_mkAppN(x_9, x_925);
lean_dec(x_925);
x_927 = lean_st_ref_take(x_13, x_917);
x_928 = lean_ctor_get(x_927, 0);
lean_inc(x_928);
x_929 = lean_ctor_get(x_927, 1);
lean_inc(x_929);
lean_dec(x_927);
x_930 = lean_ctor_get(x_928, 0);
lean_inc(x_930);
x_931 = lean_ctor_get(x_928, 1);
lean_inc(x_931);
x_932 = lean_ctor_get(x_931, 0);
lean_inc(x_932);
x_933 = lean_ctor_get(x_931, 1);
lean_inc(x_933);
x_934 = lean_ctor_get(x_931, 2);
lean_inc(x_934);
lean_dec(x_931);
lean_inc(x_926);
x_935 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_934, x_840, x_926);
x_936 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_936, 0, x_932);
lean_ctor_set(x_936, 1, x_933);
lean_ctor_set(x_936, 2, x_935);
x_937 = lean_ctor_get(x_928, 2);
lean_inc(x_937);
x_938 = lean_ctor_get(x_928, 3);
lean_inc(x_938);
x_939 = lean_ctor_get(x_928, 4);
lean_inc(x_939);
x_940 = lean_ctor_get(x_928, 5);
lean_inc(x_940);
x_941 = lean_ctor_get(x_928, 6);
lean_inc(x_941);
x_942 = lean_ctor_get_uint8(x_928, sizeof(void*)*15);
x_943 = lean_ctor_get(x_928, 7);
lean_inc(x_943);
x_944 = lean_ctor_get(x_928, 8);
lean_inc(x_944);
x_945 = lean_ctor_get(x_928, 9);
lean_inc(x_945);
x_946 = lean_ctor_get(x_928, 10);
lean_inc(x_946);
x_947 = lean_ctor_get(x_928, 11);
lean_inc(x_947);
x_948 = lean_ctor_get(x_928, 12);
lean_inc(x_948);
x_949 = lean_ctor_get(x_928, 13);
lean_inc(x_949);
x_950 = lean_ctor_get(x_928, 14);
lean_inc(x_950);
lean_dec(x_928);
x_951 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_951, 0, x_930);
lean_ctor_set(x_951, 1, x_936);
lean_ctor_set(x_951, 2, x_937);
lean_ctor_set(x_951, 3, x_938);
lean_ctor_set(x_951, 4, x_939);
lean_ctor_set(x_951, 5, x_940);
lean_ctor_set(x_951, 6, x_941);
lean_ctor_set(x_951, 7, x_943);
lean_ctor_set(x_951, 8, x_944);
lean_ctor_set(x_951, 9, x_945);
lean_ctor_set(x_951, 10, x_946);
lean_ctor_set(x_951, 11, x_947);
lean_ctor_set(x_951, 12, x_948);
lean_ctor_set(x_951, 13, x_949);
lean_ctor_set(x_951, 14, x_950);
lean_ctor_set_uint8(x_951, sizeof(void*)*15, x_942);
x_952 = lean_st_ref_set(x_13, x_951, x_929);
lean_dec(x_13);
x_953 = lean_ctor_get(x_952, 1);
lean_inc(x_953);
if (lean_is_exclusive(x_952)) {
 lean_ctor_release(x_952, 0);
 lean_ctor_release(x_952, 1);
 x_954 = x_952;
} else {
 lean_dec_ref(x_952);
 x_954 = lean_box(0);
}
if (lean_is_scalar(x_954)) {
 x_955 = lean_alloc_ctor(0, 2, 0);
} else {
 x_955 = x_954;
}
lean_ctor_set(x_955, 0, x_926);
lean_ctor_set(x_955, 1, x_953);
return x_955;
}
else
{
lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; uint8_t x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; 
lean_dec(x_10);
lean_dec(x_9);
x_956 = lean_st_ref_take(x_13, x_917);
x_957 = lean_ctor_get(x_956, 0);
lean_inc(x_957);
x_958 = lean_ctor_get(x_956, 1);
lean_inc(x_958);
lean_dec(x_956);
x_959 = lean_ctor_get(x_957, 0);
lean_inc(x_959);
x_960 = lean_ctor_get(x_957, 1);
lean_inc(x_960);
x_961 = lean_ctor_get(x_960, 0);
lean_inc(x_961);
x_962 = lean_ctor_get(x_960, 1);
lean_inc(x_962);
x_963 = lean_ctor_get(x_960, 2);
lean_inc(x_963);
lean_dec(x_960);
lean_inc(x_1);
x_964 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_963, x_840, x_1);
x_965 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_965, 0, x_961);
lean_ctor_set(x_965, 1, x_962);
lean_ctor_set(x_965, 2, x_964);
x_966 = lean_ctor_get(x_957, 2);
lean_inc(x_966);
x_967 = lean_ctor_get(x_957, 3);
lean_inc(x_967);
x_968 = lean_ctor_get(x_957, 4);
lean_inc(x_968);
x_969 = lean_ctor_get(x_957, 5);
lean_inc(x_969);
x_970 = lean_ctor_get(x_957, 6);
lean_inc(x_970);
x_971 = lean_ctor_get_uint8(x_957, sizeof(void*)*15);
x_972 = lean_ctor_get(x_957, 7);
lean_inc(x_972);
x_973 = lean_ctor_get(x_957, 8);
lean_inc(x_973);
x_974 = lean_ctor_get(x_957, 9);
lean_inc(x_974);
x_975 = lean_ctor_get(x_957, 10);
lean_inc(x_975);
x_976 = lean_ctor_get(x_957, 11);
lean_inc(x_976);
x_977 = lean_ctor_get(x_957, 12);
lean_inc(x_977);
x_978 = lean_ctor_get(x_957, 13);
lean_inc(x_978);
x_979 = lean_ctor_get(x_957, 14);
lean_inc(x_979);
lean_dec(x_957);
x_980 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_980, 0, x_959);
lean_ctor_set(x_980, 1, x_965);
lean_ctor_set(x_980, 2, x_966);
lean_ctor_set(x_980, 3, x_967);
lean_ctor_set(x_980, 4, x_968);
lean_ctor_set(x_980, 5, x_969);
lean_ctor_set(x_980, 6, x_970);
lean_ctor_set(x_980, 7, x_972);
lean_ctor_set(x_980, 8, x_973);
lean_ctor_set(x_980, 9, x_974);
lean_ctor_set(x_980, 10, x_975);
lean_ctor_set(x_980, 11, x_976);
lean_ctor_set(x_980, 12, x_977);
lean_ctor_set(x_980, 13, x_978);
lean_ctor_set(x_980, 14, x_979);
lean_ctor_set_uint8(x_980, sizeof(void*)*15, x_971);
x_981 = lean_st_ref_set(x_13, x_980, x_958);
lean_dec(x_13);
x_982 = lean_ctor_get(x_981, 1);
lean_inc(x_982);
if (lean_is_exclusive(x_981)) {
 lean_ctor_release(x_981, 0);
 lean_ctor_release(x_981, 1);
 x_983 = x_981;
} else {
 lean_dec_ref(x_981);
 x_983 = lean_box(0);
}
if (lean_is_scalar(x_983)) {
 x_984 = lean_alloc_ctor(0, 2, 0);
} else {
 x_984 = x_983;
}
lean_ctor_set(x_984, 0, x_1);
lean_ctor_set(x_984, 1, x_982);
return x_984;
}
}
else
{
lean_object* x_985; lean_object* x_986; 
lean_dec(x_840);
lean_dec(x_838);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_985 = lean_ctor_get(x_920, 0);
lean_inc(x_985);
lean_dec(x_920);
x_986 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_986, 0, x_985);
lean_ctor_set(x_986, 1, x_917);
return x_986;
}
}
}
else
{
uint8_t x_987; 
lean_dec(x_838);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_987 = !lean_is_exclusive(x_839);
if (x_987 == 0)
{
return x_839;
}
else
{
lean_object* x_988; lean_object* x_989; lean_object* x_990; 
x_988 = lean_ctor_get(x_839, 0);
x_989 = lean_ctor_get(x_839, 1);
lean_inc(x_989);
lean_inc(x_988);
lean_dec(x_839);
x_990 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_990, 0, x_988);
lean_ctor_set(x_990, 1, x_989);
return x_990;
}
}
}
block_1029:
{
lean_object* x_993; 
lean_dec(x_992);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_9);
x_993 = l_Lean_Meta_getFunInfo(x_9, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_993) == 0)
{
lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; uint8_t x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; 
x_994 = lean_ctor_get(x_993, 0);
lean_inc(x_994);
x_995 = lean_ctor_get(x_993, 1);
lean_inc(x_995);
lean_dec(x_993);
x_996 = lean_ctor_get(x_994, 0);
lean_inc(x_996);
lean_dec(x_994);
x_997 = lean_array_get_size(x_10);
x_998 = lean_unsigned_to_nat(0u);
x_999 = lean_unsigned_to_nat(1u);
lean_inc(x_997);
x_1000 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1000, 0, x_998);
lean_ctor_set(x_1000, 1, x_997);
lean_ctor_set(x_1000, 2, x_999);
x_1001 = 0;
x_1002 = lean_box(x_1001);
lean_inc(x_10);
x_1003 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1003, 0, x_10);
lean_ctor_set(x_1003, 1, x_1002);
x_1004 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_1000);
lean_inc(x_9);
lean_inc(x_1);
x_1005 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1004, x_996, x_997, x_1000, x_1000, x_1003, x_998, lean_box(0), lean_box(0), x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_995);
if (lean_obj_tag(x_1005) == 0)
{
lean_object* x_1006; lean_object* x_1007; uint8_t x_1008; 
x_1006 = lean_ctor_get(x_1005, 0);
lean_inc(x_1006);
x_1007 = lean_ctor_get(x_1006, 1);
lean_inc(x_1007);
x_1008 = lean_unbox(x_1007);
lean_dec(x_1007);
if (x_1008 == 0)
{
uint8_t x_1009; 
lean_dec(x_1006);
lean_dec(x_9);
x_1009 = !lean_is_exclusive(x_1005);
if (x_1009 == 0)
{
lean_object* x_1010; 
x_1010 = lean_ctor_get(x_1005, 0);
lean_dec(x_1010);
lean_ctor_set(x_1005, 0, x_1);
return x_1005;
}
else
{
lean_object* x_1011; lean_object* x_1012; 
x_1011 = lean_ctor_get(x_1005, 1);
lean_inc(x_1011);
lean_dec(x_1005);
x_1012 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1012, 0, x_1);
lean_ctor_set(x_1012, 1, x_1011);
return x_1012;
}
}
else
{
uint8_t x_1013; 
lean_dec(x_1);
x_1013 = !lean_is_exclusive(x_1005);
if (x_1013 == 0)
{
lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; 
x_1014 = lean_ctor_get(x_1005, 0);
lean_dec(x_1014);
x_1015 = lean_ctor_get(x_1006, 0);
lean_inc(x_1015);
lean_dec(x_1006);
x_1016 = l_Lean_mkAppN(x_9, x_1015);
lean_dec(x_1015);
lean_ctor_set(x_1005, 0, x_1016);
return x_1005;
}
else
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; 
x_1017 = lean_ctor_get(x_1005, 1);
lean_inc(x_1017);
lean_dec(x_1005);
x_1018 = lean_ctor_get(x_1006, 0);
lean_inc(x_1018);
lean_dec(x_1006);
x_1019 = l_Lean_mkAppN(x_9, x_1018);
lean_dec(x_1018);
x_1020 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1020, 0, x_1019);
lean_ctor_set(x_1020, 1, x_1017);
return x_1020;
}
}
}
else
{
uint8_t x_1021; 
lean_dec(x_9);
lean_dec(x_1);
x_1021 = !lean_is_exclusive(x_1005);
if (x_1021 == 0)
{
return x_1005;
}
else
{
lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; 
x_1022 = lean_ctor_get(x_1005, 0);
x_1023 = lean_ctor_get(x_1005, 1);
lean_inc(x_1023);
lean_inc(x_1022);
lean_dec(x_1005);
x_1024 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1024, 0, x_1022);
lean_ctor_set(x_1024, 1, x_1023);
return x_1024;
}
}
}
else
{
uint8_t x_1025; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1025 = !lean_is_exclusive(x_993);
if (x_1025 == 0)
{
return x_993;
}
else
{
lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; 
x_1026 = lean_ctor_get(x_993, 0);
x_1027 = lean_ctor_get(x_993, 1);
lean_inc(x_1027);
lean_inc(x_1026);
lean_dec(x_993);
x_1028 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1028, 0, x_1026);
lean_ctor_set(x_1028, 1, x_1027);
return x_1028;
}
}
}
}
case 5:
{
lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; 
x_1042 = lean_ctor_get(x_9, 0);
lean_inc(x_1042);
x_1043 = lean_ctor_get(x_9, 1);
lean_inc(x_1043);
lean_dec(x_9);
x_1044 = lean_array_set(x_10, x_11, x_1043);
x_1045 = lean_unsigned_to_nat(1u);
x_1046 = lean_nat_sub(x_11, x_1045);
lean_dec(x_11);
x_9 = x_1042;
x_10 = x_1044;
x_11 = x_1046;
goto _start;
}
case 6:
{
lean_object* x_1048; lean_object* x_1202; lean_object* x_1240; uint8_t x_1241; 
lean_dec(x_11);
x_1240 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_1241 = l_Lean_Expr_isConstOf(x_9, x_1240);
if (x_1241 == 0)
{
lean_object* x_1242; 
x_1242 = lean_box(0);
x_1202 = x_1242;
goto block_1239;
}
else
{
lean_object* x_1243; lean_object* x_1244; uint8_t x_1245; 
x_1243 = lean_array_get_size(x_10);
x_1244 = lean_unsigned_to_nat(2u);
x_1245 = lean_nat_dec_eq(x_1243, x_1244);
if (x_1245 == 0)
{
lean_object* x_1246; 
lean_dec(x_1243);
x_1246 = lean_box(0);
x_1202 = x_1246;
goto block_1239;
}
else
{
lean_object* x_1247; uint8_t x_1248; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1247 = lean_unsigned_to_nat(0u);
x_1248 = lean_nat_dec_lt(x_1247, x_1243);
lean_dec(x_1243);
if (x_1248 == 0)
{
lean_object* x_1249; lean_object* x_1250; 
x_1249 = l_Lean_instInhabitedExpr;
x_1250 = l_outOfBounds___rarg(x_1249);
x_1048 = x_1250;
goto block_1201;
}
else
{
lean_object* x_1251; 
x_1251 = lean_array_fget(x_10, x_1247);
x_1048 = x_1251;
goto block_1201;
}
}
}
block_1201:
{
lean_object* x_1049; 
lean_inc(x_13);
lean_inc(x_1048);
x_1049 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_1048, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_1049) == 0)
{
lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; uint8_t x_1053; 
x_1050 = lean_ctor_get(x_1049, 0);
lean_inc(x_1050);
x_1051 = lean_ctor_get(x_1049, 1);
lean_inc(x_1051);
lean_dec(x_1049);
x_1052 = lean_st_ref_get(x_13, x_1051);
x_1053 = !lean_is_exclusive(x_1052);
if (x_1053 == 0)
{
lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; 
x_1054 = lean_ctor_get(x_1052, 0);
x_1055 = lean_ctor_get(x_1052, 1);
x_1056 = lean_ctor_get(x_1054, 1);
lean_inc(x_1056);
lean_dec(x_1054);
x_1057 = lean_ctor_get(x_1056, 2);
lean_inc(x_1057);
lean_dec(x_1056);
x_1058 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_1057, x_1050);
if (lean_obj_tag(x_1058) == 0)
{
size_t x_1059; size_t x_1060; uint8_t x_1061; 
lean_free_object(x_1052);
x_1059 = lean_ptr_addr(x_1048);
lean_dec(x_1048);
x_1060 = lean_ptr_addr(x_1050);
x_1061 = lean_usize_dec_eq(x_1059, x_1060);
if (x_1061 == 0)
{
lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; uint8_t x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; uint8_t x_1091; 
lean_dec(x_1);
x_1062 = lean_unsigned_to_nat(0u);
lean_inc(x_1050);
x_1063 = lean_array_set(x_10, x_1062, x_1050);
x_1064 = l_Lean_mkAppN(x_9, x_1063);
lean_dec(x_1063);
x_1065 = lean_st_ref_take(x_13, x_1055);
x_1066 = lean_ctor_get(x_1065, 0);
lean_inc(x_1066);
x_1067 = lean_ctor_get(x_1065, 1);
lean_inc(x_1067);
lean_dec(x_1065);
x_1068 = lean_ctor_get(x_1066, 0);
lean_inc(x_1068);
x_1069 = lean_ctor_get(x_1066, 1);
lean_inc(x_1069);
x_1070 = lean_ctor_get(x_1069, 0);
lean_inc(x_1070);
x_1071 = lean_ctor_get(x_1069, 1);
lean_inc(x_1071);
x_1072 = lean_ctor_get(x_1069, 2);
lean_inc(x_1072);
lean_dec(x_1069);
lean_inc(x_1064);
x_1073 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1072, x_1050, x_1064);
x_1074 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1074, 0, x_1070);
lean_ctor_set(x_1074, 1, x_1071);
lean_ctor_set(x_1074, 2, x_1073);
x_1075 = lean_ctor_get(x_1066, 2);
lean_inc(x_1075);
x_1076 = lean_ctor_get(x_1066, 3);
lean_inc(x_1076);
x_1077 = lean_ctor_get(x_1066, 4);
lean_inc(x_1077);
x_1078 = lean_ctor_get(x_1066, 5);
lean_inc(x_1078);
x_1079 = lean_ctor_get(x_1066, 6);
lean_inc(x_1079);
x_1080 = lean_ctor_get_uint8(x_1066, sizeof(void*)*15);
x_1081 = lean_ctor_get(x_1066, 7);
lean_inc(x_1081);
x_1082 = lean_ctor_get(x_1066, 8);
lean_inc(x_1082);
x_1083 = lean_ctor_get(x_1066, 9);
lean_inc(x_1083);
x_1084 = lean_ctor_get(x_1066, 10);
lean_inc(x_1084);
x_1085 = lean_ctor_get(x_1066, 11);
lean_inc(x_1085);
x_1086 = lean_ctor_get(x_1066, 12);
lean_inc(x_1086);
x_1087 = lean_ctor_get(x_1066, 13);
lean_inc(x_1087);
x_1088 = lean_ctor_get(x_1066, 14);
lean_inc(x_1088);
lean_dec(x_1066);
x_1089 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_1089, 0, x_1068);
lean_ctor_set(x_1089, 1, x_1074);
lean_ctor_set(x_1089, 2, x_1075);
lean_ctor_set(x_1089, 3, x_1076);
lean_ctor_set(x_1089, 4, x_1077);
lean_ctor_set(x_1089, 5, x_1078);
lean_ctor_set(x_1089, 6, x_1079);
lean_ctor_set(x_1089, 7, x_1081);
lean_ctor_set(x_1089, 8, x_1082);
lean_ctor_set(x_1089, 9, x_1083);
lean_ctor_set(x_1089, 10, x_1084);
lean_ctor_set(x_1089, 11, x_1085);
lean_ctor_set(x_1089, 12, x_1086);
lean_ctor_set(x_1089, 13, x_1087);
lean_ctor_set(x_1089, 14, x_1088);
lean_ctor_set_uint8(x_1089, sizeof(void*)*15, x_1080);
x_1090 = lean_st_ref_set(x_13, x_1089, x_1067);
lean_dec(x_13);
x_1091 = !lean_is_exclusive(x_1090);
if (x_1091 == 0)
{
lean_object* x_1092; 
x_1092 = lean_ctor_get(x_1090, 0);
lean_dec(x_1092);
lean_ctor_set(x_1090, 0, x_1064);
return x_1090;
}
else
{
lean_object* x_1093; lean_object* x_1094; 
x_1093 = lean_ctor_get(x_1090, 1);
lean_inc(x_1093);
lean_dec(x_1090);
x_1094 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1094, 0, x_1064);
lean_ctor_set(x_1094, 1, x_1093);
return x_1094;
}
}
else
{
lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; uint8_t x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; uint8_t x_1121; 
lean_dec(x_10);
lean_dec(x_9);
x_1095 = lean_st_ref_take(x_13, x_1055);
x_1096 = lean_ctor_get(x_1095, 0);
lean_inc(x_1096);
x_1097 = lean_ctor_get(x_1095, 1);
lean_inc(x_1097);
lean_dec(x_1095);
x_1098 = lean_ctor_get(x_1096, 0);
lean_inc(x_1098);
x_1099 = lean_ctor_get(x_1096, 1);
lean_inc(x_1099);
x_1100 = lean_ctor_get(x_1099, 0);
lean_inc(x_1100);
x_1101 = lean_ctor_get(x_1099, 1);
lean_inc(x_1101);
x_1102 = lean_ctor_get(x_1099, 2);
lean_inc(x_1102);
lean_dec(x_1099);
lean_inc(x_1);
x_1103 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1102, x_1050, x_1);
x_1104 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1104, 0, x_1100);
lean_ctor_set(x_1104, 1, x_1101);
lean_ctor_set(x_1104, 2, x_1103);
x_1105 = lean_ctor_get(x_1096, 2);
lean_inc(x_1105);
x_1106 = lean_ctor_get(x_1096, 3);
lean_inc(x_1106);
x_1107 = lean_ctor_get(x_1096, 4);
lean_inc(x_1107);
x_1108 = lean_ctor_get(x_1096, 5);
lean_inc(x_1108);
x_1109 = lean_ctor_get(x_1096, 6);
lean_inc(x_1109);
x_1110 = lean_ctor_get_uint8(x_1096, sizeof(void*)*15);
x_1111 = lean_ctor_get(x_1096, 7);
lean_inc(x_1111);
x_1112 = lean_ctor_get(x_1096, 8);
lean_inc(x_1112);
x_1113 = lean_ctor_get(x_1096, 9);
lean_inc(x_1113);
x_1114 = lean_ctor_get(x_1096, 10);
lean_inc(x_1114);
x_1115 = lean_ctor_get(x_1096, 11);
lean_inc(x_1115);
x_1116 = lean_ctor_get(x_1096, 12);
lean_inc(x_1116);
x_1117 = lean_ctor_get(x_1096, 13);
lean_inc(x_1117);
x_1118 = lean_ctor_get(x_1096, 14);
lean_inc(x_1118);
lean_dec(x_1096);
x_1119 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_1119, 0, x_1098);
lean_ctor_set(x_1119, 1, x_1104);
lean_ctor_set(x_1119, 2, x_1105);
lean_ctor_set(x_1119, 3, x_1106);
lean_ctor_set(x_1119, 4, x_1107);
lean_ctor_set(x_1119, 5, x_1108);
lean_ctor_set(x_1119, 6, x_1109);
lean_ctor_set(x_1119, 7, x_1111);
lean_ctor_set(x_1119, 8, x_1112);
lean_ctor_set(x_1119, 9, x_1113);
lean_ctor_set(x_1119, 10, x_1114);
lean_ctor_set(x_1119, 11, x_1115);
lean_ctor_set(x_1119, 12, x_1116);
lean_ctor_set(x_1119, 13, x_1117);
lean_ctor_set(x_1119, 14, x_1118);
lean_ctor_set_uint8(x_1119, sizeof(void*)*15, x_1110);
x_1120 = lean_st_ref_set(x_13, x_1119, x_1097);
lean_dec(x_13);
x_1121 = !lean_is_exclusive(x_1120);
if (x_1121 == 0)
{
lean_object* x_1122; 
x_1122 = lean_ctor_get(x_1120, 0);
lean_dec(x_1122);
lean_ctor_set(x_1120, 0, x_1);
return x_1120;
}
else
{
lean_object* x_1123; lean_object* x_1124; 
x_1123 = lean_ctor_get(x_1120, 1);
lean_inc(x_1123);
lean_dec(x_1120);
x_1124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1124, 0, x_1);
lean_ctor_set(x_1124, 1, x_1123);
return x_1124;
}
}
}
else
{
lean_object* x_1125; 
lean_dec(x_1050);
lean_dec(x_1048);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_1125 = lean_ctor_get(x_1058, 0);
lean_inc(x_1125);
lean_dec(x_1058);
lean_ctor_set(x_1052, 0, x_1125);
return x_1052;
}
}
else
{
lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; 
x_1126 = lean_ctor_get(x_1052, 0);
x_1127 = lean_ctor_get(x_1052, 1);
lean_inc(x_1127);
lean_inc(x_1126);
lean_dec(x_1052);
x_1128 = lean_ctor_get(x_1126, 1);
lean_inc(x_1128);
lean_dec(x_1126);
x_1129 = lean_ctor_get(x_1128, 2);
lean_inc(x_1129);
lean_dec(x_1128);
x_1130 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_1129, x_1050);
if (lean_obj_tag(x_1130) == 0)
{
size_t x_1131; size_t x_1132; uint8_t x_1133; 
x_1131 = lean_ptr_addr(x_1048);
lean_dec(x_1048);
x_1132 = lean_ptr_addr(x_1050);
x_1133 = lean_usize_dec_eq(x_1131, x_1132);
if (x_1133 == 0)
{
lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; uint8_t x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; 
lean_dec(x_1);
x_1134 = lean_unsigned_to_nat(0u);
lean_inc(x_1050);
x_1135 = lean_array_set(x_10, x_1134, x_1050);
x_1136 = l_Lean_mkAppN(x_9, x_1135);
lean_dec(x_1135);
x_1137 = lean_st_ref_take(x_13, x_1127);
x_1138 = lean_ctor_get(x_1137, 0);
lean_inc(x_1138);
x_1139 = lean_ctor_get(x_1137, 1);
lean_inc(x_1139);
lean_dec(x_1137);
x_1140 = lean_ctor_get(x_1138, 0);
lean_inc(x_1140);
x_1141 = lean_ctor_get(x_1138, 1);
lean_inc(x_1141);
x_1142 = lean_ctor_get(x_1141, 0);
lean_inc(x_1142);
x_1143 = lean_ctor_get(x_1141, 1);
lean_inc(x_1143);
x_1144 = lean_ctor_get(x_1141, 2);
lean_inc(x_1144);
lean_dec(x_1141);
lean_inc(x_1136);
x_1145 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1144, x_1050, x_1136);
x_1146 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1146, 0, x_1142);
lean_ctor_set(x_1146, 1, x_1143);
lean_ctor_set(x_1146, 2, x_1145);
x_1147 = lean_ctor_get(x_1138, 2);
lean_inc(x_1147);
x_1148 = lean_ctor_get(x_1138, 3);
lean_inc(x_1148);
x_1149 = lean_ctor_get(x_1138, 4);
lean_inc(x_1149);
x_1150 = lean_ctor_get(x_1138, 5);
lean_inc(x_1150);
x_1151 = lean_ctor_get(x_1138, 6);
lean_inc(x_1151);
x_1152 = lean_ctor_get_uint8(x_1138, sizeof(void*)*15);
x_1153 = lean_ctor_get(x_1138, 7);
lean_inc(x_1153);
x_1154 = lean_ctor_get(x_1138, 8);
lean_inc(x_1154);
x_1155 = lean_ctor_get(x_1138, 9);
lean_inc(x_1155);
x_1156 = lean_ctor_get(x_1138, 10);
lean_inc(x_1156);
x_1157 = lean_ctor_get(x_1138, 11);
lean_inc(x_1157);
x_1158 = lean_ctor_get(x_1138, 12);
lean_inc(x_1158);
x_1159 = lean_ctor_get(x_1138, 13);
lean_inc(x_1159);
x_1160 = lean_ctor_get(x_1138, 14);
lean_inc(x_1160);
lean_dec(x_1138);
x_1161 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_1161, 0, x_1140);
lean_ctor_set(x_1161, 1, x_1146);
lean_ctor_set(x_1161, 2, x_1147);
lean_ctor_set(x_1161, 3, x_1148);
lean_ctor_set(x_1161, 4, x_1149);
lean_ctor_set(x_1161, 5, x_1150);
lean_ctor_set(x_1161, 6, x_1151);
lean_ctor_set(x_1161, 7, x_1153);
lean_ctor_set(x_1161, 8, x_1154);
lean_ctor_set(x_1161, 9, x_1155);
lean_ctor_set(x_1161, 10, x_1156);
lean_ctor_set(x_1161, 11, x_1157);
lean_ctor_set(x_1161, 12, x_1158);
lean_ctor_set(x_1161, 13, x_1159);
lean_ctor_set(x_1161, 14, x_1160);
lean_ctor_set_uint8(x_1161, sizeof(void*)*15, x_1152);
x_1162 = lean_st_ref_set(x_13, x_1161, x_1139);
lean_dec(x_13);
x_1163 = lean_ctor_get(x_1162, 1);
lean_inc(x_1163);
if (lean_is_exclusive(x_1162)) {
 lean_ctor_release(x_1162, 0);
 lean_ctor_release(x_1162, 1);
 x_1164 = x_1162;
} else {
 lean_dec_ref(x_1162);
 x_1164 = lean_box(0);
}
if (lean_is_scalar(x_1164)) {
 x_1165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1165 = x_1164;
}
lean_ctor_set(x_1165, 0, x_1136);
lean_ctor_set(x_1165, 1, x_1163);
return x_1165;
}
else
{
lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; uint8_t x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; 
lean_dec(x_10);
lean_dec(x_9);
x_1166 = lean_st_ref_take(x_13, x_1127);
x_1167 = lean_ctor_get(x_1166, 0);
lean_inc(x_1167);
x_1168 = lean_ctor_get(x_1166, 1);
lean_inc(x_1168);
lean_dec(x_1166);
x_1169 = lean_ctor_get(x_1167, 0);
lean_inc(x_1169);
x_1170 = lean_ctor_get(x_1167, 1);
lean_inc(x_1170);
x_1171 = lean_ctor_get(x_1170, 0);
lean_inc(x_1171);
x_1172 = lean_ctor_get(x_1170, 1);
lean_inc(x_1172);
x_1173 = lean_ctor_get(x_1170, 2);
lean_inc(x_1173);
lean_dec(x_1170);
lean_inc(x_1);
x_1174 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1173, x_1050, x_1);
x_1175 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1175, 0, x_1171);
lean_ctor_set(x_1175, 1, x_1172);
lean_ctor_set(x_1175, 2, x_1174);
x_1176 = lean_ctor_get(x_1167, 2);
lean_inc(x_1176);
x_1177 = lean_ctor_get(x_1167, 3);
lean_inc(x_1177);
x_1178 = lean_ctor_get(x_1167, 4);
lean_inc(x_1178);
x_1179 = lean_ctor_get(x_1167, 5);
lean_inc(x_1179);
x_1180 = lean_ctor_get(x_1167, 6);
lean_inc(x_1180);
x_1181 = lean_ctor_get_uint8(x_1167, sizeof(void*)*15);
x_1182 = lean_ctor_get(x_1167, 7);
lean_inc(x_1182);
x_1183 = lean_ctor_get(x_1167, 8);
lean_inc(x_1183);
x_1184 = lean_ctor_get(x_1167, 9);
lean_inc(x_1184);
x_1185 = lean_ctor_get(x_1167, 10);
lean_inc(x_1185);
x_1186 = lean_ctor_get(x_1167, 11);
lean_inc(x_1186);
x_1187 = lean_ctor_get(x_1167, 12);
lean_inc(x_1187);
x_1188 = lean_ctor_get(x_1167, 13);
lean_inc(x_1188);
x_1189 = lean_ctor_get(x_1167, 14);
lean_inc(x_1189);
lean_dec(x_1167);
x_1190 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_1190, 0, x_1169);
lean_ctor_set(x_1190, 1, x_1175);
lean_ctor_set(x_1190, 2, x_1176);
lean_ctor_set(x_1190, 3, x_1177);
lean_ctor_set(x_1190, 4, x_1178);
lean_ctor_set(x_1190, 5, x_1179);
lean_ctor_set(x_1190, 6, x_1180);
lean_ctor_set(x_1190, 7, x_1182);
lean_ctor_set(x_1190, 8, x_1183);
lean_ctor_set(x_1190, 9, x_1184);
lean_ctor_set(x_1190, 10, x_1185);
lean_ctor_set(x_1190, 11, x_1186);
lean_ctor_set(x_1190, 12, x_1187);
lean_ctor_set(x_1190, 13, x_1188);
lean_ctor_set(x_1190, 14, x_1189);
lean_ctor_set_uint8(x_1190, sizeof(void*)*15, x_1181);
x_1191 = lean_st_ref_set(x_13, x_1190, x_1168);
lean_dec(x_13);
x_1192 = lean_ctor_get(x_1191, 1);
lean_inc(x_1192);
if (lean_is_exclusive(x_1191)) {
 lean_ctor_release(x_1191, 0);
 lean_ctor_release(x_1191, 1);
 x_1193 = x_1191;
} else {
 lean_dec_ref(x_1191);
 x_1193 = lean_box(0);
}
if (lean_is_scalar(x_1193)) {
 x_1194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1194 = x_1193;
}
lean_ctor_set(x_1194, 0, x_1);
lean_ctor_set(x_1194, 1, x_1192);
return x_1194;
}
}
else
{
lean_object* x_1195; lean_object* x_1196; 
lean_dec(x_1050);
lean_dec(x_1048);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_1195 = lean_ctor_get(x_1130, 0);
lean_inc(x_1195);
lean_dec(x_1130);
x_1196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1196, 0, x_1195);
lean_ctor_set(x_1196, 1, x_1127);
return x_1196;
}
}
}
else
{
uint8_t x_1197; 
lean_dec(x_1048);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_1197 = !lean_is_exclusive(x_1049);
if (x_1197 == 0)
{
return x_1049;
}
else
{
lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; 
x_1198 = lean_ctor_get(x_1049, 0);
x_1199 = lean_ctor_get(x_1049, 1);
lean_inc(x_1199);
lean_inc(x_1198);
lean_dec(x_1049);
x_1200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1200, 0, x_1198);
lean_ctor_set(x_1200, 1, x_1199);
return x_1200;
}
}
}
block_1239:
{
lean_object* x_1203; 
lean_dec(x_1202);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_9);
x_1203 = l_Lean_Meta_getFunInfo(x_9, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_1203) == 0)
{
lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; uint8_t x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; 
x_1204 = lean_ctor_get(x_1203, 0);
lean_inc(x_1204);
x_1205 = lean_ctor_get(x_1203, 1);
lean_inc(x_1205);
lean_dec(x_1203);
x_1206 = lean_ctor_get(x_1204, 0);
lean_inc(x_1206);
lean_dec(x_1204);
x_1207 = lean_array_get_size(x_10);
x_1208 = lean_unsigned_to_nat(0u);
x_1209 = lean_unsigned_to_nat(1u);
lean_inc(x_1207);
x_1210 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1210, 0, x_1208);
lean_ctor_set(x_1210, 1, x_1207);
lean_ctor_set(x_1210, 2, x_1209);
x_1211 = 0;
x_1212 = lean_box(x_1211);
lean_inc(x_10);
x_1213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1213, 0, x_10);
lean_ctor_set(x_1213, 1, x_1212);
x_1214 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_1210);
lean_inc(x_9);
lean_inc(x_1);
x_1215 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1214, x_1206, x_1207, x_1210, x_1210, x_1213, x_1208, lean_box(0), lean_box(0), x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_1205);
if (lean_obj_tag(x_1215) == 0)
{
lean_object* x_1216; lean_object* x_1217; uint8_t x_1218; 
x_1216 = lean_ctor_get(x_1215, 0);
lean_inc(x_1216);
x_1217 = lean_ctor_get(x_1216, 1);
lean_inc(x_1217);
x_1218 = lean_unbox(x_1217);
lean_dec(x_1217);
if (x_1218 == 0)
{
uint8_t x_1219; 
lean_dec(x_1216);
lean_dec(x_9);
x_1219 = !lean_is_exclusive(x_1215);
if (x_1219 == 0)
{
lean_object* x_1220; 
x_1220 = lean_ctor_get(x_1215, 0);
lean_dec(x_1220);
lean_ctor_set(x_1215, 0, x_1);
return x_1215;
}
else
{
lean_object* x_1221; lean_object* x_1222; 
x_1221 = lean_ctor_get(x_1215, 1);
lean_inc(x_1221);
lean_dec(x_1215);
x_1222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1222, 0, x_1);
lean_ctor_set(x_1222, 1, x_1221);
return x_1222;
}
}
else
{
uint8_t x_1223; 
lean_dec(x_1);
x_1223 = !lean_is_exclusive(x_1215);
if (x_1223 == 0)
{
lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; 
x_1224 = lean_ctor_get(x_1215, 0);
lean_dec(x_1224);
x_1225 = lean_ctor_get(x_1216, 0);
lean_inc(x_1225);
lean_dec(x_1216);
x_1226 = l_Lean_mkAppN(x_9, x_1225);
lean_dec(x_1225);
lean_ctor_set(x_1215, 0, x_1226);
return x_1215;
}
else
{
lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; 
x_1227 = lean_ctor_get(x_1215, 1);
lean_inc(x_1227);
lean_dec(x_1215);
x_1228 = lean_ctor_get(x_1216, 0);
lean_inc(x_1228);
lean_dec(x_1216);
x_1229 = l_Lean_mkAppN(x_9, x_1228);
lean_dec(x_1228);
x_1230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1230, 0, x_1229);
lean_ctor_set(x_1230, 1, x_1227);
return x_1230;
}
}
}
else
{
uint8_t x_1231; 
lean_dec(x_9);
lean_dec(x_1);
x_1231 = !lean_is_exclusive(x_1215);
if (x_1231 == 0)
{
return x_1215;
}
else
{
lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; 
x_1232 = lean_ctor_get(x_1215, 0);
x_1233 = lean_ctor_get(x_1215, 1);
lean_inc(x_1233);
lean_inc(x_1232);
lean_dec(x_1215);
x_1234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1234, 0, x_1232);
lean_ctor_set(x_1234, 1, x_1233);
return x_1234;
}
}
}
else
{
uint8_t x_1235; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1235 = !lean_is_exclusive(x_1203);
if (x_1235 == 0)
{
return x_1203;
}
else
{
lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; 
x_1236 = lean_ctor_get(x_1203, 0);
x_1237 = lean_ctor_get(x_1203, 1);
lean_inc(x_1237);
lean_inc(x_1236);
lean_dec(x_1203);
x_1238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1238, 0, x_1236);
lean_ctor_set(x_1238, 1, x_1237);
return x_1238;
}
}
}
}
case 7:
{
lean_object* x_1252; lean_object* x_1406; lean_object* x_1444; uint8_t x_1445; 
lean_dec(x_11);
x_1444 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_1445 = l_Lean_Expr_isConstOf(x_9, x_1444);
if (x_1445 == 0)
{
lean_object* x_1446; 
x_1446 = lean_box(0);
x_1406 = x_1446;
goto block_1443;
}
else
{
lean_object* x_1447; lean_object* x_1448; uint8_t x_1449; 
x_1447 = lean_array_get_size(x_10);
x_1448 = lean_unsigned_to_nat(2u);
x_1449 = lean_nat_dec_eq(x_1447, x_1448);
if (x_1449 == 0)
{
lean_object* x_1450; 
lean_dec(x_1447);
x_1450 = lean_box(0);
x_1406 = x_1450;
goto block_1443;
}
else
{
lean_object* x_1451; uint8_t x_1452; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1451 = lean_unsigned_to_nat(0u);
x_1452 = lean_nat_dec_lt(x_1451, x_1447);
lean_dec(x_1447);
if (x_1452 == 0)
{
lean_object* x_1453; lean_object* x_1454; 
x_1453 = l_Lean_instInhabitedExpr;
x_1454 = l_outOfBounds___rarg(x_1453);
x_1252 = x_1454;
goto block_1405;
}
else
{
lean_object* x_1455; 
x_1455 = lean_array_fget(x_10, x_1451);
x_1252 = x_1455;
goto block_1405;
}
}
}
block_1405:
{
lean_object* x_1253; 
lean_inc(x_13);
lean_inc(x_1252);
x_1253 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_1252, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_1253) == 0)
{
lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; uint8_t x_1257; 
x_1254 = lean_ctor_get(x_1253, 0);
lean_inc(x_1254);
x_1255 = lean_ctor_get(x_1253, 1);
lean_inc(x_1255);
lean_dec(x_1253);
x_1256 = lean_st_ref_get(x_13, x_1255);
x_1257 = !lean_is_exclusive(x_1256);
if (x_1257 == 0)
{
lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; 
x_1258 = lean_ctor_get(x_1256, 0);
x_1259 = lean_ctor_get(x_1256, 1);
x_1260 = lean_ctor_get(x_1258, 1);
lean_inc(x_1260);
lean_dec(x_1258);
x_1261 = lean_ctor_get(x_1260, 2);
lean_inc(x_1261);
lean_dec(x_1260);
x_1262 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_1261, x_1254);
if (lean_obj_tag(x_1262) == 0)
{
size_t x_1263; size_t x_1264; uint8_t x_1265; 
lean_free_object(x_1256);
x_1263 = lean_ptr_addr(x_1252);
lean_dec(x_1252);
x_1264 = lean_ptr_addr(x_1254);
x_1265 = lean_usize_dec_eq(x_1263, x_1264);
if (x_1265 == 0)
{
lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; uint8_t x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; uint8_t x_1295; 
lean_dec(x_1);
x_1266 = lean_unsigned_to_nat(0u);
lean_inc(x_1254);
x_1267 = lean_array_set(x_10, x_1266, x_1254);
x_1268 = l_Lean_mkAppN(x_9, x_1267);
lean_dec(x_1267);
x_1269 = lean_st_ref_take(x_13, x_1259);
x_1270 = lean_ctor_get(x_1269, 0);
lean_inc(x_1270);
x_1271 = lean_ctor_get(x_1269, 1);
lean_inc(x_1271);
lean_dec(x_1269);
x_1272 = lean_ctor_get(x_1270, 0);
lean_inc(x_1272);
x_1273 = lean_ctor_get(x_1270, 1);
lean_inc(x_1273);
x_1274 = lean_ctor_get(x_1273, 0);
lean_inc(x_1274);
x_1275 = lean_ctor_get(x_1273, 1);
lean_inc(x_1275);
x_1276 = lean_ctor_get(x_1273, 2);
lean_inc(x_1276);
lean_dec(x_1273);
lean_inc(x_1268);
x_1277 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1276, x_1254, x_1268);
x_1278 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1278, 0, x_1274);
lean_ctor_set(x_1278, 1, x_1275);
lean_ctor_set(x_1278, 2, x_1277);
x_1279 = lean_ctor_get(x_1270, 2);
lean_inc(x_1279);
x_1280 = lean_ctor_get(x_1270, 3);
lean_inc(x_1280);
x_1281 = lean_ctor_get(x_1270, 4);
lean_inc(x_1281);
x_1282 = lean_ctor_get(x_1270, 5);
lean_inc(x_1282);
x_1283 = lean_ctor_get(x_1270, 6);
lean_inc(x_1283);
x_1284 = lean_ctor_get_uint8(x_1270, sizeof(void*)*15);
x_1285 = lean_ctor_get(x_1270, 7);
lean_inc(x_1285);
x_1286 = lean_ctor_get(x_1270, 8);
lean_inc(x_1286);
x_1287 = lean_ctor_get(x_1270, 9);
lean_inc(x_1287);
x_1288 = lean_ctor_get(x_1270, 10);
lean_inc(x_1288);
x_1289 = lean_ctor_get(x_1270, 11);
lean_inc(x_1289);
x_1290 = lean_ctor_get(x_1270, 12);
lean_inc(x_1290);
x_1291 = lean_ctor_get(x_1270, 13);
lean_inc(x_1291);
x_1292 = lean_ctor_get(x_1270, 14);
lean_inc(x_1292);
lean_dec(x_1270);
x_1293 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_1293, 0, x_1272);
lean_ctor_set(x_1293, 1, x_1278);
lean_ctor_set(x_1293, 2, x_1279);
lean_ctor_set(x_1293, 3, x_1280);
lean_ctor_set(x_1293, 4, x_1281);
lean_ctor_set(x_1293, 5, x_1282);
lean_ctor_set(x_1293, 6, x_1283);
lean_ctor_set(x_1293, 7, x_1285);
lean_ctor_set(x_1293, 8, x_1286);
lean_ctor_set(x_1293, 9, x_1287);
lean_ctor_set(x_1293, 10, x_1288);
lean_ctor_set(x_1293, 11, x_1289);
lean_ctor_set(x_1293, 12, x_1290);
lean_ctor_set(x_1293, 13, x_1291);
lean_ctor_set(x_1293, 14, x_1292);
lean_ctor_set_uint8(x_1293, sizeof(void*)*15, x_1284);
x_1294 = lean_st_ref_set(x_13, x_1293, x_1271);
lean_dec(x_13);
x_1295 = !lean_is_exclusive(x_1294);
if (x_1295 == 0)
{
lean_object* x_1296; 
x_1296 = lean_ctor_get(x_1294, 0);
lean_dec(x_1296);
lean_ctor_set(x_1294, 0, x_1268);
return x_1294;
}
else
{
lean_object* x_1297; lean_object* x_1298; 
x_1297 = lean_ctor_get(x_1294, 1);
lean_inc(x_1297);
lean_dec(x_1294);
x_1298 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1298, 0, x_1268);
lean_ctor_set(x_1298, 1, x_1297);
return x_1298;
}
}
else
{
lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; uint8_t x_1314; lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; uint8_t x_1325; 
lean_dec(x_10);
lean_dec(x_9);
x_1299 = lean_st_ref_take(x_13, x_1259);
x_1300 = lean_ctor_get(x_1299, 0);
lean_inc(x_1300);
x_1301 = lean_ctor_get(x_1299, 1);
lean_inc(x_1301);
lean_dec(x_1299);
x_1302 = lean_ctor_get(x_1300, 0);
lean_inc(x_1302);
x_1303 = lean_ctor_get(x_1300, 1);
lean_inc(x_1303);
x_1304 = lean_ctor_get(x_1303, 0);
lean_inc(x_1304);
x_1305 = lean_ctor_get(x_1303, 1);
lean_inc(x_1305);
x_1306 = lean_ctor_get(x_1303, 2);
lean_inc(x_1306);
lean_dec(x_1303);
lean_inc(x_1);
x_1307 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1306, x_1254, x_1);
x_1308 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1308, 0, x_1304);
lean_ctor_set(x_1308, 1, x_1305);
lean_ctor_set(x_1308, 2, x_1307);
x_1309 = lean_ctor_get(x_1300, 2);
lean_inc(x_1309);
x_1310 = lean_ctor_get(x_1300, 3);
lean_inc(x_1310);
x_1311 = lean_ctor_get(x_1300, 4);
lean_inc(x_1311);
x_1312 = lean_ctor_get(x_1300, 5);
lean_inc(x_1312);
x_1313 = lean_ctor_get(x_1300, 6);
lean_inc(x_1313);
x_1314 = lean_ctor_get_uint8(x_1300, sizeof(void*)*15);
x_1315 = lean_ctor_get(x_1300, 7);
lean_inc(x_1315);
x_1316 = lean_ctor_get(x_1300, 8);
lean_inc(x_1316);
x_1317 = lean_ctor_get(x_1300, 9);
lean_inc(x_1317);
x_1318 = lean_ctor_get(x_1300, 10);
lean_inc(x_1318);
x_1319 = lean_ctor_get(x_1300, 11);
lean_inc(x_1319);
x_1320 = lean_ctor_get(x_1300, 12);
lean_inc(x_1320);
x_1321 = lean_ctor_get(x_1300, 13);
lean_inc(x_1321);
x_1322 = lean_ctor_get(x_1300, 14);
lean_inc(x_1322);
lean_dec(x_1300);
x_1323 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_1323, 0, x_1302);
lean_ctor_set(x_1323, 1, x_1308);
lean_ctor_set(x_1323, 2, x_1309);
lean_ctor_set(x_1323, 3, x_1310);
lean_ctor_set(x_1323, 4, x_1311);
lean_ctor_set(x_1323, 5, x_1312);
lean_ctor_set(x_1323, 6, x_1313);
lean_ctor_set(x_1323, 7, x_1315);
lean_ctor_set(x_1323, 8, x_1316);
lean_ctor_set(x_1323, 9, x_1317);
lean_ctor_set(x_1323, 10, x_1318);
lean_ctor_set(x_1323, 11, x_1319);
lean_ctor_set(x_1323, 12, x_1320);
lean_ctor_set(x_1323, 13, x_1321);
lean_ctor_set(x_1323, 14, x_1322);
lean_ctor_set_uint8(x_1323, sizeof(void*)*15, x_1314);
x_1324 = lean_st_ref_set(x_13, x_1323, x_1301);
lean_dec(x_13);
x_1325 = !lean_is_exclusive(x_1324);
if (x_1325 == 0)
{
lean_object* x_1326; 
x_1326 = lean_ctor_get(x_1324, 0);
lean_dec(x_1326);
lean_ctor_set(x_1324, 0, x_1);
return x_1324;
}
else
{
lean_object* x_1327; lean_object* x_1328; 
x_1327 = lean_ctor_get(x_1324, 1);
lean_inc(x_1327);
lean_dec(x_1324);
x_1328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1328, 0, x_1);
lean_ctor_set(x_1328, 1, x_1327);
return x_1328;
}
}
}
else
{
lean_object* x_1329; 
lean_dec(x_1254);
lean_dec(x_1252);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_1329 = lean_ctor_get(x_1262, 0);
lean_inc(x_1329);
lean_dec(x_1262);
lean_ctor_set(x_1256, 0, x_1329);
return x_1256;
}
}
else
{
lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; 
x_1330 = lean_ctor_get(x_1256, 0);
x_1331 = lean_ctor_get(x_1256, 1);
lean_inc(x_1331);
lean_inc(x_1330);
lean_dec(x_1256);
x_1332 = lean_ctor_get(x_1330, 1);
lean_inc(x_1332);
lean_dec(x_1330);
x_1333 = lean_ctor_get(x_1332, 2);
lean_inc(x_1333);
lean_dec(x_1332);
x_1334 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_1333, x_1254);
if (lean_obj_tag(x_1334) == 0)
{
size_t x_1335; size_t x_1336; uint8_t x_1337; 
x_1335 = lean_ptr_addr(x_1252);
lean_dec(x_1252);
x_1336 = lean_ptr_addr(x_1254);
x_1337 = lean_usize_dec_eq(x_1335, x_1336);
if (x_1337 == 0)
{
lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; uint8_t x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; 
lean_dec(x_1);
x_1338 = lean_unsigned_to_nat(0u);
lean_inc(x_1254);
x_1339 = lean_array_set(x_10, x_1338, x_1254);
x_1340 = l_Lean_mkAppN(x_9, x_1339);
lean_dec(x_1339);
x_1341 = lean_st_ref_take(x_13, x_1331);
x_1342 = lean_ctor_get(x_1341, 0);
lean_inc(x_1342);
x_1343 = lean_ctor_get(x_1341, 1);
lean_inc(x_1343);
lean_dec(x_1341);
x_1344 = lean_ctor_get(x_1342, 0);
lean_inc(x_1344);
x_1345 = lean_ctor_get(x_1342, 1);
lean_inc(x_1345);
x_1346 = lean_ctor_get(x_1345, 0);
lean_inc(x_1346);
x_1347 = lean_ctor_get(x_1345, 1);
lean_inc(x_1347);
x_1348 = lean_ctor_get(x_1345, 2);
lean_inc(x_1348);
lean_dec(x_1345);
lean_inc(x_1340);
x_1349 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1348, x_1254, x_1340);
x_1350 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1350, 0, x_1346);
lean_ctor_set(x_1350, 1, x_1347);
lean_ctor_set(x_1350, 2, x_1349);
x_1351 = lean_ctor_get(x_1342, 2);
lean_inc(x_1351);
x_1352 = lean_ctor_get(x_1342, 3);
lean_inc(x_1352);
x_1353 = lean_ctor_get(x_1342, 4);
lean_inc(x_1353);
x_1354 = lean_ctor_get(x_1342, 5);
lean_inc(x_1354);
x_1355 = lean_ctor_get(x_1342, 6);
lean_inc(x_1355);
x_1356 = lean_ctor_get_uint8(x_1342, sizeof(void*)*15);
x_1357 = lean_ctor_get(x_1342, 7);
lean_inc(x_1357);
x_1358 = lean_ctor_get(x_1342, 8);
lean_inc(x_1358);
x_1359 = lean_ctor_get(x_1342, 9);
lean_inc(x_1359);
x_1360 = lean_ctor_get(x_1342, 10);
lean_inc(x_1360);
x_1361 = lean_ctor_get(x_1342, 11);
lean_inc(x_1361);
x_1362 = lean_ctor_get(x_1342, 12);
lean_inc(x_1362);
x_1363 = lean_ctor_get(x_1342, 13);
lean_inc(x_1363);
x_1364 = lean_ctor_get(x_1342, 14);
lean_inc(x_1364);
lean_dec(x_1342);
x_1365 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_1365, 0, x_1344);
lean_ctor_set(x_1365, 1, x_1350);
lean_ctor_set(x_1365, 2, x_1351);
lean_ctor_set(x_1365, 3, x_1352);
lean_ctor_set(x_1365, 4, x_1353);
lean_ctor_set(x_1365, 5, x_1354);
lean_ctor_set(x_1365, 6, x_1355);
lean_ctor_set(x_1365, 7, x_1357);
lean_ctor_set(x_1365, 8, x_1358);
lean_ctor_set(x_1365, 9, x_1359);
lean_ctor_set(x_1365, 10, x_1360);
lean_ctor_set(x_1365, 11, x_1361);
lean_ctor_set(x_1365, 12, x_1362);
lean_ctor_set(x_1365, 13, x_1363);
lean_ctor_set(x_1365, 14, x_1364);
lean_ctor_set_uint8(x_1365, sizeof(void*)*15, x_1356);
x_1366 = lean_st_ref_set(x_13, x_1365, x_1343);
lean_dec(x_13);
x_1367 = lean_ctor_get(x_1366, 1);
lean_inc(x_1367);
if (lean_is_exclusive(x_1366)) {
 lean_ctor_release(x_1366, 0);
 lean_ctor_release(x_1366, 1);
 x_1368 = x_1366;
} else {
 lean_dec_ref(x_1366);
 x_1368 = lean_box(0);
}
if (lean_is_scalar(x_1368)) {
 x_1369 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1369 = x_1368;
}
lean_ctor_set(x_1369, 0, x_1340);
lean_ctor_set(x_1369, 1, x_1367);
return x_1369;
}
else
{
lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; uint8_t x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; 
lean_dec(x_10);
lean_dec(x_9);
x_1370 = lean_st_ref_take(x_13, x_1331);
x_1371 = lean_ctor_get(x_1370, 0);
lean_inc(x_1371);
x_1372 = lean_ctor_get(x_1370, 1);
lean_inc(x_1372);
lean_dec(x_1370);
x_1373 = lean_ctor_get(x_1371, 0);
lean_inc(x_1373);
x_1374 = lean_ctor_get(x_1371, 1);
lean_inc(x_1374);
x_1375 = lean_ctor_get(x_1374, 0);
lean_inc(x_1375);
x_1376 = lean_ctor_get(x_1374, 1);
lean_inc(x_1376);
x_1377 = lean_ctor_get(x_1374, 2);
lean_inc(x_1377);
lean_dec(x_1374);
lean_inc(x_1);
x_1378 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1377, x_1254, x_1);
x_1379 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1379, 0, x_1375);
lean_ctor_set(x_1379, 1, x_1376);
lean_ctor_set(x_1379, 2, x_1378);
x_1380 = lean_ctor_get(x_1371, 2);
lean_inc(x_1380);
x_1381 = lean_ctor_get(x_1371, 3);
lean_inc(x_1381);
x_1382 = lean_ctor_get(x_1371, 4);
lean_inc(x_1382);
x_1383 = lean_ctor_get(x_1371, 5);
lean_inc(x_1383);
x_1384 = lean_ctor_get(x_1371, 6);
lean_inc(x_1384);
x_1385 = lean_ctor_get_uint8(x_1371, sizeof(void*)*15);
x_1386 = lean_ctor_get(x_1371, 7);
lean_inc(x_1386);
x_1387 = lean_ctor_get(x_1371, 8);
lean_inc(x_1387);
x_1388 = lean_ctor_get(x_1371, 9);
lean_inc(x_1388);
x_1389 = lean_ctor_get(x_1371, 10);
lean_inc(x_1389);
x_1390 = lean_ctor_get(x_1371, 11);
lean_inc(x_1390);
x_1391 = lean_ctor_get(x_1371, 12);
lean_inc(x_1391);
x_1392 = lean_ctor_get(x_1371, 13);
lean_inc(x_1392);
x_1393 = lean_ctor_get(x_1371, 14);
lean_inc(x_1393);
lean_dec(x_1371);
x_1394 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_1394, 0, x_1373);
lean_ctor_set(x_1394, 1, x_1379);
lean_ctor_set(x_1394, 2, x_1380);
lean_ctor_set(x_1394, 3, x_1381);
lean_ctor_set(x_1394, 4, x_1382);
lean_ctor_set(x_1394, 5, x_1383);
lean_ctor_set(x_1394, 6, x_1384);
lean_ctor_set(x_1394, 7, x_1386);
lean_ctor_set(x_1394, 8, x_1387);
lean_ctor_set(x_1394, 9, x_1388);
lean_ctor_set(x_1394, 10, x_1389);
lean_ctor_set(x_1394, 11, x_1390);
lean_ctor_set(x_1394, 12, x_1391);
lean_ctor_set(x_1394, 13, x_1392);
lean_ctor_set(x_1394, 14, x_1393);
lean_ctor_set_uint8(x_1394, sizeof(void*)*15, x_1385);
x_1395 = lean_st_ref_set(x_13, x_1394, x_1372);
lean_dec(x_13);
x_1396 = lean_ctor_get(x_1395, 1);
lean_inc(x_1396);
if (lean_is_exclusive(x_1395)) {
 lean_ctor_release(x_1395, 0);
 lean_ctor_release(x_1395, 1);
 x_1397 = x_1395;
} else {
 lean_dec_ref(x_1395);
 x_1397 = lean_box(0);
}
if (lean_is_scalar(x_1397)) {
 x_1398 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1398 = x_1397;
}
lean_ctor_set(x_1398, 0, x_1);
lean_ctor_set(x_1398, 1, x_1396);
return x_1398;
}
}
else
{
lean_object* x_1399; lean_object* x_1400; 
lean_dec(x_1254);
lean_dec(x_1252);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_1399 = lean_ctor_get(x_1334, 0);
lean_inc(x_1399);
lean_dec(x_1334);
x_1400 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1400, 0, x_1399);
lean_ctor_set(x_1400, 1, x_1331);
return x_1400;
}
}
}
else
{
uint8_t x_1401; 
lean_dec(x_1252);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_1401 = !lean_is_exclusive(x_1253);
if (x_1401 == 0)
{
return x_1253;
}
else
{
lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; 
x_1402 = lean_ctor_get(x_1253, 0);
x_1403 = lean_ctor_get(x_1253, 1);
lean_inc(x_1403);
lean_inc(x_1402);
lean_dec(x_1253);
x_1404 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1404, 0, x_1402);
lean_ctor_set(x_1404, 1, x_1403);
return x_1404;
}
}
}
block_1443:
{
lean_object* x_1407; 
lean_dec(x_1406);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_9);
x_1407 = l_Lean_Meta_getFunInfo(x_9, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_1407) == 0)
{
lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; uint8_t x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; 
x_1408 = lean_ctor_get(x_1407, 0);
lean_inc(x_1408);
x_1409 = lean_ctor_get(x_1407, 1);
lean_inc(x_1409);
lean_dec(x_1407);
x_1410 = lean_ctor_get(x_1408, 0);
lean_inc(x_1410);
lean_dec(x_1408);
x_1411 = lean_array_get_size(x_10);
x_1412 = lean_unsigned_to_nat(0u);
x_1413 = lean_unsigned_to_nat(1u);
lean_inc(x_1411);
x_1414 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1414, 0, x_1412);
lean_ctor_set(x_1414, 1, x_1411);
lean_ctor_set(x_1414, 2, x_1413);
x_1415 = 0;
x_1416 = lean_box(x_1415);
lean_inc(x_10);
x_1417 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1417, 0, x_10);
lean_ctor_set(x_1417, 1, x_1416);
x_1418 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_1414);
lean_inc(x_9);
lean_inc(x_1);
x_1419 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1418, x_1410, x_1411, x_1414, x_1414, x_1417, x_1412, lean_box(0), lean_box(0), x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_1409);
if (lean_obj_tag(x_1419) == 0)
{
lean_object* x_1420; lean_object* x_1421; uint8_t x_1422; 
x_1420 = lean_ctor_get(x_1419, 0);
lean_inc(x_1420);
x_1421 = lean_ctor_get(x_1420, 1);
lean_inc(x_1421);
x_1422 = lean_unbox(x_1421);
lean_dec(x_1421);
if (x_1422 == 0)
{
uint8_t x_1423; 
lean_dec(x_1420);
lean_dec(x_9);
x_1423 = !lean_is_exclusive(x_1419);
if (x_1423 == 0)
{
lean_object* x_1424; 
x_1424 = lean_ctor_get(x_1419, 0);
lean_dec(x_1424);
lean_ctor_set(x_1419, 0, x_1);
return x_1419;
}
else
{
lean_object* x_1425; lean_object* x_1426; 
x_1425 = lean_ctor_get(x_1419, 1);
lean_inc(x_1425);
lean_dec(x_1419);
x_1426 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1426, 0, x_1);
lean_ctor_set(x_1426, 1, x_1425);
return x_1426;
}
}
else
{
uint8_t x_1427; 
lean_dec(x_1);
x_1427 = !lean_is_exclusive(x_1419);
if (x_1427 == 0)
{
lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; 
x_1428 = lean_ctor_get(x_1419, 0);
lean_dec(x_1428);
x_1429 = lean_ctor_get(x_1420, 0);
lean_inc(x_1429);
lean_dec(x_1420);
x_1430 = l_Lean_mkAppN(x_9, x_1429);
lean_dec(x_1429);
lean_ctor_set(x_1419, 0, x_1430);
return x_1419;
}
else
{
lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; 
x_1431 = lean_ctor_get(x_1419, 1);
lean_inc(x_1431);
lean_dec(x_1419);
x_1432 = lean_ctor_get(x_1420, 0);
lean_inc(x_1432);
lean_dec(x_1420);
x_1433 = l_Lean_mkAppN(x_9, x_1432);
lean_dec(x_1432);
x_1434 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1434, 0, x_1433);
lean_ctor_set(x_1434, 1, x_1431);
return x_1434;
}
}
}
else
{
uint8_t x_1435; 
lean_dec(x_9);
lean_dec(x_1);
x_1435 = !lean_is_exclusive(x_1419);
if (x_1435 == 0)
{
return x_1419;
}
else
{
lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; 
x_1436 = lean_ctor_get(x_1419, 0);
x_1437 = lean_ctor_get(x_1419, 1);
lean_inc(x_1437);
lean_inc(x_1436);
lean_dec(x_1419);
x_1438 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1438, 0, x_1436);
lean_ctor_set(x_1438, 1, x_1437);
return x_1438;
}
}
}
else
{
uint8_t x_1439; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1439 = !lean_is_exclusive(x_1407);
if (x_1439 == 0)
{
return x_1407;
}
else
{
lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; 
x_1440 = lean_ctor_get(x_1407, 0);
x_1441 = lean_ctor_get(x_1407, 1);
lean_inc(x_1441);
lean_inc(x_1440);
lean_dec(x_1407);
x_1442 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1442, 0, x_1440);
lean_ctor_set(x_1442, 1, x_1441);
return x_1442;
}
}
}
}
case 8:
{
lean_object* x_1456; lean_object* x_1610; lean_object* x_1648; uint8_t x_1649; 
lean_dec(x_11);
x_1648 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_1649 = l_Lean_Expr_isConstOf(x_9, x_1648);
if (x_1649 == 0)
{
lean_object* x_1650; 
x_1650 = lean_box(0);
x_1610 = x_1650;
goto block_1647;
}
else
{
lean_object* x_1651; lean_object* x_1652; uint8_t x_1653; 
x_1651 = lean_array_get_size(x_10);
x_1652 = lean_unsigned_to_nat(2u);
x_1653 = lean_nat_dec_eq(x_1651, x_1652);
if (x_1653 == 0)
{
lean_object* x_1654; 
lean_dec(x_1651);
x_1654 = lean_box(0);
x_1610 = x_1654;
goto block_1647;
}
else
{
lean_object* x_1655; uint8_t x_1656; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1655 = lean_unsigned_to_nat(0u);
x_1656 = lean_nat_dec_lt(x_1655, x_1651);
lean_dec(x_1651);
if (x_1656 == 0)
{
lean_object* x_1657; lean_object* x_1658; 
x_1657 = l_Lean_instInhabitedExpr;
x_1658 = l_outOfBounds___rarg(x_1657);
x_1456 = x_1658;
goto block_1609;
}
else
{
lean_object* x_1659; 
x_1659 = lean_array_fget(x_10, x_1655);
x_1456 = x_1659;
goto block_1609;
}
}
}
block_1609:
{
lean_object* x_1457; 
lean_inc(x_13);
lean_inc(x_1456);
x_1457 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_1456, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_1457) == 0)
{
lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; uint8_t x_1461; 
x_1458 = lean_ctor_get(x_1457, 0);
lean_inc(x_1458);
x_1459 = lean_ctor_get(x_1457, 1);
lean_inc(x_1459);
lean_dec(x_1457);
x_1460 = lean_st_ref_get(x_13, x_1459);
x_1461 = !lean_is_exclusive(x_1460);
if (x_1461 == 0)
{
lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; 
x_1462 = lean_ctor_get(x_1460, 0);
x_1463 = lean_ctor_get(x_1460, 1);
x_1464 = lean_ctor_get(x_1462, 1);
lean_inc(x_1464);
lean_dec(x_1462);
x_1465 = lean_ctor_get(x_1464, 2);
lean_inc(x_1465);
lean_dec(x_1464);
x_1466 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_1465, x_1458);
if (lean_obj_tag(x_1466) == 0)
{
size_t x_1467; size_t x_1468; uint8_t x_1469; 
lean_free_object(x_1460);
x_1467 = lean_ptr_addr(x_1456);
lean_dec(x_1456);
x_1468 = lean_ptr_addr(x_1458);
x_1469 = lean_usize_dec_eq(x_1467, x_1468);
if (x_1469 == 0)
{
lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; uint8_t x_1488; lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; uint8_t x_1499; 
lean_dec(x_1);
x_1470 = lean_unsigned_to_nat(0u);
lean_inc(x_1458);
x_1471 = lean_array_set(x_10, x_1470, x_1458);
x_1472 = l_Lean_mkAppN(x_9, x_1471);
lean_dec(x_1471);
x_1473 = lean_st_ref_take(x_13, x_1463);
x_1474 = lean_ctor_get(x_1473, 0);
lean_inc(x_1474);
x_1475 = lean_ctor_get(x_1473, 1);
lean_inc(x_1475);
lean_dec(x_1473);
x_1476 = lean_ctor_get(x_1474, 0);
lean_inc(x_1476);
x_1477 = lean_ctor_get(x_1474, 1);
lean_inc(x_1477);
x_1478 = lean_ctor_get(x_1477, 0);
lean_inc(x_1478);
x_1479 = lean_ctor_get(x_1477, 1);
lean_inc(x_1479);
x_1480 = lean_ctor_get(x_1477, 2);
lean_inc(x_1480);
lean_dec(x_1477);
lean_inc(x_1472);
x_1481 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1480, x_1458, x_1472);
x_1482 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1482, 0, x_1478);
lean_ctor_set(x_1482, 1, x_1479);
lean_ctor_set(x_1482, 2, x_1481);
x_1483 = lean_ctor_get(x_1474, 2);
lean_inc(x_1483);
x_1484 = lean_ctor_get(x_1474, 3);
lean_inc(x_1484);
x_1485 = lean_ctor_get(x_1474, 4);
lean_inc(x_1485);
x_1486 = lean_ctor_get(x_1474, 5);
lean_inc(x_1486);
x_1487 = lean_ctor_get(x_1474, 6);
lean_inc(x_1487);
x_1488 = lean_ctor_get_uint8(x_1474, sizeof(void*)*15);
x_1489 = lean_ctor_get(x_1474, 7);
lean_inc(x_1489);
x_1490 = lean_ctor_get(x_1474, 8);
lean_inc(x_1490);
x_1491 = lean_ctor_get(x_1474, 9);
lean_inc(x_1491);
x_1492 = lean_ctor_get(x_1474, 10);
lean_inc(x_1492);
x_1493 = lean_ctor_get(x_1474, 11);
lean_inc(x_1493);
x_1494 = lean_ctor_get(x_1474, 12);
lean_inc(x_1494);
x_1495 = lean_ctor_get(x_1474, 13);
lean_inc(x_1495);
x_1496 = lean_ctor_get(x_1474, 14);
lean_inc(x_1496);
lean_dec(x_1474);
x_1497 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_1497, 0, x_1476);
lean_ctor_set(x_1497, 1, x_1482);
lean_ctor_set(x_1497, 2, x_1483);
lean_ctor_set(x_1497, 3, x_1484);
lean_ctor_set(x_1497, 4, x_1485);
lean_ctor_set(x_1497, 5, x_1486);
lean_ctor_set(x_1497, 6, x_1487);
lean_ctor_set(x_1497, 7, x_1489);
lean_ctor_set(x_1497, 8, x_1490);
lean_ctor_set(x_1497, 9, x_1491);
lean_ctor_set(x_1497, 10, x_1492);
lean_ctor_set(x_1497, 11, x_1493);
lean_ctor_set(x_1497, 12, x_1494);
lean_ctor_set(x_1497, 13, x_1495);
lean_ctor_set(x_1497, 14, x_1496);
lean_ctor_set_uint8(x_1497, sizeof(void*)*15, x_1488);
x_1498 = lean_st_ref_set(x_13, x_1497, x_1475);
lean_dec(x_13);
x_1499 = !lean_is_exclusive(x_1498);
if (x_1499 == 0)
{
lean_object* x_1500; 
x_1500 = lean_ctor_get(x_1498, 0);
lean_dec(x_1500);
lean_ctor_set(x_1498, 0, x_1472);
return x_1498;
}
else
{
lean_object* x_1501; lean_object* x_1502; 
x_1501 = lean_ctor_get(x_1498, 1);
lean_inc(x_1501);
lean_dec(x_1498);
x_1502 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1502, 0, x_1472);
lean_ctor_set(x_1502, 1, x_1501);
return x_1502;
}
}
else
{
lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; uint8_t x_1518; lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; uint8_t x_1529; 
lean_dec(x_10);
lean_dec(x_9);
x_1503 = lean_st_ref_take(x_13, x_1463);
x_1504 = lean_ctor_get(x_1503, 0);
lean_inc(x_1504);
x_1505 = lean_ctor_get(x_1503, 1);
lean_inc(x_1505);
lean_dec(x_1503);
x_1506 = lean_ctor_get(x_1504, 0);
lean_inc(x_1506);
x_1507 = lean_ctor_get(x_1504, 1);
lean_inc(x_1507);
x_1508 = lean_ctor_get(x_1507, 0);
lean_inc(x_1508);
x_1509 = lean_ctor_get(x_1507, 1);
lean_inc(x_1509);
x_1510 = lean_ctor_get(x_1507, 2);
lean_inc(x_1510);
lean_dec(x_1507);
lean_inc(x_1);
x_1511 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1510, x_1458, x_1);
x_1512 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1512, 0, x_1508);
lean_ctor_set(x_1512, 1, x_1509);
lean_ctor_set(x_1512, 2, x_1511);
x_1513 = lean_ctor_get(x_1504, 2);
lean_inc(x_1513);
x_1514 = lean_ctor_get(x_1504, 3);
lean_inc(x_1514);
x_1515 = lean_ctor_get(x_1504, 4);
lean_inc(x_1515);
x_1516 = lean_ctor_get(x_1504, 5);
lean_inc(x_1516);
x_1517 = lean_ctor_get(x_1504, 6);
lean_inc(x_1517);
x_1518 = lean_ctor_get_uint8(x_1504, sizeof(void*)*15);
x_1519 = lean_ctor_get(x_1504, 7);
lean_inc(x_1519);
x_1520 = lean_ctor_get(x_1504, 8);
lean_inc(x_1520);
x_1521 = lean_ctor_get(x_1504, 9);
lean_inc(x_1521);
x_1522 = lean_ctor_get(x_1504, 10);
lean_inc(x_1522);
x_1523 = lean_ctor_get(x_1504, 11);
lean_inc(x_1523);
x_1524 = lean_ctor_get(x_1504, 12);
lean_inc(x_1524);
x_1525 = lean_ctor_get(x_1504, 13);
lean_inc(x_1525);
x_1526 = lean_ctor_get(x_1504, 14);
lean_inc(x_1526);
lean_dec(x_1504);
x_1527 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_1527, 0, x_1506);
lean_ctor_set(x_1527, 1, x_1512);
lean_ctor_set(x_1527, 2, x_1513);
lean_ctor_set(x_1527, 3, x_1514);
lean_ctor_set(x_1527, 4, x_1515);
lean_ctor_set(x_1527, 5, x_1516);
lean_ctor_set(x_1527, 6, x_1517);
lean_ctor_set(x_1527, 7, x_1519);
lean_ctor_set(x_1527, 8, x_1520);
lean_ctor_set(x_1527, 9, x_1521);
lean_ctor_set(x_1527, 10, x_1522);
lean_ctor_set(x_1527, 11, x_1523);
lean_ctor_set(x_1527, 12, x_1524);
lean_ctor_set(x_1527, 13, x_1525);
lean_ctor_set(x_1527, 14, x_1526);
lean_ctor_set_uint8(x_1527, sizeof(void*)*15, x_1518);
x_1528 = lean_st_ref_set(x_13, x_1527, x_1505);
lean_dec(x_13);
x_1529 = !lean_is_exclusive(x_1528);
if (x_1529 == 0)
{
lean_object* x_1530; 
x_1530 = lean_ctor_get(x_1528, 0);
lean_dec(x_1530);
lean_ctor_set(x_1528, 0, x_1);
return x_1528;
}
else
{
lean_object* x_1531; lean_object* x_1532; 
x_1531 = lean_ctor_get(x_1528, 1);
lean_inc(x_1531);
lean_dec(x_1528);
x_1532 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1532, 0, x_1);
lean_ctor_set(x_1532, 1, x_1531);
return x_1532;
}
}
}
else
{
lean_object* x_1533; 
lean_dec(x_1458);
lean_dec(x_1456);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_1533 = lean_ctor_get(x_1466, 0);
lean_inc(x_1533);
lean_dec(x_1466);
lean_ctor_set(x_1460, 0, x_1533);
return x_1460;
}
}
else
{
lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; 
x_1534 = lean_ctor_get(x_1460, 0);
x_1535 = lean_ctor_get(x_1460, 1);
lean_inc(x_1535);
lean_inc(x_1534);
lean_dec(x_1460);
x_1536 = lean_ctor_get(x_1534, 1);
lean_inc(x_1536);
lean_dec(x_1534);
x_1537 = lean_ctor_get(x_1536, 2);
lean_inc(x_1537);
lean_dec(x_1536);
x_1538 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_1537, x_1458);
if (lean_obj_tag(x_1538) == 0)
{
size_t x_1539; size_t x_1540; uint8_t x_1541; 
x_1539 = lean_ptr_addr(x_1456);
lean_dec(x_1456);
x_1540 = lean_ptr_addr(x_1458);
x_1541 = lean_usize_dec_eq(x_1539, x_1540);
if (x_1541 == 0)
{
lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; uint8_t x_1560; lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; 
lean_dec(x_1);
x_1542 = lean_unsigned_to_nat(0u);
lean_inc(x_1458);
x_1543 = lean_array_set(x_10, x_1542, x_1458);
x_1544 = l_Lean_mkAppN(x_9, x_1543);
lean_dec(x_1543);
x_1545 = lean_st_ref_take(x_13, x_1535);
x_1546 = lean_ctor_get(x_1545, 0);
lean_inc(x_1546);
x_1547 = lean_ctor_get(x_1545, 1);
lean_inc(x_1547);
lean_dec(x_1545);
x_1548 = lean_ctor_get(x_1546, 0);
lean_inc(x_1548);
x_1549 = lean_ctor_get(x_1546, 1);
lean_inc(x_1549);
x_1550 = lean_ctor_get(x_1549, 0);
lean_inc(x_1550);
x_1551 = lean_ctor_get(x_1549, 1);
lean_inc(x_1551);
x_1552 = lean_ctor_get(x_1549, 2);
lean_inc(x_1552);
lean_dec(x_1549);
lean_inc(x_1544);
x_1553 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1552, x_1458, x_1544);
x_1554 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1554, 0, x_1550);
lean_ctor_set(x_1554, 1, x_1551);
lean_ctor_set(x_1554, 2, x_1553);
x_1555 = lean_ctor_get(x_1546, 2);
lean_inc(x_1555);
x_1556 = lean_ctor_get(x_1546, 3);
lean_inc(x_1556);
x_1557 = lean_ctor_get(x_1546, 4);
lean_inc(x_1557);
x_1558 = lean_ctor_get(x_1546, 5);
lean_inc(x_1558);
x_1559 = lean_ctor_get(x_1546, 6);
lean_inc(x_1559);
x_1560 = lean_ctor_get_uint8(x_1546, sizeof(void*)*15);
x_1561 = lean_ctor_get(x_1546, 7);
lean_inc(x_1561);
x_1562 = lean_ctor_get(x_1546, 8);
lean_inc(x_1562);
x_1563 = lean_ctor_get(x_1546, 9);
lean_inc(x_1563);
x_1564 = lean_ctor_get(x_1546, 10);
lean_inc(x_1564);
x_1565 = lean_ctor_get(x_1546, 11);
lean_inc(x_1565);
x_1566 = lean_ctor_get(x_1546, 12);
lean_inc(x_1566);
x_1567 = lean_ctor_get(x_1546, 13);
lean_inc(x_1567);
x_1568 = lean_ctor_get(x_1546, 14);
lean_inc(x_1568);
lean_dec(x_1546);
x_1569 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_1569, 0, x_1548);
lean_ctor_set(x_1569, 1, x_1554);
lean_ctor_set(x_1569, 2, x_1555);
lean_ctor_set(x_1569, 3, x_1556);
lean_ctor_set(x_1569, 4, x_1557);
lean_ctor_set(x_1569, 5, x_1558);
lean_ctor_set(x_1569, 6, x_1559);
lean_ctor_set(x_1569, 7, x_1561);
lean_ctor_set(x_1569, 8, x_1562);
lean_ctor_set(x_1569, 9, x_1563);
lean_ctor_set(x_1569, 10, x_1564);
lean_ctor_set(x_1569, 11, x_1565);
lean_ctor_set(x_1569, 12, x_1566);
lean_ctor_set(x_1569, 13, x_1567);
lean_ctor_set(x_1569, 14, x_1568);
lean_ctor_set_uint8(x_1569, sizeof(void*)*15, x_1560);
x_1570 = lean_st_ref_set(x_13, x_1569, x_1547);
lean_dec(x_13);
x_1571 = lean_ctor_get(x_1570, 1);
lean_inc(x_1571);
if (lean_is_exclusive(x_1570)) {
 lean_ctor_release(x_1570, 0);
 lean_ctor_release(x_1570, 1);
 x_1572 = x_1570;
} else {
 lean_dec_ref(x_1570);
 x_1572 = lean_box(0);
}
if (lean_is_scalar(x_1572)) {
 x_1573 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1573 = x_1572;
}
lean_ctor_set(x_1573, 0, x_1544);
lean_ctor_set(x_1573, 1, x_1571);
return x_1573;
}
else
{
lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; lean_object* x_1588; uint8_t x_1589; lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; 
lean_dec(x_10);
lean_dec(x_9);
x_1574 = lean_st_ref_take(x_13, x_1535);
x_1575 = lean_ctor_get(x_1574, 0);
lean_inc(x_1575);
x_1576 = lean_ctor_get(x_1574, 1);
lean_inc(x_1576);
lean_dec(x_1574);
x_1577 = lean_ctor_get(x_1575, 0);
lean_inc(x_1577);
x_1578 = lean_ctor_get(x_1575, 1);
lean_inc(x_1578);
x_1579 = lean_ctor_get(x_1578, 0);
lean_inc(x_1579);
x_1580 = lean_ctor_get(x_1578, 1);
lean_inc(x_1580);
x_1581 = lean_ctor_get(x_1578, 2);
lean_inc(x_1581);
lean_dec(x_1578);
lean_inc(x_1);
x_1582 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1581, x_1458, x_1);
x_1583 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1583, 0, x_1579);
lean_ctor_set(x_1583, 1, x_1580);
lean_ctor_set(x_1583, 2, x_1582);
x_1584 = lean_ctor_get(x_1575, 2);
lean_inc(x_1584);
x_1585 = lean_ctor_get(x_1575, 3);
lean_inc(x_1585);
x_1586 = lean_ctor_get(x_1575, 4);
lean_inc(x_1586);
x_1587 = lean_ctor_get(x_1575, 5);
lean_inc(x_1587);
x_1588 = lean_ctor_get(x_1575, 6);
lean_inc(x_1588);
x_1589 = lean_ctor_get_uint8(x_1575, sizeof(void*)*15);
x_1590 = lean_ctor_get(x_1575, 7);
lean_inc(x_1590);
x_1591 = lean_ctor_get(x_1575, 8);
lean_inc(x_1591);
x_1592 = lean_ctor_get(x_1575, 9);
lean_inc(x_1592);
x_1593 = lean_ctor_get(x_1575, 10);
lean_inc(x_1593);
x_1594 = lean_ctor_get(x_1575, 11);
lean_inc(x_1594);
x_1595 = lean_ctor_get(x_1575, 12);
lean_inc(x_1595);
x_1596 = lean_ctor_get(x_1575, 13);
lean_inc(x_1596);
x_1597 = lean_ctor_get(x_1575, 14);
lean_inc(x_1597);
lean_dec(x_1575);
x_1598 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_1598, 0, x_1577);
lean_ctor_set(x_1598, 1, x_1583);
lean_ctor_set(x_1598, 2, x_1584);
lean_ctor_set(x_1598, 3, x_1585);
lean_ctor_set(x_1598, 4, x_1586);
lean_ctor_set(x_1598, 5, x_1587);
lean_ctor_set(x_1598, 6, x_1588);
lean_ctor_set(x_1598, 7, x_1590);
lean_ctor_set(x_1598, 8, x_1591);
lean_ctor_set(x_1598, 9, x_1592);
lean_ctor_set(x_1598, 10, x_1593);
lean_ctor_set(x_1598, 11, x_1594);
lean_ctor_set(x_1598, 12, x_1595);
lean_ctor_set(x_1598, 13, x_1596);
lean_ctor_set(x_1598, 14, x_1597);
lean_ctor_set_uint8(x_1598, sizeof(void*)*15, x_1589);
x_1599 = lean_st_ref_set(x_13, x_1598, x_1576);
lean_dec(x_13);
x_1600 = lean_ctor_get(x_1599, 1);
lean_inc(x_1600);
if (lean_is_exclusive(x_1599)) {
 lean_ctor_release(x_1599, 0);
 lean_ctor_release(x_1599, 1);
 x_1601 = x_1599;
} else {
 lean_dec_ref(x_1599);
 x_1601 = lean_box(0);
}
if (lean_is_scalar(x_1601)) {
 x_1602 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1602 = x_1601;
}
lean_ctor_set(x_1602, 0, x_1);
lean_ctor_set(x_1602, 1, x_1600);
return x_1602;
}
}
else
{
lean_object* x_1603; lean_object* x_1604; 
lean_dec(x_1458);
lean_dec(x_1456);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_1603 = lean_ctor_get(x_1538, 0);
lean_inc(x_1603);
lean_dec(x_1538);
x_1604 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1604, 0, x_1603);
lean_ctor_set(x_1604, 1, x_1535);
return x_1604;
}
}
}
else
{
uint8_t x_1605; 
lean_dec(x_1456);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_1605 = !lean_is_exclusive(x_1457);
if (x_1605 == 0)
{
return x_1457;
}
else
{
lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; 
x_1606 = lean_ctor_get(x_1457, 0);
x_1607 = lean_ctor_get(x_1457, 1);
lean_inc(x_1607);
lean_inc(x_1606);
lean_dec(x_1457);
x_1608 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1608, 0, x_1606);
lean_ctor_set(x_1608, 1, x_1607);
return x_1608;
}
}
}
block_1647:
{
lean_object* x_1611; 
lean_dec(x_1610);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_9);
x_1611 = l_Lean_Meta_getFunInfo(x_9, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_1611) == 0)
{
lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; uint8_t x_1619; lean_object* x_1620; lean_object* x_1621; lean_object* x_1622; lean_object* x_1623; 
x_1612 = lean_ctor_get(x_1611, 0);
lean_inc(x_1612);
x_1613 = lean_ctor_get(x_1611, 1);
lean_inc(x_1613);
lean_dec(x_1611);
x_1614 = lean_ctor_get(x_1612, 0);
lean_inc(x_1614);
lean_dec(x_1612);
x_1615 = lean_array_get_size(x_10);
x_1616 = lean_unsigned_to_nat(0u);
x_1617 = lean_unsigned_to_nat(1u);
lean_inc(x_1615);
x_1618 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1618, 0, x_1616);
lean_ctor_set(x_1618, 1, x_1615);
lean_ctor_set(x_1618, 2, x_1617);
x_1619 = 0;
x_1620 = lean_box(x_1619);
lean_inc(x_10);
x_1621 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1621, 0, x_10);
lean_ctor_set(x_1621, 1, x_1620);
x_1622 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_1618);
lean_inc(x_9);
lean_inc(x_1);
x_1623 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1622, x_1614, x_1615, x_1618, x_1618, x_1621, x_1616, lean_box(0), lean_box(0), x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_1613);
if (lean_obj_tag(x_1623) == 0)
{
lean_object* x_1624; lean_object* x_1625; uint8_t x_1626; 
x_1624 = lean_ctor_get(x_1623, 0);
lean_inc(x_1624);
x_1625 = lean_ctor_get(x_1624, 1);
lean_inc(x_1625);
x_1626 = lean_unbox(x_1625);
lean_dec(x_1625);
if (x_1626 == 0)
{
uint8_t x_1627; 
lean_dec(x_1624);
lean_dec(x_9);
x_1627 = !lean_is_exclusive(x_1623);
if (x_1627 == 0)
{
lean_object* x_1628; 
x_1628 = lean_ctor_get(x_1623, 0);
lean_dec(x_1628);
lean_ctor_set(x_1623, 0, x_1);
return x_1623;
}
else
{
lean_object* x_1629; lean_object* x_1630; 
x_1629 = lean_ctor_get(x_1623, 1);
lean_inc(x_1629);
lean_dec(x_1623);
x_1630 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1630, 0, x_1);
lean_ctor_set(x_1630, 1, x_1629);
return x_1630;
}
}
else
{
uint8_t x_1631; 
lean_dec(x_1);
x_1631 = !lean_is_exclusive(x_1623);
if (x_1631 == 0)
{
lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; 
x_1632 = lean_ctor_get(x_1623, 0);
lean_dec(x_1632);
x_1633 = lean_ctor_get(x_1624, 0);
lean_inc(x_1633);
lean_dec(x_1624);
x_1634 = l_Lean_mkAppN(x_9, x_1633);
lean_dec(x_1633);
lean_ctor_set(x_1623, 0, x_1634);
return x_1623;
}
else
{
lean_object* x_1635; lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; 
x_1635 = lean_ctor_get(x_1623, 1);
lean_inc(x_1635);
lean_dec(x_1623);
x_1636 = lean_ctor_get(x_1624, 0);
lean_inc(x_1636);
lean_dec(x_1624);
x_1637 = l_Lean_mkAppN(x_9, x_1636);
lean_dec(x_1636);
x_1638 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1638, 0, x_1637);
lean_ctor_set(x_1638, 1, x_1635);
return x_1638;
}
}
}
else
{
uint8_t x_1639; 
lean_dec(x_9);
lean_dec(x_1);
x_1639 = !lean_is_exclusive(x_1623);
if (x_1639 == 0)
{
return x_1623;
}
else
{
lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; 
x_1640 = lean_ctor_get(x_1623, 0);
x_1641 = lean_ctor_get(x_1623, 1);
lean_inc(x_1641);
lean_inc(x_1640);
lean_dec(x_1623);
x_1642 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1642, 0, x_1640);
lean_ctor_set(x_1642, 1, x_1641);
return x_1642;
}
}
}
else
{
uint8_t x_1643; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1643 = !lean_is_exclusive(x_1611);
if (x_1643 == 0)
{
return x_1611;
}
else
{
lean_object* x_1644; lean_object* x_1645; lean_object* x_1646; 
x_1644 = lean_ctor_get(x_1611, 0);
x_1645 = lean_ctor_get(x_1611, 1);
lean_inc(x_1645);
lean_inc(x_1644);
lean_dec(x_1611);
x_1646 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1646, 0, x_1644);
lean_ctor_set(x_1646, 1, x_1645);
return x_1646;
}
}
}
}
case 9:
{
lean_object* x_1660; lean_object* x_1814; lean_object* x_1852; uint8_t x_1853; 
lean_dec(x_11);
x_1852 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_1853 = l_Lean_Expr_isConstOf(x_9, x_1852);
if (x_1853 == 0)
{
lean_object* x_1854; 
x_1854 = lean_box(0);
x_1814 = x_1854;
goto block_1851;
}
else
{
lean_object* x_1855; lean_object* x_1856; uint8_t x_1857; 
x_1855 = lean_array_get_size(x_10);
x_1856 = lean_unsigned_to_nat(2u);
x_1857 = lean_nat_dec_eq(x_1855, x_1856);
if (x_1857 == 0)
{
lean_object* x_1858; 
lean_dec(x_1855);
x_1858 = lean_box(0);
x_1814 = x_1858;
goto block_1851;
}
else
{
lean_object* x_1859; uint8_t x_1860; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1859 = lean_unsigned_to_nat(0u);
x_1860 = lean_nat_dec_lt(x_1859, x_1855);
lean_dec(x_1855);
if (x_1860 == 0)
{
lean_object* x_1861; lean_object* x_1862; 
x_1861 = l_Lean_instInhabitedExpr;
x_1862 = l_outOfBounds___rarg(x_1861);
x_1660 = x_1862;
goto block_1813;
}
else
{
lean_object* x_1863; 
x_1863 = lean_array_fget(x_10, x_1859);
x_1660 = x_1863;
goto block_1813;
}
}
}
block_1813:
{
lean_object* x_1661; 
lean_inc(x_13);
lean_inc(x_1660);
x_1661 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_1660, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_1661) == 0)
{
lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; uint8_t x_1665; 
x_1662 = lean_ctor_get(x_1661, 0);
lean_inc(x_1662);
x_1663 = lean_ctor_get(x_1661, 1);
lean_inc(x_1663);
lean_dec(x_1661);
x_1664 = lean_st_ref_get(x_13, x_1663);
x_1665 = !lean_is_exclusive(x_1664);
if (x_1665 == 0)
{
lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; 
x_1666 = lean_ctor_get(x_1664, 0);
x_1667 = lean_ctor_get(x_1664, 1);
x_1668 = lean_ctor_get(x_1666, 1);
lean_inc(x_1668);
lean_dec(x_1666);
x_1669 = lean_ctor_get(x_1668, 2);
lean_inc(x_1669);
lean_dec(x_1668);
x_1670 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_1669, x_1662);
if (lean_obj_tag(x_1670) == 0)
{
size_t x_1671; size_t x_1672; uint8_t x_1673; 
lean_free_object(x_1664);
x_1671 = lean_ptr_addr(x_1660);
lean_dec(x_1660);
x_1672 = lean_ptr_addr(x_1662);
x_1673 = lean_usize_dec_eq(x_1671, x_1672);
if (x_1673 == 0)
{
lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; lean_object* x_1677; lean_object* x_1678; lean_object* x_1679; lean_object* x_1680; lean_object* x_1681; lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; lean_object* x_1690; lean_object* x_1691; uint8_t x_1692; lean_object* x_1693; lean_object* x_1694; lean_object* x_1695; lean_object* x_1696; lean_object* x_1697; lean_object* x_1698; lean_object* x_1699; lean_object* x_1700; lean_object* x_1701; lean_object* x_1702; uint8_t x_1703; 
lean_dec(x_1);
x_1674 = lean_unsigned_to_nat(0u);
lean_inc(x_1662);
x_1675 = lean_array_set(x_10, x_1674, x_1662);
x_1676 = l_Lean_mkAppN(x_9, x_1675);
lean_dec(x_1675);
x_1677 = lean_st_ref_take(x_13, x_1667);
x_1678 = lean_ctor_get(x_1677, 0);
lean_inc(x_1678);
x_1679 = lean_ctor_get(x_1677, 1);
lean_inc(x_1679);
lean_dec(x_1677);
x_1680 = lean_ctor_get(x_1678, 0);
lean_inc(x_1680);
x_1681 = lean_ctor_get(x_1678, 1);
lean_inc(x_1681);
x_1682 = lean_ctor_get(x_1681, 0);
lean_inc(x_1682);
x_1683 = lean_ctor_get(x_1681, 1);
lean_inc(x_1683);
x_1684 = lean_ctor_get(x_1681, 2);
lean_inc(x_1684);
lean_dec(x_1681);
lean_inc(x_1676);
x_1685 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1684, x_1662, x_1676);
x_1686 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1686, 0, x_1682);
lean_ctor_set(x_1686, 1, x_1683);
lean_ctor_set(x_1686, 2, x_1685);
x_1687 = lean_ctor_get(x_1678, 2);
lean_inc(x_1687);
x_1688 = lean_ctor_get(x_1678, 3);
lean_inc(x_1688);
x_1689 = lean_ctor_get(x_1678, 4);
lean_inc(x_1689);
x_1690 = lean_ctor_get(x_1678, 5);
lean_inc(x_1690);
x_1691 = lean_ctor_get(x_1678, 6);
lean_inc(x_1691);
x_1692 = lean_ctor_get_uint8(x_1678, sizeof(void*)*15);
x_1693 = lean_ctor_get(x_1678, 7);
lean_inc(x_1693);
x_1694 = lean_ctor_get(x_1678, 8);
lean_inc(x_1694);
x_1695 = lean_ctor_get(x_1678, 9);
lean_inc(x_1695);
x_1696 = lean_ctor_get(x_1678, 10);
lean_inc(x_1696);
x_1697 = lean_ctor_get(x_1678, 11);
lean_inc(x_1697);
x_1698 = lean_ctor_get(x_1678, 12);
lean_inc(x_1698);
x_1699 = lean_ctor_get(x_1678, 13);
lean_inc(x_1699);
x_1700 = lean_ctor_get(x_1678, 14);
lean_inc(x_1700);
lean_dec(x_1678);
x_1701 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_1701, 0, x_1680);
lean_ctor_set(x_1701, 1, x_1686);
lean_ctor_set(x_1701, 2, x_1687);
lean_ctor_set(x_1701, 3, x_1688);
lean_ctor_set(x_1701, 4, x_1689);
lean_ctor_set(x_1701, 5, x_1690);
lean_ctor_set(x_1701, 6, x_1691);
lean_ctor_set(x_1701, 7, x_1693);
lean_ctor_set(x_1701, 8, x_1694);
lean_ctor_set(x_1701, 9, x_1695);
lean_ctor_set(x_1701, 10, x_1696);
lean_ctor_set(x_1701, 11, x_1697);
lean_ctor_set(x_1701, 12, x_1698);
lean_ctor_set(x_1701, 13, x_1699);
lean_ctor_set(x_1701, 14, x_1700);
lean_ctor_set_uint8(x_1701, sizeof(void*)*15, x_1692);
x_1702 = lean_st_ref_set(x_13, x_1701, x_1679);
lean_dec(x_13);
x_1703 = !lean_is_exclusive(x_1702);
if (x_1703 == 0)
{
lean_object* x_1704; 
x_1704 = lean_ctor_get(x_1702, 0);
lean_dec(x_1704);
lean_ctor_set(x_1702, 0, x_1676);
return x_1702;
}
else
{
lean_object* x_1705; lean_object* x_1706; 
x_1705 = lean_ctor_get(x_1702, 1);
lean_inc(x_1705);
lean_dec(x_1702);
x_1706 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1706, 0, x_1676);
lean_ctor_set(x_1706, 1, x_1705);
return x_1706;
}
}
else
{
lean_object* x_1707; lean_object* x_1708; lean_object* x_1709; lean_object* x_1710; lean_object* x_1711; lean_object* x_1712; lean_object* x_1713; lean_object* x_1714; lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; lean_object* x_1719; lean_object* x_1720; lean_object* x_1721; uint8_t x_1722; lean_object* x_1723; lean_object* x_1724; lean_object* x_1725; lean_object* x_1726; lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; lean_object* x_1730; lean_object* x_1731; lean_object* x_1732; uint8_t x_1733; 
lean_dec(x_10);
lean_dec(x_9);
x_1707 = lean_st_ref_take(x_13, x_1667);
x_1708 = lean_ctor_get(x_1707, 0);
lean_inc(x_1708);
x_1709 = lean_ctor_get(x_1707, 1);
lean_inc(x_1709);
lean_dec(x_1707);
x_1710 = lean_ctor_get(x_1708, 0);
lean_inc(x_1710);
x_1711 = lean_ctor_get(x_1708, 1);
lean_inc(x_1711);
x_1712 = lean_ctor_get(x_1711, 0);
lean_inc(x_1712);
x_1713 = lean_ctor_get(x_1711, 1);
lean_inc(x_1713);
x_1714 = lean_ctor_get(x_1711, 2);
lean_inc(x_1714);
lean_dec(x_1711);
lean_inc(x_1);
x_1715 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1714, x_1662, x_1);
x_1716 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1716, 0, x_1712);
lean_ctor_set(x_1716, 1, x_1713);
lean_ctor_set(x_1716, 2, x_1715);
x_1717 = lean_ctor_get(x_1708, 2);
lean_inc(x_1717);
x_1718 = lean_ctor_get(x_1708, 3);
lean_inc(x_1718);
x_1719 = lean_ctor_get(x_1708, 4);
lean_inc(x_1719);
x_1720 = lean_ctor_get(x_1708, 5);
lean_inc(x_1720);
x_1721 = lean_ctor_get(x_1708, 6);
lean_inc(x_1721);
x_1722 = lean_ctor_get_uint8(x_1708, sizeof(void*)*15);
x_1723 = lean_ctor_get(x_1708, 7);
lean_inc(x_1723);
x_1724 = lean_ctor_get(x_1708, 8);
lean_inc(x_1724);
x_1725 = lean_ctor_get(x_1708, 9);
lean_inc(x_1725);
x_1726 = lean_ctor_get(x_1708, 10);
lean_inc(x_1726);
x_1727 = lean_ctor_get(x_1708, 11);
lean_inc(x_1727);
x_1728 = lean_ctor_get(x_1708, 12);
lean_inc(x_1728);
x_1729 = lean_ctor_get(x_1708, 13);
lean_inc(x_1729);
x_1730 = lean_ctor_get(x_1708, 14);
lean_inc(x_1730);
lean_dec(x_1708);
x_1731 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_1731, 0, x_1710);
lean_ctor_set(x_1731, 1, x_1716);
lean_ctor_set(x_1731, 2, x_1717);
lean_ctor_set(x_1731, 3, x_1718);
lean_ctor_set(x_1731, 4, x_1719);
lean_ctor_set(x_1731, 5, x_1720);
lean_ctor_set(x_1731, 6, x_1721);
lean_ctor_set(x_1731, 7, x_1723);
lean_ctor_set(x_1731, 8, x_1724);
lean_ctor_set(x_1731, 9, x_1725);
lean_ctor_set(x_1731, 10, x_1726);
lean_ctor_set(x_1731, 11, x_1727);
lean_ctor_set(x_1731, 12, x_1728);
lean_ctor_set(x_1731, 13, x_1729);
lean_ctor_set(x_1731, 14, x_1730);
lean_ctor_set_uint8(x_1731, sizeof(void*)*15, x_1722);
x_1732 = lean_st_ref_set(x_13, x_1731, x_1709);
lean_dec(x_13);
x_1733 = !lean_is_exclusive(x_1732);
if (x_1733 == 0)
{
lean_object* x_1734; 
x_1734 = lean_ctor_get(x_1732, 0);
lean_dec(x_1734);
lean_ctor_set(x_1732, 0, x_1);
return x_1732;
}
else
{
lean_object* x_1735; lean_object* x_1736; 
x_1735 = lean_ctor_get(x_1732, 1);
lean_inc(x_1735);
lean_dec(x_1732);
x_1736 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1736, 0, x_1);
lean_ctor_set(x_1736, 1, x_1735);
return x_1736;
}
}
}
else
{
lean_object* x_1737; 
lean_dec(x_1662);
lean_dec(x_1660);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_1737 = lean_ctor_get(x_1670, 0);
lean_inc(x_1737);
lean_dec(x_1670);
lean_ctor_set(x_1664, 0, x_1737);
return x_1664;
}
}
else
{
lean_object* x_1738; lean_object* x_1739; lean_object* x_1740; lean_object* x_1741; lean_object* x_1742; 
x_1738 = lean_ctor_get(x_1664, 0);
x_1739 = lean_ctor_get(x_1664, 1);
lean_inc(x_1739);
lean_inc(x_1738);
lean_dec(x_1664);
x_1740 = lean_ctor_get(x_1738, 1);
lean_inc(x_1740);
lean_dec(x_1738);
x_1741 = lean_ctor_get(x_1740, 2);
lean_inc(x_1741);
lean_dec(x_1740);
x_1742 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_1741, x_1662);
if (lean_obj_tag(x_1742) == 0)
{
size_t x_1743; size_t x_1744; uint8_t x_1745; 
x_1743 = lean_ptr_addr(x_1660);
lean_dec(x_1660);
x_1744 = lean_ptr_addr(x_1662);
x_1745 = lean_usize_dec_eq(x_1743, x_1744);
if (x_1745 == 0)
{
lean_object* x_1746; lean_object* x_1747; lean_object* x_1748; lean_object* x_1749; lean_object* x_1750; lean_object* x_1751; lean_object* x_1752; lean_object* x_1753; lean_object* x_1754; lean_object* x_1755; lean_object* x_1756; lean_object* x_1757; lean_object* x_1758; lean_object* x_1759; lean_object* x_1760; lean_object* x_1761; lean_object* x_1762; lean_object* x_1763; uint8_t x_1764; lean_object* x_1765; lean_object* x_1766; lean_object* x_1767; lean_object* x_1768; lean_object* x_1769; lean_object* x_1770; lean_object* x_1771; lean_object* x_1772; lean_object* x_1773; lean_object* x_1774; lean_object* x_1775; lean_object* x_1776; lean_object* x_1777; 
lean_dec(x_1);
x_1746 = lean_unsigned_to_nat(0u);
lean_inc(x_1662);
x_1747 = lean_array_set(x_10, x_1746, x_1662);
x_1748 = l_Lean_mkAppN(x_9, x_1747);
lean_dec(x_1747);
x_1749 = lean_st_ref_take(x_13, x_1739);
x_1750 = lean_ctor_get(x_1749, 0);
lean_inc(x_1750);
x_1751 = lean_ctor_get(x_1749, 1);
lean_inc(x_1751);
lean_dec(x_1749);
x_1752 = lean_ctor_get(x_1750, 0);
lean_inc(x_1752);
x_1753 = lean_ctor_get(x_1750, 1);
lean_inc(x_1753);
x_1754 = lean_ctor_get(x_1753, 0);
lean_inc(x_1754);
x_1755 = lean_ctor_get(x_1753, 1);
lean_inc(x_1755);
x_1756 = lean_ctor_get(x_1753, 2);
lean_inc(x_1756);
lean_dec(x_1753);
lean_inc(x_1748);
x_1757 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1756, x_1662, x_1748);
x_1758 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1758, 0, x_1754);
lean_ctor_set(x_1758, 1, x_1755);
lean_ctor_set(x_1758, 2, x_1757);
x_1759 = lean_ctor_get(x_1750, 2);
lean_inc(x_1759);
x_1760 = lean_ctor_get(x_1750, 3);
lean_inc(x_1760);
x_1761 = lean_ctor_get(x_1750, 4);
lean_inc(x_1761);
x_1762 = lean_ctor_get(x_1750, 5);
lean_inc(x_1762);
x_1763 = lean_ctor_get(x_1750, 6);
lean_inc(x_1763);
x_1764 = lean_ctor_get_uint8(x_1750, sizeof(void*)*15);
x_1765 = lean_ctor_get(x_1750, 7);
lean_inc(x_1765);
x_1766 = lean_ctor_get(x_1750, 8);
lean_inc(x_1766);
x_1767 = lean_ctor_get(x_1750, 9);
lean_inc(x_1767);
x_1768 = lean_ctor_get(x_1750, 10);
lean_inc(x_1768);
x_1769 = lean_ctor_get(x_1750, 11);
lean_inc(x_1769);
x_1770 = lean_ctor_get(x_1750, 12);
lean_inc(x_1770);
x_1771 = lean_ctor_get(x_1750, 13);
lean_inc(x_1771);
x_1772 = lean_ctor_get(x_1750, 14);
lean_inc(x_1772);
lean_dec(x_1750);
x_1773 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_1773, 0, x_1752);
lean_ctor_set(x_1773, 1, x_1758);
lean_ctor_set(x_1773, 2, x_1759);
lean_ctor_set(x_1773, 3, x_1760);
lean_ctor_set(x_1773, 4, x_1761);
lean_ctor_set(x_1773, 5, x_1762);
lean_ctor_set(x_1773, 6, x_1763);
lean_ctor_set(x_1773, 7, x_1765);
lean_ctor_set(x_1773, 8, x_1766);
lean_ctor_set(x_1773, 9, x_1767);
lean_ctor_set(x_1773, 10, x_1768);
lean_ctor_set(x_1773, 11, x_1769);
lean_ctor_set(x_1773, 12, x_1770);
lean_ctor_set(x_1773, 13, x_1771);
lean_ctor_set(x_1773, 14, x_1772);
lean_ctor_set_uint8(x_1773, sizeof(void*)*15, x_1764);
x_1774 = lean_st_ref_set(x_13, x_1773, x_1751);
lean_dec(x_13);
x_1775 = lean_ctor_get(x_1774, 1);
lean_inc(x_1775);
if (lean_is_exclusive(x_1774)) {
 lean_ctor_release(x_1774, 0);
 lean_ctor_release(x_1774, 1);
 x_1776 = x_1774;
} else {
 lean_dec_ref(x_1774);
 x_1776 = lean_box(0);
}
if (lean_is_scalar(x_1776)) {
 x_1777 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1777 = x_1776;
}
lean_ctor_set(x_1777, 0, x_1748);
lean_ctor_set(x_1777, 1, x_1775);
return x_1777;
}
else
{
lean_object* x_1778; lean_object* x_1779; lean_object* x_1780; lean_object* x_1781; lean_object* x_1782; lean_object* x_1783; lean_object* x_1784; lean_object* x_1785; lean_object* x_1786; lean_object* x_1787; lean_object* x_1788; lean_object* x_1789; lean_object* x_1790; lean_object* x_1791; lean_object* x_1792; uint8_t x_1793; lean_object* x_1794; lean_object* x_1795; lean_object* x_1796; lean_object* x_1797; lean_object* x_1798; lean_object* x_1799; lean_object* x_1800; lean_object* x_1801; lean_object* x_1802; lean_object* x_1803; lean_object* x_1804; lean_object* x_1805; lean_object* x_1806; 
lean_dec(x_10);
lean_dec(x_9);
x_1778 = lean_st_ref_take(x_13, x_1739);
x_1779 = lean_ctor_get(x_1778, 0);
lean_inc(x_1779);
x_1780 = lean_ctor_get(x_1778, 1);
lean_inc(x_1780);
lean_dec(x_1778);
x_1781 = lean_ctor_get(x_1779, 0);
lean_inc(x_1781);
x_1782 = lean_ctor_get(x_1779, 1);
lean_inc(x_1782);
x_1783 = lean_ctor_get(x_1782, 0);
lean_inc(x_1783);
x_1784 = lean_ctor_get(x_1782, 1);
lean_inc(x_1784);
x_1785 = lean_ctor_get(x_1782, 2);
lean_inc(x_1785);
lean_dec(x_1782);
lean_inc(x_1);
x_1786 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1785, x_1662, x_1);
x_1787 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1787, 0, x_1783);
lean_ctor_set(x_1787, 1, x_1784);
lean_ctor_set(x_1787, 2, x_1786);
x_1788 = lean_ctor_get(x_1779, 2);
lean_inc(x_1788);
x_1789 = lean_ctor_get(x_1779, 3);
lean_inc(x_1789);
x_1790 = lean_ctor_get(x_1779, 4);
lean_inc(x_1790);
x_1791 = lean_ctor_get(x_1779, 5);
lean_inc(x_1791);
x_1792 = lean_ctor_get(x_1779, 6);
lean_inc(x_1792);
x_1793 = lean_ctor_get_uint8(x_1779, sizeof(void*)*15);
x_1794 = lean_ctor_get(x_1779, 7);
lean_inc(x_1794);
x_1795 = lean_ctor_get(x_1779, 8);
lean_inc(x_1795);
x_1796 = lean_ctor_get(x_1779, 9);
lean_inc(x_1796);
x_1797 = lean_ctor_get(x_1779, 10);
lean_inc(x_1797);
x_1798 = lean_ctor_get(x_1779, 11);
lean_inc(x_1798);
x_1799 = lean_ctor_get(x_1779, 12);
lean_inc(x_1799);
x_1800 = lean_ctor_get(x_1779, 13);
lean_inc(x_1800);
x_1801 = lean_ctor_get(x_1779, 14);
lean_inc(x_1801);
lean_dec(x_1779);
x_1802 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_1802, 0, x_1781);
lean_ctor_set(x_1802, 1, x_1787);
lean_ctor_set(x_1802, 2, x_1788);
lean_ctor_set(x_1802, 3, x_1789);
lean_ctor_set(x_1802, 4, x_1790);
lean_ctor_set(x_1802, 5, x_1791);
lean_ctor_set(x_1802, 6, x_1792);
lean_ctor_set(x_1802, 7, x_1794);
lean_ctor_set(x_1802, 8, x_1795);
lean_ctor_set(x_1802, 9, x_1796);
lean_ctor_set(x_1802, 10, x_1797);
lean_ctor_set(x_1802, 11, x_1798);
lean_ctor_set(x_1802, 12, x_1799);
lean_ctor_set(x_1802, 13, x_1800);
lean_ctor_set(x_1802, 14, x_1801);
lean_ctor_set_uint8(x_1802, sizeof(void*)*15, x_1793);
x_1803 = lean_st_ref_set(x_13, x_1802, x_1780);
lean_dec(x_13);
x_1804 = lean_ctor_get(x_1803, 1);
lean_inc(x_1804);
if (lean_is_exclusive(x_1803)) {
 lean_ctor_release(x_1803, 0);
 lean_ctor_release(x_1803, 1);
 x_1805 = x_1803;
} else {
 lean_dec_ref(x_1803);
 x_1805 = lean_box(0);
}
if (lean_is_scalar(x_1805)) {
 x_1806 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1806 = x_1805;
}
lean_ctor_set(x_1806, 0, x_1);
lean_ctor_set(x_1806, 1, x_1804);
return x_1806;
}
}
else
{
lean_object* x_1807; lean_object* x_1808; 
lean_dec(x_1662);
lean_dec(x_1660);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_1807 = lean_ctor_get(x_1742, 0);
lean_inc(x_1807);
lean_dec(x_1742);
x_1808 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1808, 0, x_1807);
lean_ctor_set(x_1808, 1, x_1739);
return x_1808;
}
}
}
else
{
uint8_t x_1809; 
lean_dec(x_1660);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_1809 = !lean_is_exclusive(x_1661);
if (x_1809 == 0)
{
return x_1661;
}
else
{
lean_object* x_1810; lean_object* x_1811; lean_object* x_1812; 
x_1810 = lean_ctor_get(x_1661, 0);
x_1811 = lean_ctor_get(x_1661, 1);
lean_inc(x_1811);
lean_inc(x_1810);
lean_dec(x_1661);
x_1812 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1812, 0, x_1810);
lean_ctor_set(x_1812, 1, x_1811);
return x_1812;
}
}
}
block_1851:
{
lean_object* x_1815; 
lean_dec(x_1814);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_9);
x_1815 = l_Lean_Meta_getFunInfo(x_9, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_1815) == 0)
{
lean_object* x_1816; lean_object* x_1817; lean_object* x_1818; lean_object* x_1819; lean_object* x_1820; lean_object* x_1821; lean_object* x_1822; uint8_t x_1823; lean_object* x_1824; lean_object* x_1825; lean_object* x_1826; lean_object* x_1827; 
x_1816 = lean_ctor_get(x_1815, 0);
lean_inc(x_1816);
x_1817 = lean_ctor_get(x_1815, 1);
lean_inc(x_1817);
lean_dec(x_1815);
x_1818 = lean_ctor_get(x_1816, 0);
lean_inc(x_1818);
lean_dec(x_1816);
x_1819 = lean_array_get_size(x_10);
x_1820 = lean_unsigned_to_nat(0u);
x_1821 = lean_unsigned_to_nat(1u);
lean_inc(x_1819);
x_1822 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1822, 0, x_1820);
lean_ctor_set(x_1822, 1, x_1819);
lean_ctor_set(x_1822, 2, x_1821);
x_1823 = 0;
x_1824 = lean_box(x_1823);
lean_inc(x_10);
x_1825 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1825, 0, x_10);
lean_ctor_set(x_1825, 1, x_1824);
x_1826 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_1822);
lean_inc(x_9);
lean_inc(x_1);
x_1827 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1826, x_1818, x_1819, x_1822, x_1822, x_1825, x_1820, lean_box(0), lean_box(0), x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_1817);
if (lean_obj_tag(x_1827) == 0)
{
lean_object* x_1828; lean_object* x_1829; uint8_t x_1830; 
x_1828 = lean_ctor_get(x_1827, 0);
lean_inc(x_1828);
x_1829 = lean_ctor_get(x_1828, 1);
lean_inc(x_1829);
x_1830 = lean_unbox(x_1829);
lean_dec(x_1829);
if (x_1830 == 0)
{
uint8_t x_1831; 
lean_dec(x_1828);
lean_dec(x_9);
x_1831 = !lean_is_exclusive(x_1827);
if (x_1831 == 0)
{
lean_object* x_1832; 
x_1832 = lean_ctor_get(x_1827, 0);
lean_dec(x_1832);
lean_ctor_set(x_1827, 0, x_1);
return x_1827;
}
else
{
lean_object* x_1833; lean_object* x_1834; 
x_1833 = lean_ctor_get(x_1827, 1);
lean_inc(x_1833);
lean_dec(x_1827);
x_1834 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1834, 0, x_1);
lean_ctor_set(x_1834, 1, x_1833);
return x_1834;
}
}
else
{
uint8_t x_1835; 
lean_dec(x_1);
x_1835 = !lean_is_exclusive(x_1827);
if (x_1835 == 0)
{
lean_object* x_1836; lean_object* x_1837; lean_object* x_1838; 
x_1836 = lean_ctor_get(x_1827, 0);
lean_dec(x_1836);
x_1837 = lean_ctor_get(x_1828, 0);
lean_inc(x_1837);
lean_dec(x_1828);
x_1838 = l_Lean_mkAppN(x_9, x_1837);
lean_dec(x_1837);
lean_ctor_set(x_1827, 0, x_1838);
return x_1827;
}
else
{
lean_object* x_1839; lean_object* x_1840; lean_object* x_1841; lean_object* x_1842; 
x_1839 = lean_ctor_get(x_1827, 1);
lean_inc(x_1839);
lean_dec(x_1827);
x_1840 = lean_ctor_get(x_1828, 0);
lean_inc(x_1840);
lean_dec(x_1828);
x_1841 = l_Lean_mkAppN(x_9, x_1840);
lean_dec(x_1840);
x_1842 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1842, 0, x_1841);
lean_ctor_set(x_1842, 1, x_1839);
return x_1842;
}
}
}
else
{
uint8_t x_1843; 
lean_dec(x_9);
lean_dec(x_1);
x_1843 = !lean_is_exclusive(x_1827);
if (x_1843 == 0)
{
return x_1827;
}
else
{
lean_object* x_1844; lean_object* x_1845; lean_object* x_1846; 
x_1844 = lean_ctor_get(x_1827, 0);
x_1845 = lean_ctor_get(x_1827, 1);
lean_inc(x_1845);
lean_inc(x_1844);
lean_dec(x_1827);
x_1846 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1846, 0, x_1844);
lean_ctor_set(x_1846, 1, x_1845);
return x_1846;
}
}
}
else
{
uint8_t x_1847; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1847 = !lean_is_exclusive(x_1815);
if (x_1847 == 0)
{
return x_1815;
}
else
{
lean_object* x_1848; lean_object* x_1849; lean_object* x_1850; 
x_1848 = lean_ctor_get(x_1815, 0);
x_1849 = lean_ctor_get(x_1815, 1);
lean_inc(x_1849);
lean_inc(x_1848);
lean_dec(x_1815);
x_1850 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1850, 0, x_1848);
lean_ctor_set(x_1850, 1, x_1849);
return x_1850;
}
}
}
}
case 10:
{
lean_object* x_1864; lean_object* x_2018; lean_object* x_2056; uint8_t x_2057; 
lean_dec(x_11);
x_2056 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_2057 = l_Lean_Expr_isConstOf(x_9, x_2056);
if (x_2057 == 0)
{
lean_object* x_2058; 
x_2058 = lean_box(0);
x_2018 = x_2058;
goto block_2055;
}
else
{
lean_object* x_2059; lean_object* x_2060; uint8_t x_2061; 
x_2059 = lean_array_get_size(x_10);
x_2060 = lean_unsigned_to_nat(2u);
x_2061 = lean_nat_dec_eq(x_2059, x_2060);
if (x_2061 == 0)
{
lean_object* x_2062; 
lean_dec(x_2059);
x_2062 = lean_box(0);
x_2018 = x_2062;
goto block_2055;
}
else
{
lean_object* x_2063; uint8_t x_2064; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2063 = lean_unsigned_to_nat(0u);
x_2064 = lean_nat_dec_lt(x_2063, x_2059);
lean_dec(x_2059);
if (x_2064 == 0)
{
lean_object* x_2065; lean_object* x_2066; 
x_2065 = l_Lean_instInhabitedExpr;
x_2066 = l_outOfBounds___rarg(x_2065);
x_1864 = x_2066;
goto block_2017;
}
else
{
lean_object* x_2067; 
x_2067 = lean_array_fget(x_10, x_2063);
x_1864 = x_2067;
goto block_2017;
}
}
}
block_2017:
{
lean_object* x_1865; 
lean_inc(x_13);
lean_inc(x_1864);
x_1865 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_1864, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_1865) == 0)
{
lean_object* x_1866; lean_object* x_1867; lean_object* x_1868; uint8_t x_1869; 
x_1866 = lean_ctor_get(x_1865, 0);
lean_inc(x_1866);
x_1867 = lean_ctor_get(x_1865, 1);
lean_inc(x_1867);
lean_dec(x_1865);
x_1868 = lean_st_ref_get(x_13, x_1867);
x_1869 = !lean_is_exclusive(x_1868);
if (x_1869 == 0)
{
lean_object* x_1870; lean_object* x_1871; lean_object* x_1872; lean_object* x_1873; lean_object* x_1874; 
x_1870 = lean_ctor_get(x_1868, 0);
x_1871 = lean_ctor_get(x_1868, 1);
x_1872 = lean_ctor_get(x_1870, 1);
lean_inc(x_1872);
lean_dec(x_1870);
x_1873 = lean_ctor_get(x_1872, 2);
lean_inc(x_1873);
lean_dec(x_1872);
x_1874 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_1873, x_1866);
if (lean_obj_tag(x_1874) == 0)
{
size_t x_1875; size_t x_1876; uint8_t x_1877; 
lean_free_object(x_1868);
x_1875 = lean_ptr_addr(x_1864);
lean_dec(x_1864);
x_1876 = lean_ptr_addr(x_1866);
x_1877 = lean_usize_dec_eq(x_1875, x_1876);
if (x_1877 == 0)
{
lean_object* x_1878; lean_object* x_1879; lean_object* x_1880; lean_object* x_1881; lean_object* x_1882; lean_object* x_1883; lean_object* x_1884; lean_object* x_1885; lean_object* x_1886; lean_object* x_1887; lean_object* x_1888; lean_object* x_1889; lean_object* x_1890; lean_object* x_1891; lean_object* x_1892; lean_object* x_1893; lean_object* x_1894; lean_object* x_1895; uint8_t x_1896; lean_object* x_1897; lean_object* x_1898; lean_object* x_1899; lean_object* x_1900; lean_object* x_1901; lean_object* x_1902; lean_object* x_1903; lean_object* x_1904; lean_object* x_1905; lean_object* x_1906; uint8_t x_1907; 
lean_dec(x_1);
x_1878 = lean_unsigned_to_nat(0u);
lean_inc(x_1866);
x_1879 = lean_array_set(x_10, x_1878, x_1866);
x_1880 = l_Lean_mkAppN(x_9, x_1879);
lean_dec(x_1879);
x_1881 = lean_st_ref_take(x_13, x_1871);
x_1882 = lean_ctor_get(x_1881, 0);
lean_inc(x_1882);
x_1883 = lean_ctor_get(x_1881, 1);
lean_inc(x_1883);
lean_dec(x_1881);
x_1884 = lean_ctor_get(x_1882, 0);
lean_inc(x_1884);
x_1885 = lean_ctor_get(x_1882, 1);
lean_inc(x_1885);
x_1886 = lean_ctor_get(x_1885, 0);
lean_inc(x_1886);
x_1887 = lean_ctor_get(x_1885, 1);
lean_inc(x_1887);
x_1888 = lean_ctor_get(x_1885, 2);
lean_inc(x_1888);
lean_dec(x_1885);
lean_inc(x_1880);
x_1889 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1888, x_1866, x_1880);
x_1890 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1890, 0, x_1886);
lean_ctor_set(x_1890, 1, x_1887);
lean_ctor_set(x_1890, 2, x_1889);
x_1891 = lean_ctor_get(x_1882, 2);
lean_inc(x_1891);
x_1892 = lean_ctor_get(x_1882, 3);
lean_inc(x_1892);
x_1893 = lean_ctor_get(x_1882, 4);
lean_inc(x_1893);
x_1894 = lean_ctor_get(x_1882, 5);
lean_inc(x_1894);
x_1895 = lean_ctor_get(x_1882, 6);
lean_inc(x_1895);
x_1896 = lean_ctor_get_uint8(x_1882, sizeof(void*)*15);
x_1897 = lean_ctor_get(x_1882, 7);
lean_inc(x_1897);
x_1898 = lean_ctor_get(x_1882, 8);
lean_inc(x_1898);
x_1899 = lean_ctor_get(x_1882, 9);
lean_inc(x_1899);
x_1900 = lean_ctor_get(x_1882, 10);
lean_inc(x_1900);
x_1901 = lean_ctor_get(x_1882, 11);
lean_inc(x_1901);
x_1902 = lean_ctor_get(x_1882, 12);
lean_inc(x_1902);
x_1903 = lean_ctor_get(x_1882, 13);
lean_inc(x_1903);
x_1904 = lean_ctor_get(x_1882, 14);
lean_inc(x_1904);
lean_dec(x_1882);
x_1905 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_1905, 0, x_1884);
lean_ctor_set(x_1905, 1, x_1890);
lean_ctor_set(x_1905, 2, x_1891);
lean_ctor_set(x_1905, 3, x_1892);
lean_ctor_set(x_1905, 4, x_1893);
lean_ctor_set(x_1905, 5, x_1894);
lean_ctor_set(x_1905, 6, x_1895);
lean_ctor_set(x_1905, 7, x_1897);
lean_ctor_set(x_1905, 8, x_1898);
lean_ctor_set(x_1905, 9, x_1899);
lean_ctor_set(x_1905, 10, x_1900);
lean_ctor_set(x_1905, 11, x_1901);
lean_ctor_set(x_1905, 12, x_1902);
lean_ctor_set(x_1905, 13, x_1903);
lean_ctor_set(x_1905, 14, x_1904);
lean_ctor_set_uint8(x_1905, sizeof(void*)*15, x_1896);
x_1906 = lean_st_ref_set(x_13, x_1905, x_1883);
lean_dec(x_13);
x_1907 = !lean_is_exclusive(x_1906);
if (x_1907 == 0)
{
lean_object* x_1908; 
x_1908 = lean_ctor_get(x_1906, 0);
lean_dec(x_1908);
lean_ctor_set(x_1906, 0, x_1880);
return x_1906;
}
else
{
lean_object* x_1909; lean_object* x_1910; 
x_1909 = lean_ctor_get(x_1906, 1);
lean_inc(x_1909);
lean_dec(x_1906);
x_1910 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1910, 0, x_1880);
lean_ctor_set(x_1910, 1, x_1909);
return x_1910;
}
}
else
{
lean_object* x_1911; lean_object* x_1912; lean_object* x_1913; lean_object* x_1914; lean_object* x_1915; lean_object* x_1916; lean_object* x_1917; lean_object* x_1918; lean_object* x_1919; lean_object* x_1920; lean_object* x_1921; lean_object* x_1922; lean_object* x_1923; lean_object* x_1924; lean_object* x_1925; uint8_t x_1926; lean_object* x_1927; lean_object* x_1928; lean_object* x_1929; lean_object* x_1930; lean_object* x_1931; lean_object* x_1932; lean_object* x_1933; lean_object* x_1934; lean_object* x_1935; lean_object* x_1936; uint8_t x_1937; 
lean_dec(x_10);
lean_dec(x_9);
x_1911 = lean_st_ref_take(x_13, x_1871);
x_1912 = lean_ctor_get(x_1911, 0);
lean_inc(x_1912);
x_1913 = lean_ctor_get(x_1911, 1);
lean_inc(x_1913);
lean_dec(x_1911);
x_1914 = lean_ctor_get(x_1912, 0);
lean_inc(x_1914);
x_1915 = lean_ctor_get(x_1912, 1);
lean_inc(x_1915);
x_1916 = lean_ctor_get(x_1915, 0);
lean_inc(x_1916);
x_1917 = lean_ctor_get(x_1915, 1);
lean_inc(x_1917);
x_1918 = lean_ctor_get(x_1915, 2);
lean_inc(x_1918);
lean_dec(x_1915);
lean_inc(x_1);
x_1919 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1918, x_1866, x_1);
x_1920 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1920, 0, x_1916);
lean_ctor_set(x_1920, 1, x_1917);
lean_ctor_set(x_1920, 2, x_1919);
x_1921 = lean_ctor_get(x_1912, 2);
lean_inc(x_1921);
x_1922 = lean_ctor_get(x_1912, 3);
lean_inc(x_1922);
x_1923 = lean_ctor_get(x_1912, 4);
lean_inc(x_1923);
x_1924 = lean_ctor_get(x_1912, 5);
lean_inc(x_1924);
x_1925 = lean_ctor_get(x_1912, 6);
lean_inc(x_1925);
x_1926 = lean_ctor_get_uint8(x_1912, sizeof(void*)*15);
x_1927 = lean_ctor_get(x_1912, 7);
lean_inc(x_1927);
x_1928 = lean_ctor_get(x_1912, 8);
lean_inc(x_1928);
x_1929 = lean_ctor_get(x_1912, 9);
lean_inc(x_1929);
x_1930 = lean_ctor_get(x_1912, 10);
lean_inc(x_1930);
x_1931 = lean_ctor_get(x_1912, 11);
lean_inc(x_1931);
x_1932 = lean_ctor_get(x_1912, 12);
lean_inc(x_1932);
x_1933 = lean_ctor_get(x_1912, 13);
lean_inc(x_1933);
x_1934 = lean_ctor_get(x_1912, 14);
lean_inc(x_1934);
lean_dec(x_1912);
x_1935 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_1935, 0, x_1914);
lean_ctor_set(x_1935, 1, x_1920);
lean_ctor_set(x_1935, 2, x_1921);
lean_ctor_set(x_1935, 3, x_1922);
lean_ctor_set(x_1935, 4, x_1923);
lean_ctor_set(x_1935, 5, x_1924);
lean_ctor_set(x_1935, 6, x_1925);
lean_ctor_set(x_1935, 7, x_1927);
lean_ctor_set(x_1935, 8, x_1928);
lean_ctor_set(x_1935, 9, x_1929);
lean_ctor_set(x_1935, 10, x_1930);
lean_ctor_set(x_1935, 11, x_1931);
lean_ctor_set(x_1935, 12, x_1932);
lean_ctor_set(x_1935, 13, x_1933);
lean_ctor_set(x_1935, 14, x_1934);
lean_ctor_set_uint8(x_1935, sizeof(void*)*15, x_1926);
x_1936 = lean_st_ref_set(x_13, x_1935, x_1913);
lean_dec(x_13);
x_1937 = !lean_is_exclusive(x_1936);
if (x_1937 == 0)
{
lean_object* x_1938; 
x_1938 = lean_ctor_get(x_1936, 0);
lean_dec(x_1938);
lean_ctor_set(x_1936, 0, x_1);
return x_1936;
}
else
{
lean_object* x_1939; lean_object* x_1940; 
x_1939 = lean_ctor_get(x_1936, 1);
lean_inc(x_1939);
lean_dec(x_1936);
x_1940 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1940, 0, x_1);
lean_ctor_set(x_1940, 1, x_1939);
return x_1940;
}
}
}
else
{
lean_object* x_1941; 
lean_dec(x_1866);
lean_dec(x_1864);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_1941 = lean_ctor_get(x_1874, 0);
lean_inc(x_1941);
lean_dec(x_1874);
lean_ctor_set(x_1868, 0, x_1941);
return x_1868;
}
}
else
{
lean_object* x_1942; lean_object* x_1943; lean_object* x_1944; lean_object* x_1945; lean_object* x_1946; 
x_1942 = lean_ctor_get(x_1868, 0);
x_1943 = lean_ctor_get(x_1868, 1);
lean_inc(x_1943);
lean_inc(x_1942);
lean_dec(x_1868);
x_1944 = lean_ctor_get(x_1942, 1);
lean_inc(x_1944);
lean_dec(x_1942);
x_1945 = lean_ctor_get(x_1944, 2);
lean_inc(x_1945);
lean_dec(x_1944);
x_1946 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_1945, x_1866);
if (lean_obj_tag(x_1946) == 0)
{
size_t x_1947; size_t x_1948; uint8_t x_1949; 
x_1947 = lean_ptr_addr(x_1864);
lean_dec(x_1864);
x_1948 = lean_ptr_addr(x_1866);
x_1949 = lean_usize_dec_eq(x_1947, x_1948);
if (x_1949 == 0)
{
lean_object* x_1950; lean_object* x_1951; lean_object* x_1952; lean_object* x_1953; lean_object* x_1954; lean_object* x_1955; lean_object* x_1956; lean_object* x_1957; lean_object* x_1958; lean_object* x_1959; lean_object* x_1960; lean_object* x_1961; lean_object* x_1962; lean_object* x_1963; lean_object* x_1964; lean_object* x_1965; lean_object* x_1966; lean_object* x_1967; uint8_t x_1968; lean_object* x_1969; lean_object* x_1970; lean_object* x_1971; lean_object* x_1972; lean_object* x_1973; lean_object* x_1974; lean_object* x_1975; lean_object* x_1976; lean_object* x_1977; lean_object* x_1978; lean_object* x_1979; lean_object* x_1980; lean_object* x_1981; 
lean_dec(x_1);
x_1950 = lean_unsigned_to_nat(0u);
lean_inc(x_1866);
x_1951 = lean_array_set(x_10, x_1950, x_1866);
x_1952 = l_Lean_mkAppN(x_9, x_1951);
lean_dec(x_1951);
x_1953 = lean_st_ref_take(x_13, x_1943);
x_1954 = lean_ctor_get(x_1953, 0);
lean_inc(x_1954);
x_1955 = lean_ctor_get(x_1953, 1);
lean_inc(x_1955);
lean_dec(x_1953);
x_1956 = lean_ctor_get(x_1954, 0);
lean_inc(x_1956);
x_1957 = lean_ctor_get(x_1954, 1);
lean_inc(x_1957);
x_1958 = lean_ctor_get(x_1957, 0);
lean_inc(x_1958);
x_1959 = lean_ctor_get(x_1957, 1);
lean_inc(x_1959);
x_1960 = lean_ctor_get(x_1957, 2);
lean_inc(x_1960);
lean_dec(x_1957);
lean_inc(x_1952);
x_1961 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1960, x_1866, x_1952);
x_1962 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1962, 0, x_1958);
lean_ctor_set(x_1962, 1, x_1959);
lean_ctor_set(x_1962, 2, x_1961);
x_1963 = lean_ctor_get(x_1954, 2);
lean_inc(x_1963);
x_1964 = lean_ctor_get(x_1954, 3);
lean_inc(x_1964);
x_1965 = lean_ctor_get(x_1954, 4);
lean_inc(x_1965);
x_1966 = lean_ctor_get(x_1954, 5);
lean_inc(x_1966);
x_1967 = lean_ctor_get(x_1954, 6);
lean_inc(x_1967);
x_1968 = lean_ctor_get_uint8(x_1954, sizeof(void*)*15);
x_1969 = lean_ctor_get(x_1954, 7);
lean_inc(x_1969);
x_1970 = lean_ctor_get(x_1954, 8);
lean_inc(x_1970);
x_1971 = lean_ctor_get(x_1954, 9);
lean_inc(x_1971);
x_1972 = lean_ctor_get(x_1954, 10);
lean_inc(x_1972);
x_1973 = lean_ctor_get(x_1954, 11);
lean_inc(x_1973);
x_1974 = lean_ctor_get(x_1954, 12);
lean_inc(x_1974);
x_1975 = lean_ctor_get(x_1954, 13);
lean_inc(x_1975);
x_1976 = lean_ctor_get(x_1954, 14);
lean_inc(x_1976);
lean_dec(x_1954);
x_1977 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_1977, 0, x_1956);
lean_ctor_set(x_1977, 1, x_1962);
lean_ctor_set(x_1977, 2, x_1963);
lean_ctor_set(x_1977, 3, x_1964);
lean_ctor_set(x_1977, 4, x_1965);
lean_ctor_set(x_1977, 5, x_1966);
lean_ctor_set(x_1977, 6, x_1967);
lean_ctor_set(x_1977, 7, x_1969);
lean_ctor_set(x_1977, 8, x_1970);
lean_ctor_set(x_1977, 9, x_1971);
lean_ctor_set(x_1977, 10, x_1972);
lean_ctor_set(x_1977, 11, x_1973);
lean_ctor_set(x_1977, 12, x_1974);
lean_ctor_set(x_1977, 13, x_1975);
lean_ctor_set(x_1977, 14, x_1976);
lean_ctor_set_uint8(x_1977, sizeof(void*)*15, x_1968);
x_1978 = lean_st_ref_set(x_13, x_1977, x_1955);
lean_dec(x_13);
x_1979 = lean_ctor_get(x_1978, 1);
lean_inc(x_1979);
if (lean_is_exclusive(x_1978)) {
 lean_ctor_release(x_1978, 0);
 lean_ctor_release(x_1978, 1);
 x_1980 = x_1978;
} else {
 lean_dec_ref(x_1978);
 x_1980 = lean_box(0);
}
if (lean_is_scalar(x_1980)) {
 x_1981 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1981 = x_1980;
}
lean_ctor_set(x_1981, 0, x_1952);
lean_ctor_set(x_1981, 1, x_1979);
return x_1981;
}
else
{
lean_object* x_1982; lean_object* x_1983; lean_object* x_1984; lean_object* x_1985; lean_object* x_1986; lean_object* x_1987; lean_object* x_1988; lean_object* x_1989; lean_object* x_1990; lean_object* x_1991; lean_object* x_1992; lean_object* x_1993; lean_object* x_1994; lean_object* x_1995; lean_object* x_1996; uint8_t x_1997; lean_object* x_1998; lean_object* x_1999; lean_object* x_2000; lean_object* x_2001; lean_object* x_2002; lean_object* x_2003; lean_object* x_2004; lean_object* x_2005; lean_object* x_2006; lean_object* x_2007; lean_object* x_2008; lean_object* x_2009; lean_object* x_2010; 
lean_dec(x_10);
lean_dec(x_9);
x_1982 = lean_st_ref_take(x_13, x_1943);
x_1983 = lean_ctor_get(x_1982, 0);
lean_inc(x_1983);
x_1984 = lean_ctor_get(x_1982, 1);
lean_inc(x_1984);
lean_dec(x_1982);
x_1985 = lean_ctor_get(x_1983, 0);
lean_inc(x_1985);
x_1986 = lean_ctor_get(x_1983, 1);
lean_inc(x_1986);
x_1987 = lean_ctor_get(x_1986, 0);
lean_inc(x_1987);
x_1988 = lean_ctor_get(x_1986, 1);
lean_inc(x_1988);
x_1989 = lean_ctor_get(x_1986, 2);
lean_inc(x_1989);
lean_dec(x_1986);
lean_inc(x_1);
x_1990 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1989, x_1866, x_1);
x_1991 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1991, 0, x_1987);
lean_ctor_set(x_1991, 1, x_1988);
lean_ctor_set(x_1991, 2, x_1990);
x_1992 = lean_ctor_get(x_1983, 2);
lean_inc(x_1992);
x_1993 = lean_ctor_get(x_1983, 3);
lean_inc(x_1993);
x_1994 = lean_ctor_get(x_1983, 4);
lean_inc(x_1994);
x_1995 = lean_ctor_get(x_1983, 5);
lean_inc(x_1995);
x_1996 = lean_ctor_get(x_1983, 6);
lean_inc(x_1996);
x_1997 = lean_ctor_get_uint8(x_1983, sizeof(void*)*15);
x_1998 = lean_ctor_get(x_1983, 7);
lean_inc(x_1998);
x_1999 = lean_ctor_get(x_1983, 8);
lean_inc(x_1999);
x_2000 = lean_ctor_get(x_1983, 9);
lean_inc(x_2000);
x_2001 = lean_ctor_get(x_1983, 10);
lean_inc(x_2001);
x_2002 = lean_ctor_get(x_1983, 11);
lean_inc(x_2002);
x_2003 = lean_ctor_get(x_1983, 12);
lean_inc(x_2003);
x_2004 = lean_ctor_get(x_1983, 13);
lean_inc(x_2004);
x_2005 = lean_ctor_get(x_1983, 14);
lean_inc(x_2005);
lean_dec(x_1983);
x_2006 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_2006, 0, x_1985);
lean_ctor_set(x_2006, 1, x_1991);
lean_ctor_set(x_2006, 2, x_1992);
lean_ctor_set(x_2006, 3, x_1993);
lean_ctor_set(x_2006, 4, x_1994);
lean_ctor_set(x_2006, 5, x_1995);
lean_ctor_set(x_2006, 6, x_1996);
lean_ctor_set(x_2006, 7, x_1998);
lean_ctor_set(x_2006, 8, x_1999);
lean_ctor_set(x_2006, 9, x_2000);
lean_ctor_set(x_2006, 10, x_2001);
lean_ctor_set(x_2006, 11, x_2002);
lean_ctor_set(x_2006, 12, x_2003);
lean_ctor_set(x_2006, 13, x_2004);
lean_ctor_set(x_2006, 14, x_2005);
lean_ctor_set_uint8(x_2006, sizeof(void*)*15, x_1997);
x_2007 = lean_st_ref_set(x_13, x_2006, x_1984);
lean_dec(x_13);
x_2008 = lean_ctor_get(x_2007, 1);
lean_inc(x_2008);
if (lean_is_exclusive(x_2007)) {
 lean_ctor_release(x_2007, 0);
 lean_ctor_release(x_2007, 1);
 x_2009 = x_2007;
} else {
 lean_dec_ref(x_2007);
 x_2009 = lean_box(0);
}
if (lean_is_scalar(x_2009)) {
 x_2010 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2010 = x_2009;
}
lean_ctor_set(x_2010, 0, x_1);
lean_ctor_set(x_2010, 1, x_2008);
return x_2010;
}
}
else
{
lean_object* x_2011; lean_object* x_2012; 
lean_dec(x_1866);
lean_dec(x_1864);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_2011 = lean_ctor_get(x_1946, 0);
lean_inc(x_2011);
lean_dec(x_1946);
x_2012 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2012, 0, x_2011);
lean_ctor_set(x_2012, 1, x_1943);
return x_2012;
}
}
}
else
{
uint8_t x_2013; 
lean_dec(x_1864);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_2013 = !lean_is_exclusive(x_1865);
if (x_2013 == 0)
{
return x_1865;
}
else
{
lean_object* x_2014; lean_object* x_2015; lean_object* x_2016; 
x_2014 = lean_ctor_get(x_1865, 0);
x_2015 = lean_ctor_get(x_1865, 1);
lean_inc(x_2015);
lean_inc(x_2014);
lean_dec(x_1865);
x_2016 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2016, 0, x_2014);
lean_ctor_set(x_2016, 1, x_2015);
return x_2016;
}
}
}
block_2055:
{
lean_object* x_2019; 
lean_dec(x_2018);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_9);
x_2019 = l_Lean_Meta_getFunInfo(x_9, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_2019) == 0)
{
lean_object* x_2020; lean_object* x_2021; lean_object* x_2022; lean_object* x_2023; lean_object* x_2024; lean_object* x_2025; lean_object* x_2026; uint8_t x_2027; lean_object* x_2028; lean_object* x_2029; lean_object* x_2030; lean_object* x_2031; 
x_2020 = lean_ctor_get(x_2019, 0);
lean_inc(x_2020);
x_2021 = lean_ctor_get(x_2019, 1);
lean_inc(x_2021);
lean_dec(x_2019);
x_2022 = lean_ctor_get(x_2020, 0);
lean_inc(x_2022);
lean_dec(x_2020);
x_2023 = lean_array_get_size(x_10);
x_2024 = lean_unsigned_to_nat(0u);
x_2025 = lean_unsigned_to_nat(1u);
lean_inc(x_2023);
x_2026 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2026, 0, x_2024);
lean_ctor_set(x_2026, 1, x_2023);
lean_ctor_set(x_2026, 2, x_2025);
x_2027 = 0;
x_2028 = lean_box(x_2027);
lean_inc(x_10);
x_2029 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2029, 0, x_10);
lean_ctor_set(x_2029, 1, x_2028);
x_2030 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_2026);
lean_inc(x_9);
lean_inc(x_1);
x_2031 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_2030, x_2022, x_2023, x_2026, x_2026, x_2029, x_2024, lean_box(0), lean_box(0), x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_2021);
if (lean_obj_tag(x_2031) == 0)
{
lean_object* x_2032; lean_object* x_2033; uint8_t x_2034; 
x_2032 = lean_ctor_get(x_2031, 0);
lean_inc(x_2032);
x_2033 = lean_ctor_get(x_2032, 1);
lean_inc(x_2033);
x_2034 = lean_unbox(x_2033);
lean_dec(x_2033);
if (x_2034 == 0)
{
uint8_t x_2035; 
lean_dec(x_2032);
lean_dec(x_9);
x_2035 = !lean_is_exclusive(x_2031);
if (x_2035 == 0)
{
lean_object* x_2036; 
x_2036 = lean_ctor_get(x_2031, 0);
lean_dec(x_2036);
lean_ctor_set(x_2031, 0, x_1);
return x_2031;
}
else
{
lean_object* x_2037; lean_object* x_2038; 
x_2037 = lean_ctor_get(x_2031, 1);
lean_inc(x_2037);
lean_dec(x_2031);
x_2038 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2038, 0, x_1);
lean_ctor_set(x_2038, 1, x_2037);
return x_2038;
}
}
else
{
uint8_t x_2039; 
lean_dec(x_1);
x_2039 = !lean_is_exclusive(x_2031);
if (x_2039 == 0)
{
lean_object* x_2040; lean_object* x_2041; lean_object* x_2042; 
x_2040 = lean_ctor_get(x_2031, 0);
lean_dec(x_2040);
x_2041 = lean_ctor_get(x_2032, 0);
lean_inc(x_2041);
lean_dec(x_2032);
x_2042 = l_Lean_mkAppN(x_9, x_2041);
lean_dec(x_2041);
lean_ctor_set(x_2031, 0, x_2042);
return x_2031;
}
else
{
lean_object* x_2043; lean_object* x_2044; lean_object* x_2045; lean_object* x_2046; 
x_2043 = lean_ctor_get(x_2031, 1);
lean_inc(x_2043);
lean_dec(x_2031);
x_2044 = lean_ctor_get(x_2032, 0);
lean_inc(x_2044);
lean_dec(x_2032);
x_2045 = l_Lean_mkAppN(x_9, x_2044);
lean_dec(x_2044);
x_2046 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2046, 0, x_2045);
lean_ctor_set(x_2046, 1, x_2043);
return x_2046;
}
}
}
else
{
uint8_t x_2047; 
lean_dec(x_9);
lean_dec(x_1);
x_2047 = !lean_is_exclusive(x_2031);
if (x_2047 == 0)
{
return x_2031;
}
else
{
lean_object* x_2048; lean_object* x_2049; lean_object* x_2050; 
x_2048 = lean_ctor_get(x_2031, 0);
x_2049 = lean_ctor_get(x_2031, 1);
lean_inc(x_2049);
lean_inc(x_2048);
lean_dec(x_2031);
x_2050 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2050, 0, x_2048);
lean_ctor_set(x_2050, 1, x_2049);
return x_2050;
}
}
}
else
{
uint8_t x_2051; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2051 = !lean_is_exclusive(x_2019);
if (x_2051 == 0)
{
return x_2019;
}
else
{
lean_object* x_2052; lean_object* x_2053; lean_object* x_2054; 
x_2052 = lean_ctor_get(x_2019, 0);
x_2053 = lean_ctor_get(x_2019, 1);
lean_inc(x_2053);
lean_inc(x_2052);
lean_dec(x_2019);
x_2054 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2054, 0, x_2052);
lean_ctor_set(x_2054, 1, x_2053);
return x_2054;
}
}
}
}
default: 
{
lean_object* x_2068; lean_object* x_2222; lean_object* x_2260; uint8_t x_2261; 
lean_dec(x_11);
x_2260 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_2261 = l_Lean_Expr_isConstOf(x_9, x_2260);
if (x_2261 == 0)
{
lean_object* x_2262; 
x_2262 = lean_box(0);
x_2222 = x_2262;
goto block_2259;
}
else
{
lean_object* x_2263; lean_object* x_2264; uint8_t x_2265; 
x_2263 = lean_array_get_size(x_10);
x_2264 = lean_unsigned_to_nat(2u);
x_2265 = lean_nat_dec_eq(x_2263, x_2264);
if (x_2265 == 0)
{
lean_object* x_2266; 
lean_dec(x_2263);
x_2266 = lean_box(0);
x_2222 = x_2266;
goto block_2259;
}
else
{
lean_object* x_2267; uint8_t x_2268; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2267 = lean_unsigned_to_nat(0u);
x_2268 = lean_nat_dec_lt(x_2267, x_2263);
lean_dec(x_2263);
if (x_2268 == 0)
{
lean_object* x_2269; lean_object* x_2270; 
x_2269 = l_Lean_instInhabitedExpr;
x_2270 = l_outOfBounds___rarg(x_2269);
x_2068 = x_2270;
goto block_2221;
}
else
{
lean_object* x_2271; 
x_2271 = lean_array_fget(x_10, x_2267);
x_2068 = x_2271;
goto block_2221;
}
}
}
block_2221:
{
lean_object* x_2069; 
lean_inc(x_13);
lean_inc(x_2068);
x_2069 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_2068, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_2069) == 0)
{
lean_object* x_2070; lean_object* x_2071; lean_object* x_2072; uint8_t x_2073; 
x_2070 = lean_ctor_get(x_2069, 0);
lean_inc(x_2070);
x_2071 = lean_ctor_get(x_2069, 1);
lean_inc(x_2071);
lean_dec(x_2069);
x_2072 = lean_st_ref_get(x_13, x_2071);
x_2073 = !lean_is_exclusive(x_2072);
if (x_2073 == 0)
{
lean_object* x_2074; lean_object* x_2075; lean_object* x_2076; lean_object* x_2077; lean_object* x_2078; 
x_2074 = lean_ctor_get(x_2072, 0);
x_2075 = lean_ctor_get(x_2072, 1);
x_2076 = lean_ctor_get(x_2074, 1);
lean_inc(x_2076);
lean_dec(x_2074);
x_2077 = lean_ctor_get(x_2076, 2);
lean_inc(x_2077);
lean_dec(x_2076);
x_2078 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_2077, x_2070);
if (lean_obj_tag(x_2078) == 0)
{
size_t x_2079; size_t x_2080; uint8_t x_2081; 
lean_free_object(x_2072);
x_2079 = lean_ptr_addr(x_2068);
lean_dec(x_2068);
x_2080 = lean_ptr_addr(x_2070);
x_2081 = lean_usize_dec_eq(x_2079, x_2080);
if (x_2081 == 0)
{
lean_object* x_2082; lean_object* x_2083; lean_object* x_2084; lean_object* x_2085; lean_object* x_2086; lean_object* x_2087; lean_object* x_2088; lean_object* x_2089; lean_object* x_2090; lean_object* x_2091; lean_object* x_2092; lean_object* x_2093; lean_object* x_2094; lean_object* x_2095; lean_object* x_2096; lean_object* x_2097; lean_object* x_2098; lean_object* x_2099; uint8_t x_2100; lean_object* x_2101; lean_object* x_2102; lean_object* x_2103; lean_object* x_2104; lean_object* x_2105; lean_object* x_2106; lean_object* x_2107; lean_object* x_2108; lean_object* x_2109; lean_object* x_2110; uint8_t x_2111; 
lean_dec(x_1);
x_2082 = lean_unsigned_to_nat(0u);
lean_inc(x_2070);
x_2083 = lean_array_set(x_10, x_2082, x_2070);
x_2084 = l_Lean_mkAppN(x_9, x_2083);
lean_dec(x_2083);
x_2085 = lean_st_ref_take(x_13, x_2075);
x_2086 = lean_ctor_get(x_2085, 0);
lean_inc(x_2086);
x_2087 = lean_ctor_get(x_2085, 1);
lean_inc(x_2087);
lean_dec(x_2085);
x_2088 = lean_ctor_get(x_2086, 0);
lean_inc(x_2088);
x_2089 = lean_ctor_get(x_2086, 1);
lean_inc(x_2089);
x_2090 = lean_ctor_get(x_2089, 0);
lean_inc(x_2090);
x_2091 = lean_ctor_get(x_2089, 1);
lean_inc(x_2091);
x_2092 = lean_ctor_get(x_2089, 2);
lean_inc(x_2092);
lean_dec(x_2089);
lean_inc(x_2084);
x_2093 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_2092, x_2070, x_2084);
x_2094 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2094, 0, x_2090);
lean_ctor_set(x_2094, 1, x_2091);
lean_ctor_set(x_2094, 2, x_2093);
x_2095 = lean_ctor_get(x_2086, 2);
lean_inc(x_2095);
x_2096 = lean_ctor_get(x_2086, 3);
lean_inc(x_2096);
x_2097 = lean_ctor_get(x_2086, 4);
lean_inc(x_2097);
x_2098 = lean_ctor_get(x_2086, 5);
lean_inc(x_2098);
x_2099 = lean_ctor_get(x_2086, 6);
lean_inc(x_2099);
x_2100 = lean_ctor_get_uint8(x_2086, sizeof(void*)*15);
x_2101 = lean_ctor_get(x_2086, 7);
lean_inc(x_2101);
x_2102 = lean_ctor_get(x_2086, 8);
lean_inc(x_2102);
x_2103 = lean_ctor_get(x_2086, 9);
lean_inc(x_2103);
x_2104 = lean_ctor_get(x_2086, 10);
lean_inc(x_2104);
x_2105 = lean_ctor_get(x_2086, 11);
lean_inc(x_2105);
x_2106 = lean_ctor_get(x_2086, 12);
lean_inc(x_2106);
x_2107 = lean_ctor_get(x_2086, 13);
lean_inc(x_2107);
x_2108 = lean_ctor_get(x_2086, 14);
lean_inc(x_2108);
lean_dec(x_2086);
x_2109 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_2109, 0, x_2088);
lean_ctor_set(x_2109, 1, x_2094);
lean_ctor_set(x_2109, 2, x_2095);
lean_ctor_set(x_2109, 3, x_2096);
lean_ctor_set(x_2109, 4, x_2097);
lean_ctor_set(x_2109, 5, x_2098);
lean_ctor_set(x_2109, 6, x_2099);
lean_ctor_set(x_2109, 7, x_2101);
lean_ctor_set(x_2109, 8, x_2102);
lean_ctor_set(x_2109, 9, x_2103);
lean_ctor_set(x_2109, 10, x_2104);
lean_ctor_set(x_2109, 11, x_2105);
lean_ctor_set(x_2109, 12, x_2106);
lean_ctor_set(x_2109, 13, x_2107);
lean_ctor_set(x_2109, 14, x_2108);
lean_ctor_set_uint8(x_2109, sizeof(void*)*15, x_2100);
x_2110 = lean_st_ref_set(x_13, x_2109, x_2087);
lean_dec(x_13);
x_2111 = !lean_is_exclusive(x_2110);
if (x_2111 == 0)
{
lean_object* x_2112; 
x_2112 = lean_ctor_get(x_2110, 0);
lean_dec(x_2112);
lean_ctor_set(x_2110, 0, x_2084);
return x_2110;
}
else
{
lean_object* x_2113; lean_object* x_2114; 
x_2113 = lean_ctor_get(x_2110, 1);
lean_inc(x_2113);
lean_dec(x_2110);
x_2114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2114, 0, x_2084);
lean_ctor_set(x_2114, 1, x_2113);
return x_2114;
}
}
else
{
lean_object* x_2115; lean_object* x_2116; lean_object* x_2117; lean_object* x_2118; lean_object* x_2119; lean_object* x_2120; lean_object* x_2121; lean_object* x_2122; lean_object* x_2123; lean_object* x_2124; lean_object* x_2125; lean_object* x_2126; lean_object* x_2127; lean_object* x_2128; lean_object* x_2129; uint8_t x_2130; lean_object* x_2131; lean_object* x_2132; lean_object* x_2133; lean_object* x_2134; lean_object* x_2135; lean_object* x_2136; lean_object* x_2137; lean_object* x_2138; lean_object* x_2139; lean_object* x_2140; uint8_t x_2141; 
lean_dec(x_10);
lean_dec(x_9);
x_2115 = lean_st_ref_take(x_13, x_2075);
x_2116 = lean_ctor_get(x_2115, 0);
lean_inc(x_2116);
x_2117 = lean_ctor_get(x_2115, 1);
lean_inc(x_2117);
lean_dec(x_2115);
x_2118 = lean_ctor_get(x_2116, 0);
lean_inc(x_2118);
x_2119 = lean_ctor_get(x_2116, 1);
lean_inc(x_2119);
x_2120 = lean_ctor_get(x_2119, 0);
lean_inc(x_2120);
x_2121 = lean_ctor_get(x_2119, 1);
lean_inc(x_2121);
x_2122 = lean_ctor_get(x_2119, 2);
lean_inc(x_2122);
lean_dec(x_2119);
lean_inc(x_1);
x_2123 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_2122, x_2070, x_1);
x_2124 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2124, 0, x_2120);
lean_ctor_set(x_2124, 1, x_2121);
lean_ctor_set(x_2124, 2, x_2123);
x_2125 = lean_ctor_get(x_2116, 2);
lean_inc(x_2125);
x_2126 = lean_ctor_get(x_2116, 3);
lean_inc(x_2126);
x_2127 = lean_ctor_get(x_2116, 4);
lean_inc(x_2127);
x_2128 = lean_ctor_get(x_2116, 5);
lean_inc(x_2128);
x_2129 = lean_ctor_get(x_2116, 6);
lean_inc(x_2129);
x_2130 = lean_ctor_get_uint8(x_2116, sizeof(void*)*15);
x_2131 = lean_ctor_get(x_2116, 7);
lean_inc(x_2131);
x_2132 = lean_ctor_get(x_2116, 8);
lean_inc(x_2132);
x_2133 = lean_ctor_get(x_2116, 9);
lean_inc(x_2133);
x_2134 = lean_ctor_get(x_2116, 10);
lean_inc(x_2134);
x_2135 = lean_ctor_get(x_2116, 11);
lean_inc(x_2135);
x_2136 = lean_ctor_get(x_2116, 12);
lean_inc(x_2136);
x_2137 = lean_ctor_get(x_2116, 13);
lean_inc(x_2137);
x_2138 = lean_ctor_get(x_2116, 14);
lean_inc(x_2138);
lean_dec(x_2116);
x_2139 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_2139, 0, x_2118);
lean_ctor_set(x_2139, 1, x_2124);
lean_ctor_set(x_2139, 2, x_2125);
lean_ctor_set(x_2139, 3, x_2126);
lean_ctor_set(x_2139, 4, x_2127);
lean_ctor_set(x_2139, 5, x_2128);
lean_ctor_set(x_2139, 6, x_2129);
lean_ctor_set(x_2139, 7, x_2131);
lean_ctor_set(x_2139, 8, x_2132);
lean_ctor_set(x_2139, 9, x_2133);
lean_ctor_set(x_2139, 10, x_2134);
lean_ctor_set(x_2139, 11, x_2135);
lean_ctor_set(x_2139, 12, x_2136);
lean_ctor_set(x_2139, 13, x_2137);
lean_ctor_set(x_2139, 14, x_2138);
lean_ctor_set_uint8(x_2139, sizeof(void*)*15, x_2130);
x_2140 = lean_st_ref_set(x_13, x_2139, x_2117);
lean_dec(x_13);
x_2141 = !lean_is_exclusive(x_2140);
if (x_2141 == 0)
{
lean_object* x_2142; 
x_2142 = lean_ctor_get(x_2140, 0);
lean_dec(x_2142);
lean_ctor_set(x_2140, 0, x_1);
return x_2140;
}
else
{
lean_object* x_2143; lean_object* x_2144; 
x_2143 = lean_ctor_get(x_2140, 1);
lean_inc(x_2143);
lean_dec(x_2140);
x_2144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2144, 0, x_1);
lean_ctor_set(x_2144, 1, x_2143);
return x_2144;
}
}
}
else
{
lean_object* x_2145; 
lean_dec(x_2070);
lean_dec(x_2068);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_2145 = lean_ctor_get(x_2078, 0);
lean_inc(x_2145);
lean_dec(x_2078);
lean_ctor_set(x_2072, 0, x_2145);
return x_2072;
}
}
else
{
lean_object* x_2146; lean_object* x_2147; lean_object* x_2148; lean_object* x_2149; lean_object* x_2150; 
x_2146 = lean_ctor_get(x_2072, 0);
x_2147 = lean_ctor_get(x_2072, 1);
lean_inc(x_2147);
lean_inc(x_2146);
lean_dec(x_2072);
x_2148 = lean_ctor_get(x_2146, 1);
lean_inc(x_2148);
lean_dec(x_2146);
x_2149 = lean_ctor_get(x_2148, 2);
lean_inc(x_2149);
lean_dec(x_2148);
x_2150 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_2149, x_2070);
if (lean_obj_tag(x_2150) == 0)
{
size_t x_2151; size_t x_2152; uint8_t x_2153; 
x_2151 = lean_ptr_addr(x_2068);
lean_dec(x_2068);
x_2152 = lean_ptr_addr(x_2070);
x_2153 = lean_usize_dec_eq(x_2151, x_2152);
if (x_2153 == 0)
{
lean_object* x_2154; lean_object* x_2155; lean_object* x_2156; lean_object* x_2157; lean_object* x_2158; lean_object* x_2159; lean_object* x_2160; lean_object* x_2161; lean_object* x_2162; lean_object* x_2163; lean_object* x_2164; lean_object* x_2165; lean_object* x_2166; lean_object* x_2167; lean_object* x_2168; lean_object* x_2169; lean_object* x_2170; lean_object* x_2171; uint8_t x_2172; lean_object* x_2173; lean_object* x_2174; lean_object* x_2175; lean_object* x_2176; lean_object* x_2177; lean_object* x_2178; lean_object* x_2179; lean_object* x_2180; lean_object* x_2181; lean_object* x_2182; lean_object* x_2183; lean_object* x_2184; lean_object* x_2185; 
lean_dec(x_1);
x_2154 = lean_unsigned_to_nat(0u);
lean_inc(x_2070);
x_2155 = lean_array_set(x_10, x_2154, x_2070);
x_2156 = l_Lean_mkAppN(x_9, x_2155);
lean_dec(x_2155);
x_2157 = lean_st_ref_take(x_13, x_2147);
x_2158 = lean_ctor_get(x_2157, 0);
lean_inc(x_2158);
x_2159 = lean_ctor_get(x_2157, 1);
lean_inc(x_2159);
lean_dec(x_2157);
x_2160 = lean_ctor_get(x_2158, 0);
lean_inc(x_2160);
x_2161 = lean_ctor_get(x_2158, 1);
lean_inc(x_2161);
x_2162 = lean_ctor_get(x_2161, 0);
lean_inc(x_2162);
x_2163 = lean_ctor_get(x_2161, 1);
lean_inc(x_2163);
x_2164 = lean_ctor_get(x_2161, 2);
lean_inc(x_2164);
lean_dec(x_2161);
lean_inc(x_2156);
x_2165 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_2164, x_2070, x_2156);
x_2166 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2166, 0, x_2162);
lean_ctor_set(x_2166, 1, x_2163);
lean_ctor_set(x_2166, 2, x_2165);
x_2167 = lean_ctor_get(x_2158, 2);
lean_inc(x_2167);
x_2168 = lean_ctor_get(x_2158, 3);
lean_inc(x_2168);
x_2169 = lean_ctor_get(x_2158, 4);
lean_inc(x_2169);
x_2170 = lean_ctor_get(x_2158, 5);
lean_inc(x_2170);
x_2171 = lean_ctor_get(x_2158, 6);
lean_inc(x_2171);
x_2172 = lean_ctor_get_uint8(x_2158, sizeof(void*)*15);
x_2173 = lean_ctor_get(x_2158, 7);
lean_inc(x_2173);
x_2174 = lean_ctor_get(x_2158, 8);
lean_inc(x_2174);
x_2175 = lean_ctor_get(x_2158, 9);
lean_inc(x_2175);
x_2176 = lean_ctor_get(x_2158, 10);
lean_inc(x_2176);
x_2177 = lean_ctor_get(x_2158, 11);
lean_inc(x_2177);
x_2178 = lean_ctor_get(x_2158, 12);
lean_inc(x_2178);
x_2179 = lean_ctor_get(x_2158, 13);
lean_inc(x_2179);
x_2180 = lean_ctor_get(x_2158, 14);
lean_inc(x_2180);
lean_dec(x_2158);
x_2181 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_2181, 0, x_2160);
lean_ctor_set(x_2181, 1, x_2166);
lean_ctor_set(x_2181, 2, x_2167);
lean_ctor_set(x_2181, 3, x_2168);
lean_ctor_set(x_2181, 4, x_2169);
lean_ctor_set(x_2181, 5, x_2170);
lean_ctor_set(x_2181, 6, x_2171);
lean_ctor_set(x_2181, 7, x_2173);
lean_ctor_set(x_2181, 8, x_2174);
lean_ctor_set(x_2181, 9, x_2175);
lean_ctor_set(x_2181, 10, x_2176);
lean_ctor_set(x_2181, 11, x_2177);
lean_ctor_set(x_2181, 12, x_2178);
lean_ctor_set(x_2181, 13, x_2179);
lean_ctor_set(x_2181, 14, x_2180);
lean_ctor_set_uint8(x_2181, sizeof(void*)*15, x_2172);
x_2182 = lean_st_ref_set(x_13, x_2181, x_2159);
lean_dec(x_13);
x_2183 = lean_ctor_get(x_2182, 1);
lean_inc(x_2183);
if (lean_is_exclusive(x_2182)) {
 lean_ctor_release(x_2182, 0);
 lean_ctor_release(x_2182, 1);
 x_2184 = x_2182;
} else {
 lean_dec_ref(x_2182);
 x_2184 = lean_box(0);
}
if (lean_is_scalar(x_2184)) {
 x_2185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2185 = x_2184;
}
lean_ctor_set(x_2185, 0, x_2156);
lean_ctor_set(x_2185, 1, x_2183);
return x_2185;
}
else
{
lean_object* x_2186; lean_object* x_2187; lean_object* x_2188; lean_object* x_2189; lean_object* x_2190; lean_object* x_2191; lean_object* x_2192; lean_object* x_2193; lean_object* x_2194; lean_object* x_2195; lean_object* x_2196; lean_object* x_2197; lean_object* x_2198; lean_object* x_2199; lean_object* x_2200; uint8_t x_2201; lean_object* x_2202; lean_object* x_2203; lean_object* x_2204; lean_object* x_2205; lean_object* x_2206; lean_object* x_2207; lean_object* x_2208; lean_object* x_2209; lean_object* x_2210; lean_object* x_2211; lean_object* x_2212; lean_object* x_2213; lean_object* x_2214; 
lean_dec(x_10);
lean_dec(x_9);
x_2186 = lean_st_ref_take(x_13, x_2147);
x_2187 = lean_ctor_get(x_2186, 0);
lean_inc(x_2187);
x_2188 = lean_ctor_get(x_2186, 1);
lean_inc(x_2188);
lean_dec(x_2186);
x_2189 = lean_ctor_get(x_2187, 0);
lean_inc(x_2189);
x_2190 = lean_ctor_get(x_2187, 1);
lean_inc(x_2190);
x_2191 = lean_ctor_get(x_2190, 0);
lean_inc(x_2191);
x_2192 = lean_ctor_get(x_2190, 1);
lean_inc(x_2192);
x_2193 = lean_ctor_get(x_2190, 2);
lean_inc(x_2193);
lean_dec(x_2190);
lean_inc(x_1);
x_2194 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_2193, x_2070, x_1);
x_2195 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2195, 0, x_2191);
lean_ctor_set(x_2195, 1, x_2192);
lean_ctor_set(x_2195, 2, x_2194);
x_2196 = lean_ctor_get(x_2187, 2);
lean_inc(x_2196);
x_2197 = lean_ctor_get(x_2187, 3);
lean_inc(x_2197);
x_2198 = lean_ctor_get(x_2187, 4);
lean_inc(x_2198);
x_2199 = lean_ctor_get(x_2187, 5);
lean_inc(x_2199);
x_2200 = lean_ctor_get(x_2187, 6);
lean_inc(x_2200);
x_2201 = lean_ctor_get_uint8(x_2187, sizeof(void*)*15);
x_2202 = lean_ctor_get(x_2187, 7);
lean_inc(x_2202);
x_2203 = lean_ctor_get(x_2187, 8);
lean_inc(x_2203);
x_2204 = lean_ctor_get(x_2187, 9);
lean_inc(x_2204);
x_2205 = lean_ctor_get(x_2187, 10);
lean_inc(x_2205);
x_2206 = lean_ctor_get(x_2187, 11);
lean_inc(x_2206);
x_2207 = lean_ctor_get(x_2187, 12);
lean_inc(x_2207);
x_2208 = lean_ctor_get(x_2187, 13);
lean_inc(x_2208);
x_2209 = lean_ctor_get(x_2187, 14);
lean_inc(x_2209);
lean_dec(x_2187);
x_2210 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_2210, 0, x_2189);
lean_ctor_set(x_2210, 1, x_2195);
lean_ctor_set(x_2210, 2, x_2196);
lean_ctor_set(x_2210, 3, x_2197);
lean_ctor_set(x_2210, 4, x_2198);
lean_ctor_set(x_2210, 5, x_2199);
lean_ctor_set(x_2210, 6, x_2200);
lean_ctor_set(x_2210, 7, x_2202);
lean_ctor_set(x_2210, 8, x_2203);
lean_ctor_set(x_2210, 9, x_2204);
lean_ctor_set(x_2210, 10, x_2205);
lean_ctor_set(x_2210, 11, x_2206);
lean_ctor_set(x_2210, 12, x_2207);
lean_ctor_set(x_2210, 13, x_2208);
lean_ctor_set(x_2210, 14, x_2209);
lean_ctor_set_uint8(x_2210, sizeof(void*)*15, x_2201);
x_2211 = lean_st_ref_set(x_13, x_2210, x_2188);
lean_dec(x_13);
x_2212 = lean_ctor_get(x_2211, 1);
lean_inc(x_2212);
if (lean_is_exclusive(x_2211)) {
 lean_ctor_release(x_2211, 0);
 lean_ctor_release(x_2211, 1);
 x_2213 = x_2211;
} else {
 lean_dec_ref(x_2211);
 x_2213 = lean_box(0);
}
if (lean_is_scalar(x_2213)) {
 x_2214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2214 = x_2213;
}
lean_ctor_set(x_2214, 0, x_1);
lean_ctor_set(x_2214, 1, x_2212);
return x_2214;
}
}
else
{
lean_object* x_2215; lean_object* x_2216; 
lean_dec(x_2070);
lean_dec(x_2068);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_2215 = lean_ctor_get(x_2150, 0);
lean_inc(x_2215);
lean_dec(x_2150);
x_2216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2216, 0, x_2215);
lean_ctor_set(x_2216, 1, x_2147);
return x_2216;
}
}
}
else
{
uint8_t x_2217; 
lean_dec(x_2068);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_2217 = !lean_is_exclusive(x_2069);
if (x_2217 == 0)
{
return x_2069;
}
else
{
lean_object* x_2218; lean_object* x_2219; lean_object* x_2220; 
x_2218 = lean_ctor_get(x_2069, 0);
x_2219 = lean_ctor_get(x_2069, 1);
lean_inc(x_2219);
lean_inc(x_2218);
lean_dec(x_2069);
x_2220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2220, 0, x_2218);
lean_ctor_set(x_2220, 1, x_2219);
return x_2220;
}
}
}
block_2259:
{
lean_object* x_2223; 
lean_dec(x_2222);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_9);
x_2223 = l_Lean_Meta_getFunInfo(x_9, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_2223) == 0)
{
lean_object* x_2224; lean_object* x_2225; lean_object* x_2226; lean_object* x_2227; lean_object* x_2228; lean_object* x_2229; lean_object* x_2230; uint8_t x_2231; lean_object* x_2232; lean_object* x_2233; lean_object* x_2234; lean_object* x_2235; 
x_2224 = lean_ctor_get(x_2223, 0);
lean_inc(x_2224);
x_2225 = lean_ctor_get(x_2223, 1);
lean_inc(x_2225);
lean_dec(x_2223);
x_2226 = lean_ctor_get(x_2224, 0);
lean_inc(x_2226);
lean_dec(x_2224);
x_2227 = lean_array_get_size(x_10);
x_2228 = lean_unsigned_to_nat(0u);
x_2229 = lean_unsigned_to_nat(1u);
lean_inc(x_2227);
x_2230 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2230, 0, x_2228);
lean_ctor_set(x_2230, 1, x_2227);
lean_ctor_set(x_2230, 2, x_2229);
x_2231 = 0;
x_2232 = lean_box(x_2231);
lean_inc(x_10);
x_2233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2233, 0, x_10);
lean_ctor_set(x_2233, 1, x_2232);
x_2234 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_2230);
lean_inc(x_9);
lean_inc(x_1);
x_2235 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_2234, x_2226, x_2227, x_2230, x_2230, x_2233, x_2228, lean_box(0), lean_box(0), x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_2225);
if (lean_obj_tag(x_2235) == 0)
{
lean_object* x_2236; lean_object* x_2237; uint8_t x_2238; 
x_2236 = lean_ctor_get(x_2235, 0);
lean_inc(x_2236);
x_2237 = lean_ctor_get(x_2236, 1);
lean_inc(x_2237);
x_2238 = lean_unbox(x_2237);
lean_dec(x_2237);
if (x_2238 == 0)
{
uint8_t x_2239; 
lean_dec(x_2236);
lean_dec(x_9);
x_2239 = !lean_is_exclusive(x_2235);
if (x_2239 == 0)
{
lean_object* x_2240; 
x_2240 = lean_ctor_get(x_2235, 0);
lean_dec(x_2240);
lean_ctor_set(x_2235, 0, x_1);
return x_2235;
}
else
{
lean_object* x_2241; lean_object* x_2242; 
x_2241 = lean_ctor_get(x_2235, 1);
lean_inc(x_2241);
lean_dec(x_2235);
x_2242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2242, 0, x_1);
lean_ctor_set(x_2242, 1, x_2241);
return x_2242;
}
}
else
{
uint8_t x_2243; 
lean_dec(x_1);
x_2243 = !lean_is_exclusive(x_2235);
if (x_2243 == 0)
{
lean_object* x_2244; lean_object* x_2245; lean_object* x_2246; 
x_2244 = lean_ctor_get(x_2235, 0);
lean_dec(x_2244);
x_2245 = lean_ctor_get(x_2236, 0);
lean_inc(x_2245);
lean_dec(x_2236);
x_2246 = l_Lean_mkAppN(x_9, x_2245);
lean_dec(x_2245);
lean_ctor_set(x_2235, 0, x_2246);
return x_2235;
}
else
{
lean_object* x_2247; lean_object* x_2248; lean_object* x_2249; lean_object* x_2250; 
x_2247 = lean_ctor_get(x_2235, 1);
lean_inc(x_2247);
lean_dec(x_2235);
x_2248 = lean_ctor_get(x_2236, 0);
lean_inc(x_2248);
lean_dec(x_2236);
x_2249 = l_Lean_mkAppN(x_9, x_2248);
lean_dec(x_2248);
x_2250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2250, 0, x_2249);
lean_ctor_set(x_2250, 1, x_2247);
return x_2250;
}
}
}
else
{
uint8_t x_2251; 
lean_dec(x_9);
lean_dec(x_1);
x_2251 = !lean_is_exclusive(x_2235);
if (x_2251 == 0)
{
return x_2235;
}
else
{
lean_object* x_2252; lean_object* x_2253; lean_object* x_2254; 
x_2252 = lean_ctor_get(x_2235, 0);
x_2253 = lean_ctor_get(x_2235, 1);
lean_inc(x_2253);
lean_inc(x_2252);
lean_dec(x_2235);
x_2254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2254, 0, x_2252);
lean_ctor_set(x_2254, 1, x_2253);
return x_2254;
}
}
}
else
{
uint8_t x_2255; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2255 = !lean_is_exclusive(x_2223);
if (x_2255 == 0)
{
return x_2223;
}
else
{
lean_object* x_2256; lean_object* x_2257; lean_object* x_2258; 
x_2256 = lean_ctor_get(x_2223, 0);
x_2257 = lean_ctor_get(x_2223, 1);
lean_inc(x_2257);
lean_inc(x_2256);
lean_dec(x_2223);
x_2258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2258, 0, x_2256);
lean_ctor_set(x_2258, 1, x_2257);
return x_2258;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__12(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ptr_addr(x_4);
x_8 = lean_ptr_addr(x_1);
x_9 = lean_usize_dec_eq(x_7, x_8);
if (x_9 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_11; 
lean_inc(x_5);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_st_ref_take(x_3, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; size_t x_30; size_t x_31; size_t x_32; size_t x_33; size_t x_34; lean_object* x_35; uint8_t x_36; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
x_19 = lean_array_get_size(x_18);
x_20 = lean_ptr_addr(x_1);
x_21 = lean_usize_to_uint64(x_20);
x_22 = 11;
x_23 = lean_uint64_mix_hash(x_21, x_22);
x_24 = 32;
x_25 = lean_uint64_shift_right(x_23, x_24);
x_26 = lean_uint64_xor(x_23, x_25);
x_27 = 16;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = lean_uint64_to_usize(x_29);
x_31 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_32 = 1;
x_33 = lean_usize_sub(x_31, x_32);
x_34 = lean_usize_land(x_30, x_33);
x_35 = lean_array_uget(x_18, x_34);
x_36 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1(x_1, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_17, x_37);
lean_dec(x_17);
lean_inc(x_2);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_2);
lean_ctor_set(x_39, 2, x_35);
x_40 = lean_array_uset(x_18, x_34, x_39);
x_41 = lean_unsigned_to_nat(4u);
x_42 = lean_nat_mul(x_38, x_41);
x_43 = lean_unsigned_to_nat(3u);
x_44 = lean_nat_div(x_42, x_43);
lean_dec(x_42);
x_45 = lean_array_get_size(x_40);
x_46 = lean_nat_dec_le(x_44, x_45);
lean_dec(x_45);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__2(x_40);
lean_ctor_set(x_14, 1, x_47);
lean_ctor_set(x_14, 0, x_38);
x_48 = lean_st_ref_set(x_3, x_14, x_15);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
lean_ctor_set(x_48, 0, x_2);
return x_48;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_2);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
lean_object* x_53; uint8_t x_54; 
lean_ctor_set(x_14, 1, x_40);
lean_ctor_set(x_14, 0, x_38);
x_53 = lean_st_ref_set(x_3, x_14, x_15);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set(x_53, 0, x_2);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_2);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_58 = lean_box(0);
x_59 = lean_array_uset(x_18, x_34, x_58);
lean_inc(x_2);
x_60 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__6(x_1, x_2, x_35);
x_61 = lean_array_uset(x_59, x_34, x_60);
lean_ctor_set(x_14, 1, x_61);
x_62 = lean_st_ref_set(x_3, x_14, x_15);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_62, 0);
lean_dec(x_64);
lean_ctor_set(x_62, 0, x_2);
return x_62;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_2);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; size_t x_70; uint64_t x_71; uint64_t x_72; uint64_t x_73; uint64_t x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; size_t x_80; size_t x_81; size_t x_82; size_t x_83; size_t x_84; lean_object* x_85; uint8_t x_86; 
x_67 = lean_ctor_get(x_14, 0);
x_68 = lean_ctor_get(x_14, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_14);
x_69 = lean_array_get_size(x_68);
x_70 = lean_ptr_addr(x_1);
x_71 = lean_usize_to_uint64(x_70);
x_72 = 11;
x_73 = lean_uint64_mix_hash(x_71, x_72);
x_74 = 32;
x_75 = lean_uint64_shift_right(x_73, x_74);
x_76 = lean_uint64_xor(x_73, x_75);
x_77 = 16;
x_78 = lean_uint64_shift_right(x_76, x_77);
x_79 = lean_uint64_xor(x_76, x_78);
x_80 = lean_uint64_to_usize(x_79);
x_81 = lean_usize_of_nat(x_69);
lean_dec(x_69);
x_82 = 1;
x_83 = lean_usize_sub(x_81, x_82);
x_84 = lean_usize_land(x_80, x_83);
x_85 = lean_array_uget(x_68, x_84);
x_86 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1(x_1, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_nat_add(x_67, x_87);
lean_dec(x_67);
lean_inc(x_2);
x_89 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_89, 0, x_1);
lean_ctor_set(x_89, 1, x_2);
lean_ctor_set(x_89, 2, x_85);
x_90 = lean_array_uset(x_68, x_84, x_89);
x_91 = lean_unsigned_to_nat(4u);
x_92 = lean_nat_mul(x_88, x_91);
x_93 = lean_unsigned_to_nat(3u);
x_94 = lean_nat_div(x_92, x_93);
lean_dec(x_92);
x_95 = lean_array_get_size(x_90);
x_96 = lean_nat_dec_le(x_94, x_95);
lean_dec(x_95);
lean_dec(x_94);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_97 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__2(x_90);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_88);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_st_ref_set(x_3, x_98, x_15);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_101 = x_99;
} else {
 lean_dec_ref(x_99);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_2);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_88);
lean_ctor_set(x_103, 1, x_90);
x_104 = lean_st_ref_set(x_3, x_103, x_15);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_106 = x_104;
} else {
 lean_dec_ref(x_104);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_2);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_108 = lean_box(0);
x_109 = lean_array_uset(x_68, x_84, x_108);
lean_inc(x_2);
x_110 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__6(x_1, x_2, x_85);
x_111 = lean_array_uset(x_109, x_84, x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_67);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_st_ref_set(x_3, x_112, x_15);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_115 = x_113;
} else {
 lean_dec_ref(x_113);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_2);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; size_t x_19; size_t x_20; uint8_t x_21; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Lean_Expr_forallE___override(x_1, x_2, x_3, x_4);
x_19 = lean_ptr_addr(x_2);
lean_dec(x_2);
x_20 = lean_ptr_addr(x_5);
x_21 = lean_usize_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_3);
x_22 = l_Lean_Expr_forallE___override(x_1, x_5, x_7, x_4);
x_23 = lean_apply_11(x_6, x_22, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_23;
}
else
{
size_t x_24; size_t x_25; uint8_t x_26; 
x_24 = lean_ptr_addr(x_3);
lean_dec(x_3);
x_25 = lean_ptr_addr(x_7);
x_26 = lean_usize_dec_eq(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_18);
x_27 = l_Lean_Expr_forallE___override(x_1, x_5, x_7, x_4);
x_28 = lean_apply_11(x_6, x_27, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_4, x_4);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_18);
x_30 = l_Lean_Expr_forallE___override(x_1, x_5, x_7, x_4);
x_31 = lean_apply_11(x_6, x_30, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_31;
}
else
{
lean_object* x_32; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_32 = lean_apply_11(x_6, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_32;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.Canon", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Grind.Canon.canonImpl.visit", 37, 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__1;
x_2 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__2;
x_3 = lean_unsigned_to_nat(192u);
x_4 = lean_unsigned_to_nat(13u);
x_5 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_16);
x_18 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__5;
lean_inc(x_17);
x_19 = lean_mk_array(x_17, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_17, x_20);
lean_dec(x_17);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_n(x_4, 2);
lean_inc_n(x_3, 2);
lean_inc_n(x_1, 2);
x_22 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11(x_1, x_2, x_3, x_4, x_4, x_3, x_4, x_3, x_1, x_19, x_21, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__1(x_1, x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_24);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_22);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
case 7:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 2);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_34 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__1___boxed), 12, 1);
lean_closure_set(x_34, 0, x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_31);
x_35 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_31, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Expr_hasLooseBVars(x_32);
if (x_38 == 0)
{
lean_object* x_39; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_32);
x_39 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_32, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__2(x_30, x_31, x_32, x_33, x_36, x_34, x_40, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_41);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_43 = !lean_is_exclusive(x_39);
if (x_43 == 0)
{
return x_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_39, 0);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_39);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; 
lean_inc(x_32);
x_47 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__2(x_30, x_31, x_32, x_33, x_36, x_34, x_32, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_37);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_48 = !lean_is_exclusive(x_35);
if (x_48 == 0)
{
return x_35;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_35, 0);
x_50 = lean_ctor_get(x_35, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_35);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
default: 
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__4;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_53 = l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7(x_52, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__1(x_1, x_54, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_55);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_53);
if (x_57 == 0)
{
return x_53;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_53, 0);
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_53);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift), 3, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_st_ref_get(x_3, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; size_t x_29; size_t x_30; size_t x_31; size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_array_get_size(x_17);
x_19 = lean_ptr_addr(x_1);
x_20 = lean_usize_to_uint64(x_19);
x_21 = 11;
x_22 = lean_uint64_mix_hash(x_20, x_21);
x_23 = 32;
x_24 = lean_uint64_shift_right(x_22, x_23);
x_25 = lean_uint64_xor(x_22, x_24);
x_26 = 16;
x_27 = lean_uint64_shift_right(x_25, x_26);
x_28 = lean_uint64_xor(x_25, x_27);
x_29 = lean_uint64_to_usize(x_28);
x_30 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_31 = 1;
x_32 = lean_usize_sub(x_30, x_31);
x_33 = lean_usize_land(x_29, x_32);
x_34 = lean_array_uget(x_17, x_33);
lean_dec(x_17);
x_35 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__12(x_1, x_34);
lean_dec(x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_free_object(x_13);
x_36 = l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__5;
x_37 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
x_38 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4___closed__1;
x_39 = lean_box(0);
x_40 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3(x_1, x_36, x_37, x_38, x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
return x_40;
}
else
{
lean_object* x_41; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_41 = lean_ctor_get(x_35, 0);
lean_inc(x_41);
lean_dec(x_35);
lean_ctor_set(x_13, 0, x_41);
return x_13;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; size_t x_56; size_t x_57; size_t x_58; size_t x_59; size_t x_60; lean_object* x_61; lean_object* x_62; 
x_42 = lean_ctor_get(x_13, 0);
x_43 = lean_ctor_get(x_13, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_13);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_array_get_size(x_44);
x_46 = lean_ptr_addr(x_1);
x_47 = lean_usize_to_uint64(x_46);
x_48 = 11;
x_49 = lean_uint64_mix_hash(x_47, x_48);
x_50 = 32;
x_51 = lean_uint64_shift_right(x_49, x_50);
x_52 = lean_uint64_xor(x_49, x_51);
x_53 = 16;
x_54 = lean_uint64_shift_right(x_52, x_53);
x_55 = lean_uint64_xor(x_52, x_54);
x_56 = lean_uint64_to_usize(x_55);
x_57 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_58 = 1;
x_59 = lean_usize_sub(x_57, x_58);
x_60 = lean_usize_land(x_56, x_59);
x_61 = lean_array_uget(x_44, x_60);
lean_dec(x_44);
x_62 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__12(x_1, x_61);
lean_dec(x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__5;
x_64 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
x_65 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4___closed__1;
x_66 = lean_box(0);
x_67 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3(x_1, x_63, x_64, x_65, x_66, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_43);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_68 = lean_ctor_get(x_62, 0);
lean_inc(x_68);
lean_dec(x_62);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_43);
return x_69;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = l_Lean_Expr_isApp(x_1);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isForall(x_1);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4(x_1, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__1(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; lean_object* x_20; 
x_19 = lean_unbox(x_7);
lean_dec(x_7);
x_20 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_8);
lean_dec(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__4___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
_start:
{
lean_object* x_28; 
x_28 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
lean_dec(x_3);
return x_28;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
lean_object* x_29 = _args[28];
_start:
{
lean_object* x_30; 
x_30 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29);
return x_30;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
lean_object* x_22; 
x_22 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__12___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__12(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_4);
lean_dec(x_4);
x_19 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__2(x_1, x_2, x_3, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonImpl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = l_Lean_mkPtrMap___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_Lean_Meta_Grind_Canon_canonImpl___closed__1;
x_12 = lean_st_mk_ref(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_13);
x_15 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_1, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_13, x_17);
lean_dec(x_13);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_16);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_13);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_canon_unsafe__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Canon_canonImpl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_canon___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Canon_canonImpl(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_canon(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__2;
x_12 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_Meta_Grind_Canon_canonImpl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 1);
x_19 = lean_ctor_get(x_12, 0);
lean_dec(x_19);
x_20 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_1);
x_22 = l_Lean_MessageData_ofExpr(x_1);
x_23 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10;
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_22);
lean_ctor_set(x_12, 0, x_23);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_11, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_Meta_Grind_Canon_canonImpl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
return x_27;
}
else
{
uint8_t x_28; 
lean_free_object(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
lean_dec(x_12);
x_33 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
lean_inc(x_1);
x_35 = l_Lean_MessageData_ofExpr(x_1);
x_36 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_11, x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_34);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l_Lean_Meta_Grind_Canon_canonImpl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_44 = x_33;
} else {
 lean_dec_ref(x_33);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_canon___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_canon___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
lean_object* initialize_Init_Grind_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_FunInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FVarSubset(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_PtrSet(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FVarSubset(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Canon(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_FunInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FVarSubset(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_PtrSet(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FVarSubset(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__1);
l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__2);
l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__3);
l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__4);
l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__5);
l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__6);
l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__7);
l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__8);
l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__9 = _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__9);
l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__10 = _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__10);
l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__11 = _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__11);
l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__12 = _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__12);
l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__13 = _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__13();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__2___closed__13);
l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__3___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__3___closed__1();
l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___closed__1);
l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___closed__2);
l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__1 = _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__1();
l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__2 = _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__2();
l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__1);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__1 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__1);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__2 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__2);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__3 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__3();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__3);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__4 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__4();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__4);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__5 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__5();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__5);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__6 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__6();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__6);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__7 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__7();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__7);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__8 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__8();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__8);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__9 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__9();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__9);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___closed__1 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___closed__1);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___closed__2 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___closed__2);
l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__1 = _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__1);
l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__2 = _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__2);
l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__3 = _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__3);
l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__4 = _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__4);
l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__5 = _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__5);
l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__6 = _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__6);
l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__7 = _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__7);
l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__8 = _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__8);
l_Lean_Meta_Grind_Canon_canonElemCore___lambda__3___closed__1 = _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonElemCore___lambda__3___closed__1);
l_Lean_Meta_Grind_Canon_canonInst___closed__1 = _init_l_Lean_Meta_Grind_Canon_canonInst___closed__1();
l_Lean_Meta_Grind_Canon_canonImplicit___closed__1 = _init_l_Lean_Meta_Grind_Canon_canonImplicit___closed__1();
l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___closed__1);
l_Lean_Meta_Grind_Canon_instInhabitedShouldCanonResult = _init_l_Lean_Meta_Grind_Canon_instInhabitedShouldCanonResult();
l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__1 = _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__1);
l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__2 = _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__2);
l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__3 = _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__3);
l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__4 = _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__4);
l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__5 = _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__5);
l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__6 = _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__6);
l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__7 = _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__7);
l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__8 = _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__8);
l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__1 = _init_l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__1();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__1);
l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__2 = _init_l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__2();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__2);
l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__3 = _init_l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__3();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__3);
l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__4 = _init_l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__4();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__4);
l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__5 = _init_l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__5();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__5);
l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__6 = _init_l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__6();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__6);
l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__1 = _init_l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__1();
l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__2 = _init_l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__2);
l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__1 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__1();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__1);
l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__2 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__2();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__2);
l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__3 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__3();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__3);
l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__4 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__4();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__4);
l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__5 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__5();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__5);
l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__6 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__6();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__6);
l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__3);
l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__4 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__4);
l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5);
l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__1 = _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__1);
l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__2 = _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__2);
l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__3 = _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__3);
l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__4 = _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__4);
l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__5 = _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__5);
l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4___closed__1 = _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4___closed__1);
l_Lean_Meta_Grind_Canon_canonImpl___closed__1 = _init_l_Lean_Meta_Grind_Canon_canonImpl___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonImpl___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
