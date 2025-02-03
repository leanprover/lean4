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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
x_26 = lean_ctor_get(x_12, 2);
x_27 = lean_ctor_get(x_12, 3);
x_28 = lean_ctor_get(x_12, 4);
x_29 = lean_ctor_get(x_12, 5);
x_30 = lean_ctor_get(x_12, 6);
x_31 = lean_ctor_get_uint8(x_12, sizeof(void*)*26);
x_32 = lean_ctor_get(x_12, 7);
x_33 = lean_ctor_get(x_12, 8);
x_34 = lean_ctor_get(x_12, 9);
x_35 = lean_ctor_get(x_12, 10);
x_36 = lean_ctor_get(x_12, 11);
x_37 = lean_ctor_get(x_12, 12);
x_38 = lean_ctor_get(x_12, 13);
x_39 = lean_ctor_get(x_12, 14);
x_40 = lean_ctor_get(x_12, 15);
x_41 = lean_ctor_get(x_12, 16);
x_42 = lean_ctor_get(x_12, 17);
x_43 = lean_ctor_get(x_12, 18);
x_44 = lean_ctor_get(x_12, 19);
x_45 = lean_ctor_get(x_12, 20);
x_46 = lean_ctor_get(x_12, 21);
x_47 = lean_ctor_get(x_12, 22);
x_48 = lean_ctor_get(x_12, 23);
x_49 = lean_ctor_get(x_12, 24);
x_50 = lean_ctor_get(x_12, 25);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
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
x_51 = lean_apply_1(x_1, x_25);
x_52 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_52, 0, x_24);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_26);
lean_ctor_set(x_52, 3, x_27);
lean_ctor_set(x_52, 4, x_28);
lean_ctor_set(x_52, 5, x_29);
lean_ctor_set(x_52, 6, x_30);
lean_ctor_set(x_52, 7, x_32);
lean_ctor_set(x_52, 8, x_33);
lean_ctor_set(x_52, 9, x_34);
lean_ctor_set(x_52, 10, x_35);
lean_ctor_set(x_52, 11, x_36);
lean_ctor_set(x_52, 12, x_37);
lean_ctor_set(x_52, 13, x_38);
lean_ctor_set(x_52, 14, x_39);
lean_ctor_set(x_52, 15, x_40);
lean_ctor_set(x_52, 16, x_41);
lean_ctor_set(x_52, 17, x_42);
lean_ctor_set(x_52, 18, x_43);
lean_ctor_set(x_52, 19, x_44);
lean_ctor_set(x_52, 20, x_45);
lean_ctor_set(x_52, 21, x_46);
lean_ctor_set(x_52, 22, x_47);
lean_ctor_set(x_52, 23, x_48);
lean_ctor_set(x_52, 24, x_49);
lean_ctor_set(x_52, 25, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*26, x_31);
x_53 = lean_st_ref_set(x_2, x_52, x_13);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
x_56 = lean_box(0);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
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
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_150 = lean_ctor_get(x_29, 0);
x_151 = lean_ctor_get(x_29, 2);
x_152 = lean_ctor_get(x_29, 3);
x_153 = lean_ctor_get(x_29, 4);
x_154 = lean_ctor_get(x_29, 5);
x_155 = lean_ctor_get(x_29, 6);
x_156 = lean_ctor_get_uint8(x_29, sizeof(void*)*26);
x_157 = lean_ctor_get(x_29, 7);
x_158 = lean_ctor_get(x_29, 8);
x_159 = lean_ctor_get(x_29, 9);
x_160 = lean_ctor_get(x_29, 10);
x_161 = lean_ctor_get(x_29, 11);
x_162 = lean_ctor_get(x_29, 12);
x_163 = lean_ctor_get(x_29, 13);
x_164 = lean_ctor_get(x_29, 14);
x_165 = lean_ctor_get(x_29, 15);
x_166 = lean_ctor_get(x_29, 16);
x_167 = lean_ctor_get(x_29, 17);
x_168 = lean_ctor_get(x_29, 18);
x_169 = lean_ctor_get(x_29, 19);
x_170 = lean_ctor_get(x_29, 20);
x_171 = lean_ctor_get(x_29, 21);
x_172 = lean_ctor_get(x_29, 22);
x_173 = lean_ctor_get(x_29, 23);
x_174 = lean_ctor_get(x_29, 24);
x_175 = lean_ctor_get(x_29, 25);
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
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
x_176 = lean_ctor_get(x_30, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_30, 1);
lean_inc(x_177);
x_178 = lean_ctor_get(x_30, 2);
lean_inc(x_178);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 x_179 = x_30;
} else {
 lean_dec_ref(x_30);
 x_179 = lean_box(0);
}
lean_inc(x_4);
lean_inc(x_3);
x_180 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_177, x_3, x_4);
if (lean_is_scalar(x_179)) {
 x_181 = lean_alloc_ctor(0, 3, 0);
} else {
 x_181 = x_179;
}
lean_ctor_set(x_181, 0, x_176);
lean_ctor_set(x_181, 1, x_180);
lean_ctor_set(x_181, 2, x_178);
x_182 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_182, 0, x_150);
lean_ctor_set(x_182, 1, x_181);
lean_ctor_set(x_182, 2, x_151);
lean_ctor_set(x_182, 3, x_152);
lean_ctor_set(x_182, 4, x_153);
lean_ctor_set(x_182, 5, x_154);
lean_ctor_set(x_182, 6, x_155);
lean_ctor_set(x_182, 7, x_157);
lean_ctor_set(x_182, 8, x_158);
lean_ctor_set(x_182, 9, x_159);
lean_ctor_set(x_182, 10, x_160);
lean_ctor_set(x_182, 11, x_161);
lean_ctor_set(x_182, 12, x_162);
lean_ctor_set(x_182, 13, x_163);
lean_ctor_set(x_182, 14, x_164);
lean_ctor_set(x_182, 15, x_165);
lean_ctor_set(x_182, 16, x_166);
lean_ctor_set(x_182, 17, x_167);
lean_ctor_set(x_182, 18, x_168);
lean_ctor_set(x_182, 19, x_169);
lean_ctor_set(x_182, 20, x_170);
lean_ctor_set(x_182, 21, x_171);
lean_ctor_set(x_182, 22, x_172);
lean_ctor_set(x_182, 23, x_173);
lean_ctor_set(x_182, 24, x_174);
lean_ctor_set(x_182, 25, x_175);
lean_ctor_set_uint8(x_182, sizeof(void*)*26, x_156);
x_183 = lean_st_ref_set(x_7, x_182, x_32);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_185 = x_183;
} else {
 lean_dec_ref(x_183);
 x_185 = lean_box(0);
}
x_186 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__4;
x_187 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_186, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_184);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_unbox(x_188);
lean_dec(x_188);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_185);
lean_free_object(x_28);
lean_dec(x_3);
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
lean_dec(x_187);
x_191 = lean_box(0);
x_192 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_4, x_191, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_190);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_187, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_194 = x_187;
} else {
 lean_dec_ref(x_187);
 x_194 = lean_box(0);
}
x_195 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_193);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_196 = lean_ctor_get(x_195, 1);
lean_inc(x_196);
lean_dec(x_195);
x_197 = l_Lean_MessageData_ofExpr(x_3);
x_198 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__6;
if (lean_is_scalar(x_194)) {
 x_199 = lean_alloc_ctor(7, 2, 0);
} else {
 x_199 = x_194;
 lean_ctor_set_tag(x_199, 7);
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_197);
x_200 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__8;
if (lean_is_scalar(x_185)) {
 x_201 = lean_alloc_ctor(7, 2, 0);
} else {
 x_201 = x_185;
 lean_ctor_set_tag(x_201, 7);
}
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
lean_inc(x_4);
x_202 = l_Lean_MessageData_ofExpr(x_4);
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_202);
lean_ctor_set(x_28, 0, x_201);
x_203 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10;
x_204 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_204, 0, x_28);
lean_ctor_set(x_204, 1, x_203);
x_205 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_186, x_204, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_196);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_208 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_4, x_206, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_207);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_206);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_194);
lean_dec(x_185);
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
x_209 = lean_ctor_get(x_195, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_195, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_211 = x_195;
} else {
 lean_dec_ref(x_195);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_210);
return x_212;
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_213 = lean_ctor_get(x_28, 1);
lean_inc(x_213);
lean_dec(x_28);
x_214 = lean_ctor_get(x_29, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_29, 2);
lean_inc(x_215);
x_216 = lean_ctor_get(x_29, 3);
lean_inc(x_216);
x_217 = lean_ctor_get(x_29, 4);
lean_inc(x_217);
x_218 = lean_ctor_get(x_29, 5);
lean_inc(x_218);
x_219 = lean_ctor_get(x_29, 6);
lean_inc(x_219);
x_220 = lean_ctor_get_uint8(x_29, sizeof(void*)*26);
x_221 = lean_ctor_get(x_29, 7);
lean_inc(x_221);
x_222 = lean_ctor_get(x_29, 8);
lean_inc(x_222);
x_223 = lean_ctor_get(x_29, 9);
lean_inc(x_223);
x_224 = lean_ctor_get(x_29, 10);
lean_inc(x_224);
x_225 = lean_ctor_get(x_29, 11);
lean_inc(x_225);
x_226 = lean_ctor_get(x_29, 12);
lean_inc(x_226);
x_227 = lean_ctor_get(x_29, 13);
lean_inc(x_227);
x_228 = lean_ctor_get(x_29, 14);
lean_inc(x_228);
x_229 = lean_ctor_get(x_29, 15);
lean_inc(x_229);
x_230 = lean_ctor_get(x_29, 16);
lean_inc(x_230);
x_231 = lean_ctor_get(x_29, 17);
lean_inc(x_231);
x_232 = lean_ctor_get(x_29, 18);
lean_inc(x_232);
x_233 = lean_ctor_get(x_29, 19);
lean_inc(x_233);
x_234 = lean_ctor_get(x_29, 20);
lean_inc(x_234);
x_235 = lean_ctor_get(x_29, 21);
lean_inc(x_235);
x_236 = lean_ctor_get(x_29, 22);
lean_inc(x_236);
x_237 = lean_ctor_get(x_29, 23);
lean_inc(x_237);
x_238 = lean_ctor_get(x_29, 24);
lean_inc(x_238);
x_239 = lean_ctor_get(x_29, 25);
lean_inc(x_239);
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
 lean_ctor_release(x_29, 15);
 lean_ctor_release(x_29, 16);
 lean_ctor_release(x_29, 17);
 lean_ctor_release(x_29, 18);
 lean_ctor_release(x_29, 19);
 lean_ctor_release(x_29, 20);
 lean_ctor_release(x_29, 21);
 lean_ctor_release(x_29, 22);
 lean_ctor_release(x_29, 23);
 lean_ctor_release(x_29, 24);
 lean_ctor_release(x_29, 25);
 x_240 = x_29;
} else {
 lean_dec_ref(x_29);
 x_240 = lean_box(0);
}
x_241 = lean_ctor_get(x_30, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_30, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_30, 2);
lean_inc(x_243);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 x_244 = x_30;
} else {
 lean_dec_ref(x_30);
 x_244 = lean_box(0);
}
lean_inc(x_4);
lean_inc(x_3);
x_245 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_242, x_3, x_4);
if (lean_is_scalar(x_244)) {
 x_246 = lean_alloc_ctor(0, 3, 0);
} else {
 x_246 = x_244;
}
lean_ctor_set(x_246, 0, x_241);
lean_ctor_set(x_246, 1, x_245);
lean_ctor_set(x_246, 2, x_243);
if (lean_is_scalar(x_240)) {
 x_247 = lean_alloc_ctor(0, 26, 1);
} else {
 x_247 = x_240;
}
lean_ctor_set(x_247, 0, x_214);
lean_ctor_set(x_247, 1, x_246);
lean_ctor_set(x_247, 2, x_215);
lean_ctor_set(x_247, 3, x_216);
lean_ctor_set(x_247, 4, x_217);
lean_ctor_set(x_247, 5, x_218);
lean_ctor_set(x_247, 6, x_219);
lean_ctor_set(x_247, 7, x_221);
lean_ctor_set(x_247, 8, x_222);
lean_ctor_set(x_247, 9, x_223);
lean_ctor_set(x_247, 10, x_224);
lean_ctor_set(x_247, 11, x_225);
lean_ctor_set(x_247, 12, x_226);
lean_ctor_set(x_247, 13, x_227);
lean_ctor_set(x_247, 14, x_228);
lean_ctor_set(x_247, 15, x_229);
lean_ctor_set(x_247, 16, x_230);
lean_ctor_set(x_247, 17, x_231);
lean_ctor_set(x_247, 18, x_232);
lean_ctor_set(x_247, 19, x_233);
lean_ctor_set(x_247, 20, x_234);
lean_ctor_set(x_247, 21, x_235);
lean_ctor_set(x_247, 22, x_236);
lean_ctor_set(x_247, 23, x_237);
lean_ctor_set(x_247, 24, x_238);
lean_ctor_set(x_247, 25, x_239);
lean_ctor_set_uint8(x_247, sizeof(void*)*26, x_220);
x_248 = lean_st_ref_set(x_7, x_247, x_213);
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_250 = x_248;
} else {
 lean_dec_ref(x_248);
 x_250 = lean_box(0);
}
x_251 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__4;
x_252 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_251, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_249);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_unbox(x_253);
lean_dec(x_253);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_250);
lean_dec(x_3);
x_255 = lean_ctor_get(x_252, 1);
lean_inc(x_255);
lean_dec(x_252);
x_256 = lean_box(0);
x_257 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_4, x_256, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_255);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_257;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_252, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_259 = x_252;
} else {
 lean_dec_ref(x_252);
 x_259 = lean_box(0);
}
x_260 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_258);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_261 = lean_ctor_get(x_260, 1);
lean_inc(x_261);
lean_dec(x_260);
x_262 = l_Lean_MessageData_ofExpr(x_3);
x_263 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__6;
if (lean_is_scalar(x_259)) {
 x_264 = lean_alloc_ctor(7, 2, 0);
} else {
 x_264 = x_259;
 lean_ctor_set_tag(x_264, 7);
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_262);
x_265 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__8;
if (lean_is_scalar(x_250)) {
 x_266 = lean_alloc_ctor(7, 2, 0);
} else {
 x_266 = x_250;
 lean_ctor_set_tag(x_266, 7);
}
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
lean_inc(x_4);
x_267 = l_Lean_MessageData_ofExpr(x_4);
x_268 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_267);
x_269 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10;
x_270 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
x_271 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_251, x_270, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_261);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
x_274 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_4, x_272, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_273);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_272);
return x_274;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_259);
lean_dec(x_250);
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
x_275 = lean_ctor_get(x_260, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_260, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 x_277 = x_260;
} else {
 lean_dec_ref(x_260);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(1, 2, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_275);
lean_ctor_set(x_278, 1, x_276);
return x_278;
}
}
}
}
}
else
{
uint8_t x_279; 
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
x_279 = !lean_is_exclusive(x_18);
if (x_279 == 0)
{
return x_18;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_18, 0);
x_281 = lean_ctor_get(x_18, 1);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_18);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
return x_282;
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
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_205 = lean_ctor_get(x_74, 0);
x_206 = lean_ctor_get(x_74, 2);
x_207 = lean_ctor_get(x_74, 3);
x_208 = lean_ctor_get(x_74, 4);
x_209 = lean_ctor_get(x_74, 5);
x_210 = lean_ctor_get(x_74, 6);
x_211 = lean_ctor_get_uint8(x_74, sizeof(void*)*26);
x_212 = lean_ctor_get(x_74, 7);
x_213 = lean_ctor_get(x_74, 8);
x_214 = lean_ctor_get(x_74, 9);
x_215 = lean_ctor_get(x_74, 10);
x_216 = lean_ctor_get(x_74, 11);
x_217 = lean_ctor_get(x_74, 12);
x_218 = lean_ctor_get(x_74, 13);
x_219 = lean_ctor_get(x_74, 14);
x_220 = lean_ctor_get(x_74, 15);
x_221 = lean_ctor_get(x_74, 16);
x_222 = lean_ctor_get(x_74, 17);
x_223 = lean_ctor_get(x_74, 18);
x_224 = lean_ctor_get(x_74, 19);
x_225 = lean_ctor_get(x_74, 20);
x_226 = lean_ctor_get(x_74, 21);
x_227 = lean_ctor_get(x_74, 22);
x_228 = lean_ctor_get(x_74, 23);
x_229 = lean_ctor_get(x_74, 24);
x_230 = lean_ctor_get(x_74, 25);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
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
x_231 = lean_ctor_get(x_75, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_75, 1);
lean_inc(x_232);
x_233 = lean_ctor_get(x_75, 2);
lean_inc(x_233);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 x_234 = x_75;
} else {
 lean_dec_ref(x_75);
 x_234 = lean_box(0);
}
lean_inc(x_34);
lean_inc(x_2);
x_235 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_232, x_2, x_34);
if (lean_is_scalar(x_234)) {
 x_236 = lean_alloc_ctor(0, 3, 0);
} else {
 x_236 = x_234;
}
lean_ctor_set(x_236, 0, x_231);
lean_ctor_set(x_236, 1, x_235);
lean_ctor_set(x_236, 2, x_233);
x_237 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_237, 0, x_205);
lean_ctor_set(x_237, 1, x_236);
lean_ctor_set(x_237, 2, x_206);
lean_ctor_set(x_237, 3, x_207);
lean_ctor_set(x_237, 4, x_208);
lean_ctor_set(x_237, 5, x_209);
lean_ctor_set(x_237, 6, x_210);
lean_ctor_set(x_237, 7, x_212);
lean_ctor_set(x_237, 8, x_213);
lean_ctor_set(x_237, 9, x_214);
lean_ctor_set(x_237, 10, x_215);
lean_ctor_set(x_237, 11, x_216);
lean_ctor_set(x_237, 12, x_217);
lean_ctor_set(x_237, 13, x_218);
lean_ctor_set(x_237, 14, x_219);
lean_ctor_set(x_237, 15, x_220);
lean_ctor_set(x_237, 16, x_221);
lean_ctor_set(x_237, 17, x_222);
lean_ctor_set(x_237, 18, x_223);
lean_ctor_set(x_237, 19, x_224);
lean_ctor_set(x_237, 20, x_225);
lean_ctor_set(x_237, 21, x_226);
lean_ctor_set(x_237, 22, x_227);
lean_ctor_set(x_237, 23, x_228);
lean_ctor_set(x_237, 24, x_229);
lean_ctor_set(x_237, 25, x_230);
lean_ctor_set_uint8(x_237, sizeof(void*)*26, x_211);
x_238 = lean_st_ref_set(x_12, x_237, x_77);
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_240 = x_238;
} else {
 lean_dec_ref(x_238);
 x_240 = lean_box(0);
}
x_241 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__4;
x_242 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_241, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_239);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_unbox(x_243);
lean_dec(x_243);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_240);
lean_free_object(x_73);
lean_free_object(x_22);
x_245 = lean_ctor_get(x_242, 1);
lean_inc(x_245);
lean_dec(x_242);
x_246 = lean_box(0);
x_247 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_34, x_246, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_245);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_25 = x_248;
x_26 = x_249;
goto block_31;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_242, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_251 = x_242;
} else {
 lean_dec_ref(x_242);
 x_251 = lean_box(0);
}
x_252 = l_Lean_Meta_Grind_updateLastTag(x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_250);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
lean_dec(x_252);
lean_inc(x_2);
x_254 = l_Lean_MessageData_ofExpr(x_2);
x_255 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___closed__2;
if (lean_is_scalar(x_251)) {
 x_256 = lean_alloc_ctor(7, 2, 0);
} else {
 x_256 = x_251;
 lean_ctor_set_tag(x_256, 7);
}
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_254);
x_257 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__8;
if (lean_is_scalar(x_240)) {
 x_258 = lean_alloc_ctor(7, 2, 0);
} else {
 x_258 = x_240;
 lean_ctor_set_tag(x_258, 7);
}
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
lean_inc(x_34);
x_259 = l_Lean_MessageData_ofExpr(x_34);
lean_ctor_set_tag(x_73, 7);
lean_ctor_set(x_73, 1, x_259);
lean_ctor_set(x_73, 0, x_258);
x_260 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_260);
lean_ctor_set(x_22, 0, x_73);
x_261 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_241, x_22, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_253);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_264 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_34, x_262, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_263);
lean_dec(x_262);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_25 = x_265;
x_26 = x_266;
goto block_31;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_251);
lean_dec(x_240);
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
x_267 = lean_ctor_get(x_252, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_252, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_269 = x_252;
} else {
 lean_dec_ref(x_252);
 x_269 = lean_box(0);
}
if (lean_is_scalar(x_269)) {
 x_270 = lean_alloc_ctor(1, 2, 0);
} else {
 x_270 = x_269;
}
lean_ctor_set(x_270, 0, x_267);
lean_ctor_set(x_270, 1, x_268);
return x_270;
}
}
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; 
x_271 = lean_ctor_get(x_73, 1);
lean_inc(x_271);
lean_dec(x_73);
x_272 = lean_ctor_get(x_74, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_74, 2);
lean_inc(x_273);
x_274 = lean_ctor_get(x_74, 3);
lean_inc(x_274);
x_275 = lean_ctor_get(x_74, 4);
lean_inc(x_275);
x_276 = lean_ctor_get(x_74, 5);
lean_inc(x_276);
x_277 = lean_ctor_get(x_74, 6);
lean_inc(x_277);
x_278 = lean_ctor_get_uint8(x_74, sizeof(void*)*26);
x_279 = lean_ctor_get(x_74, 7);
lean_inc(x_279);
x_280 = lean_ctor_get(x_74, 8);
lean_inc(x_280);
x_281 = lean_ctor_get(x_74, 9);
lean_inc(x_281);
x_282 = lean_ctor_get(x_74, 10);
lean_inc(x_282);
x_283 = lean_ctor_get(x_74, 11);
lean_inc(x_283);
x_284 = lean_ctor_get(x_74, 12);
lean_inc(x_284);
x_285 = lean_ctor_get(x_74, 13);
lean_inc(x_285);
x_286 = lean_ctor_get(x_74, 14);
lean_inc(x_286);
x_287 = lean_ctor_get(x_74, 15);
lean_inc(x_287);
x_288 = lean_ctor_get(x_74, 16);
lean_inc(x_288);
x_289 = lean_ctor_get(x_74, 17);
lean_inc(x_289);
x_290 = lean_ctor_get(x_74, 18);
lean_inc(x_290);
x_291 = lean_ctor_get(x_74, 19);
lean_inc(x_291);
x_292 = lean_ctor_get(x_74, 20);
lean_inc(x_292);
x_293 = lean_ctor_get(x_74, 21);
lean_inc(x_293);
x_294 = lean_ctor_get(x_74, 22);
lean_inc(x_294);
x_295 = lean_ctor_get(x_74, 23);
lean_inc(x_295);
x_296 = lean_ctor_get(x_74, 24);
lean_inc(x_296);
x_297 = lean_ctor_get(x_74, 25);
lean_inc(x_297);
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
 lean_ctor_release(x_74, 15);
 lean_ctor_release(x_74, 16);
 lean_ctor_release(x_74, 17);
 lean_ctor_release(x_74, 18);
 lean_ctor_release(x_74, 19);
 lean_ctor_release(x_74, 20);
 lean_ctor_release(x_74, 21);
 lean_ctor_release(x_74, 22);
 lean_ctor_release(x_74, 23);
 lean_ctor_release(x_74, 24);
 lean_ctor_release(x_74, 25);
 x_298 = x_74;
} else {
 lean_dec_ref(x_74);
 x_298 = lean_box(0);
}
x_299 = lean_ctor_get(x_75, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_75, 1);
lean_inc(x_300);
x_301 = lean_ctor_get(x_75, 2);
lean_inc(x_301);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 x_302 = x_75;
} else {
 lean_dec_ref(x_75);
 x_302 = lean_box(0);
}
lean_inc(x_34);
lean_inc(x_2);
x_303 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_300, x_2, x_34);
if (lean_is_scalar(x_302)) {
 x_304 = lean_alloc_ctor(0, 3, 0);
} else {
 x_304 = x_302;
}
lean_ctor_set(x_304, 0, x_299);
lean_ctor_set(x_304, 1, x_303);
lean_ctor_set(x_304, 2, x_301);
if (lean_is_scalar(x_298)) {
 x_305 = lean_alloc_ctor(0, 26, 1);
} else {
 x_305 = x_298;
}
lean_ctor_set(x_305, 0, x_272);
lean_ctor_set(x_305, 1, x_304);
lean_ctor_set(x_305, 2, x_273);
lean_ctor_set(x_305, 3, x_274);
lean_ctor_set(x_305, 4, x_275);
lean_ctor_set(x_305, 5, x_276);
lean_ctor_set(x_305, 6, x_277);
lean_ctor_set(x_305, 7, x_279);
lean_ctor_set(x_305, 8, x_280);
lean_ctor_set(x_305, 9, x_281);
lean_ctor_set(x_305, 10, x_282);
lean_ctor_set(x_305, 11, x_283);
lean_ctor_set(x_305, 12, x_284);
lean_ctor_set(x_305, 13, x_285);
lean_ctor_set(x_305, 14, x_286);
lean_ctor_set(x_305, 15, x_287);
lean_ctor_set(x_305, 16, x_288);
lean_ctor_set(x_305, 17, x_289);
lean_ctor_set(x_305, 18, x_290);
lean_ctor_set(x_305, 19, x_291);
lean_ctor_set(x_305, 20, x_292);
lean_ctor_set(x_305, 21, x_293);
lean_ctor_set(x_305, 22, x_294);
lean_ctor_set(x_305, 23, x_295);
lean_ctor_set(x_305, 24, x_296);
lean_ctor_set(x_305, 25, x_297);
lean_ctor_set_uint8(x_305, sizeof(void*)*26, x_278);
x_306 = lean_st_ref_set(x_12, x_305, x_271);
x_307 = lean_ctor_get(x_306, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 x_308 = x_306;
} else {
 lean_dec_ref(x_306);
 x_308 = lean_box(0);
}
x_309 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__4;
x_310 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_309, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_307);
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_unbox(x_311);
lean_dec(x_311);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_308);
lean_free_object(x_22);
x_313 = lean_ctor_get(x_310, 1);
lean_inc(x_313);
lean_dec(x_310);
x_314 = lean_box(0);
x_315 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_34, x_314, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_313);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
x_25 = x_316;
x_26 = x_317;
goto block_31;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_310, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 lean_ctor_release(x_310, 1);
 x_319 = x_310;
} else {
 lean_dec_ref(x_310);
 x_319 = lean_box(0);
}
x_320 = l_Lean_Meta_Grind_updateLastTag(x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_318);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_321 = lean_ctor_get(x_320, 1);
lean_inc(x_321);
lean_dec(x_320);
lean_inc(x_2);
x_322 = l_Lean_MessageData_ofExpr(x_2);
x_323 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___closed__2;
if (lean_is_scalar(x_319)) {
 x_324 = lean_alloc_ctor(7, 2, 0);
} else {
 x_324 = x_319;
 lean_ctor_set_tag(x_324, 7);
}
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_322);
x_325 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__8;
if (lean_is_scalar(x_308)) {
 x_326 = lean_alloc_ctor(7, 2, 0);
} else {
 x_326 = x_308;
 lean_ctor_set_tag(x_326, 7);
}
lean_ctor_set(x_326, 0, x_324);
lean_ctor_set(x_326, 1, x_325);
lean_inc(x_34);
x_327 = l_Lean_MessageData_ofExpr(x_34);
x_328 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
x_329 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_329);
lean_ctor_set(x_22, 0, x_328);
x_330 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_309, x_22, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_321);
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
lean_dec(x_330);
x_333 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_34, x_331, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_332);
lean_dec(x_331);
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_333, 1);
lean_inc(x_335);
lean_dec(x_333);
x_25 = x_334;
x_26 = x_335;
goto block_31;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_319);
lean_dec(x_308);
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
x_336 = lean_ctor_get(x_320, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_320, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 x_338 = x_320;
} else {
 lean_dec_ref(x_320);
 x_338 = lean_box(0);
}
if (lean_is_scalar(x_338)) {
 x_339 = lean_alloc_ctor(1, 2, 0);
} else {
 x_339 = x_338;
}
lean_ctor_set(x_339, 0, x_336);
lean_ctor_set(x_339, 1, x_337);
return x_339;
}
}
}
}
}
else
{
uint8_t x_340; 
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
x_340 = !lean_is_exclusive(x_60);
if (x_340 == 0)
{
return x_60;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_ctor_get(x_60, 0);
x_342 = lean_ctor_get(x_60, 1);
lean_inc(x_342);
lean_inc(x_341);
lean_dec(x_60);
x_343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
return x_343;
}
}
}
}
else
{
uint8_t x_344; 
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
x_344 = !lean_is_exclusive(x_54);
if (x_344 == 0)
{
return x_54;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_345 = lean_ctor_get(x_54, 0);
x_346 = lean_ctor_get(x_54, 1);
lean_inc(x_346);
lean_inc(x_345);
lean_dec(x_54);
x_347 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_346);
return x_347;
}
}
}
else
{
uint8_t x_348; uint8_t x_349; uint8_t x_350; uint8_t x_351; uint8_t x_352; uint8_t x_353; uint8_t x_354; uint8_t x_355; uint8_t x_356; uint8_t x_357; uint8_t x_358; uint8_t x_359; uint8_t x_360; uint8_t x_361; uint8_t x_362; uint8_t x_363; uint8_t x_364; uint8_t x_365; uint8_t x_366; uint8_t x_367; lean_object* x_368; uint64_t x_369; uint64_t x_370; uint64_t x_371; uint64_t x_372; uint64_t x_373; lean_object* x_374; lean_object* x_375; 
x_348 = lean_ctor_get_uint8(x_16, sizeof(void*)*7 + 9);
x_349 = lean_ctor_get_uint8(x_16, sizeof(void*)*7 + 10);
x_350 = lean_ctor_get_uint8(x_32, 0);
x_351 = lean_ctor_get_uint8(x_32, 1);
x_352 = lean_ctor_get_uint8(x_32, 2);
x_353 = lean_ctor_get_uint8(x_32, 3);
x_354 = lean_ctor_get_uint8(x_32, 4);
x_355 = lean_ctor_get_uint8(x_32, 5);
x_356 = lean_ctor_get_uint8(x_32, 6);
x_357 = lean_ctor_get_uint8(x_32, 7);
x_358 = lean_ctor_get_uint8(x_32, 8);
x_359 = lean_ctor_get_uint8(x_32, 10);
x_360 = lean_ctor_get_uint8(x_32, 11);
x_361 = lean_ctor_get_uint8(x_32, 12);
x_362 = lean_ctor_get_uint8(x_32, 13);
x_363 = lean_ctor_get_uint8(x_32, 14);
x_364 = lean_ctor_get_uint8(x_32, 15);
x_365 = lean_ctor_get_uint8(x_32, 16);
x_366 = lean_ctor_get_uint8(x_32, 17);
lean_dec(x_32);
x_367 = 1;
x_368 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_368, 0, x_350);
lean_ctor_set_uint8(x_368, 1, x_351);
lean_ctor_set_uint8(x_368, 2, x_352);
lean_ctor_set_uint8(x_368, 3, x_353);
lean_ctor_set_uint8(x_368, 4, x_354);
lean_ctor_set_uint8(x_368, 5, x_355);
lean_ctor_set_uint8(x_368, 6, x_356);
lean_ctor_set_uint8(x_368, 7, x_357);
lean_ctor_set_uint8(x_368, 8, x_358);
lean_ctor_set_uint8(x_368, 9, x_367);
lean_ctor_set_uint8(x_368, 10, x_359);
lean_ctor_set_uint8(x_368, 11, x_360);
lean_ctor_set_uint8(x_368, 12, x_361);
lean_ctor_set_uint8(x_368, 13, x_362);
lean_ctor_set_uint8(x_368, 14, x_363);
lean_ctor_set_uint8(x_368, 15, x_364);
lean_ctor_set_uint8(x_368, 16, x_365);
lean_ctor_set_uint8(x_368, 17, x_366);
x_369 = 2;
x_370 = lean_uint64_shift_right(x_36, x_369);
x_371 = lean_uint64_shift_left(x_370, x_369);
x_372 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__3___closed__1;
x_373 = lean_uint64_lor(x_371, x_372);
x_374 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_374, 0, x_368);
lean_ctor_set(x_374, 1, x_38);
lean_ctor_set(x_374, 2, x_39);
lean_ctor_set(x_374, 3, x_40);
lean_ctor_set(x_374, 4, x_41);
lean_ctor_set(x_374, 5, x_42);
lean_ctor_set(x_374, 6, x_43);
lean_ctor_set_uint64(x_374, sizeof(void*)*7, x_373);
lean_ctor_set_uint8(x_374, sizeof(void*)*7 + 8, x_37);
lean_ctor_set_uint8(x_374, sizeof(void*)*7 + 9, x_348);
lean_ctor_set_uint8(x_374, sizeof(void*)*7 + 10, x_349);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_4);
x_375 = l_Lean_Meta_isExprDefEq(x_4, x_35, x_374, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; uint8_t x_377; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_unbox(x_376);
lean_dec(x_376);
if (x_377 == 0)
{
lean_object* x_378; lean_object* x_379; 
lean_free_object(x_22);
lean_dec(x_34);
x_378 = lean_ctor_get(x_375, 1);
lean_inc(x_378);
lean_dec(x_375);
lean_inc(x_6);
x_379 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_379, 0, x_6);
x_25 = x_379;
x_26 = x_378;
goto block_31;
}
else
{
lean_object* x_380; lean_object* x_381; 
x_380 = lean_ctor_get(x_375, 1);
lean_inc(x_380);
lean_dec(x_375);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_34);
lean_inc(x_2);
x_381 = l_Lean_Meta_isExprDefEq(x_2, x_34, x_16, x_17, x_18, x_19, x_380);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; uint8_t x_383; 
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_unbox(x_382);
lean_dec(x_382);
if (x_383 == 0)
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; 
lean_free_object(x_22);
x_384 = lean_ctor_get(x_381, 1);
lean_inc(x_384);
lean_dec(x_381);
x_385 = lean_box(0);
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
x_386 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2(x_3, x_6, x_2, x_34, x_1, x_385, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_384);
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; lean_object* x_388; 
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
lean_dec(x_386);
x_25 = x_387;
x_26 = x_388;
goto block_31;
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
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
x_389 = lean_ctor_get(x_386, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_386, 1);
lean_inc(x_390);
if (lean_is_exclusive(x_386)) {
 lean_ctor_release(x_386, 0);
 lean_ctor_release(x_386, 1);
 x_391 = x_386;
} else {
 lean_dec_ref(x_386);
 x_391 = lean_box(0);
}
if (lean_is_scalar(x_391)) {
 x_392 = lean_alloc_ctor(1, 2, 0);
} else {
 x_392 = x_391;
}
lean_ctor_set(x_392, 0, x_389);
lean_ctor_set(x_392, 1, x_390);
return x_392;
}
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; uint8_t x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; uint8_t x_439; 
x_393 = lean_ctor_get(x_381, 1);
lean_inc(x_393);
lean_dec(x_381);
x_394 = lean_st_ref_take(x_12, x_393);
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_395, 1);
lean_inc(x_396);
x_397 = lean_ctor_get(x_394, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 x_398 = x_394;
} else {
 lean_dec_ref(x_394);
 x_398 = lean_box(0);
}
x_399 = lean_ctor_get(x_395, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_395, 2);
lean_inc(x_400);
x_401 = lean_ctor_get(x_395, 3);
lean_inc(x_401);
x_402 = lean_ctor_get(x_395, 4);
lean_inc(x_402);
x_403 = lean_ctor_get(x_395, 5);
lean_inc(x_403);
x_404 = lean_ctor_get(x_395, 6);
lean_inc(x_404);
x_405 = lean_ctor_get_uint8(x_395, sizeof(void*)*26);
x_406 = lean_ctor_get(x_395, 7);
lean_inc(x_406);
x_407 = lean_ctor_get(x_395, 8);
lean_inc(x_407);
x_408 = lean_ctor_get(x_395, 9);
lean_inc(x_408);
x_409 = lean_ctor_get(x_395, 10);
lean_inc(x_409);
x_410 = lean_ctor_get(x_395, 11);
lean_inc(x_410);
x_411 = lean_ctor_get(x_395, 12);
lean_inc(x_411);
x_412 = lean_ctor_get(x_395, 13);
lean_inc(x_412);
x_413 = lean_ctor_get(x_395, 14);
lean_inc(x_413);
x_414 = lean_ctor_get(x_395, 15);
lean_inc(x_414);
x_415 = lean_ctor_get(x_395, 16);
lean_inc(x_415);
x_416 = lean_ctor_get(x_395, 17);
lean_inc(x_416);
x_417 = lean_ctor_get(x_395, 18);
lean_inc(x_417);
x_418 = lean_ctor_get(x_395, 19);
lean_inc(x_418);
x_419 = lean_ctor_get(x_395, 20);
lean_inc(x_419);
x_420 = lean_ctor_get(x_395, 21);
lean_inc(x_420);
x_421 = lean_ctor_get(x_395, 22);
lean_inc(x_421);
x_422 = lean_ctor_get(x_395, 23);
lean_inc(x_422);
x_423 = lean_ctor_get(x_395, 24);
lean_inc(x_423);
x_424 = lean_ctor_get(x_395, 25);
lean_inc(x_424);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 lean_ctor_release(x_395, 1);
 lean_ctor_release(x_395, 2);
 lean_ctor_release(x_395, 3);
 lean_ctor_release(x_395, 4);
 lean_ctor_release(x_395, 5);
 lean_ctor_release(x_395, 6);
 lean_ctor_release(x_395, 7);
 lean_ctor_release(x_395, 8);
 lean_ctor_release(x_395, 9);
 lean_ctor_release(x_395, 10);
 lean_ctor_release(x_395, 11);
 lean_ctor_release(x_395, 12);
 lean_ctor_release(x_395, 13);
 lean_ctor_release(x_395, 14);
 lean_ctor_release(x_395, 15);
 lean_ctor_release(x_395, 16);
 lean_ctor_release(x_395, 17);
 lean_ctor_release(x_395, 18);
 lean_ctor_release(x_395, 19);
 lean_ctor_release(x_395, 20);
 lean_ctor_release(x_395, 21);
 lean_ctor_release(x_395, 22);
 lean_ctor_release(x_395, 23);
 lean_ctor_release(x_395, 24);
 lean_ctor_release(x_395, 25);
 x_425 = x_395;
} else {
 lean_dec_ref(x_395);
 x_425 = lean_box(0);
}
x_426 = lean_ctor_get(x_396, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_396, 1);
lean_inc(x_427);
x_428 = lean_ctor_get(x_396, 2);
lean_inc(x_428);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 lean_ctor_release(x_396, 2);
 x_429 = x_396;
} else {
 lean_dec_ref(x_396);
 x_429 = lean_box(0);
}
lean_inc(x_34);
lean_inc(x_2);
x_430 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_427, x_2, x_34);
if (lean_is_scalar(x_429)) {
 x_431 = lean_alloc_ctor(0, 3, 0);
} else {
 x_431 = x_429;
}
lean_ctor_set(x_431, 0, x_426);
lean_ctor_set(x_431, 1, x_430);
lean_ctor_set(x_431, 2, x_428);
if (lean_is_scalar(x_425)) {
 x_432 = lean_alloc_ctor(0, 26, 1);
} else {
 x_432 = x_425;
}
lean_ctor_set(x_432, 0, x_399);
lean_ctor_set(x_432, 1, x_431);
lean_ctor_set(x_432, 2, x_400);
lean_ctor_set(x_432, 3, x_401);
lean_ctor_set(x_432, 4, x_402);
lean_ctor_set(x_432, 5, x_403);
lean_ctor_set(x_432, 6, x_404);
lean_ctor_set(x_432, 7, x_406);
lean_ctor_set(x_432, 8, x_407);
lean_ctor_set(x_432, 9, x_408);
lean_ctor_set(x_432, 10, x_409);
lean_ctor_set(x_432, 11, x_410);
lean_ctor_set(x_432, 12, x_411);
lean_ctor_set(x_432, 13, x_412);
lean_ctor_set(x_432, 14, x_413);
lean_ctor_set(x_432, 15, x_414);
lean_ctor_set(x_432, 16, x_415);
lean_ctor_set(x_432, 17, x_416);
lean_ctor_set(x_432, 18, x_417);
lean_ctor_set(x_432, 19, x_418);
lean_ctor_set(x_432, 20, x_419);
lean_ctor_set(x_432, 21, x_420);
lean_ctor_set(x_432, 22, x_421);
lean_ctor_set(x_432, 23, x_422);
lean_ctor_set(x_432, 24, x_423);
lean_ctor_set(x_432, 25, x_424);
lean_ctor_set_uint8(x_432, sizeof(void*)*26, x_405);
x_433 = lean_st_ref_set(x_12, x_432, x_397);
x_434 = lean_ctor_get(x_433, 1);
lean_inc(x_434);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 x_435 = x_433;
} else {
 lean_dec_ref(x_433);
 x_435 = lean_box(0);
}
x_436 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__4;
x_437 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_436, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_434);
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
x_439 = lean_unbox(x_438);
lean_dec(x_438);
if (x_439 == 0)
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
lean_dec(x_435);
lean_dec(x_398);
lean_free_object(x_22);
x_440 = lean_ctor_get(x_437, 1);
lean_inc(x_440);
lean_dec(x_437);
x_441 = lean_box(0);
x_442 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_34, x_441, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_440);
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_442, 1);
lean_inc(x_444);
lean_dec(x_442);
x_25 = x_443;
x_26 = x_444;
goto block_31;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_445 = lean_ctor_get(x_437, 1);
lean_inc(x_445);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 lean_ctor_release(x_437, 1);
 x_446 = x_437;
} else {
 lean_dec_ref(x_437);
 x_446 = lean_box(0);
}
x_447 = l_Lean_Meta_Grind_updateLastTag(x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_445);
if (lean_obj_tag(x_447) == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_448 = lean_ctor_get(x_447, 1);
lean_inc(x_448);
lean_dec(x_447);
lean_inc(x_2);
x_449 = l_Lean_MessageData_ofExpr(x_2);
x_450 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___closed__2;
if (lean_is_scalar(x_446)) {
 x_451 = lean_alloc_ctor(7, 2, 0);
} else {
 x_451 = x_446;
 lean_ctor_set_tag(x_451, 7);
}
lean_ctor_set(x_451, 0, x_450);
lean_ctor_set(x_451, 1, x_449);
x_452 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__8;
if (lean_is_scalar(x_435)) {
 x_453 = lean_alloc_ctor(7, 2, 0);
} else {
 x_453 = x_435;
 lean_ctor_set_tag(x_453, 7);
}
lean_ctor_set(x_453, 0, x_451);
lean_ctor_set(x_453, 1, x_452);
lean_inc(x_34);
x_454 = l_Lean_MessageData_ofExpr(x_34);
if (lean_is_scalar(x_398)) {
 x_455 = lean_alloc_ctor(7, 2, 0);
} else {
 x_455 = x_398;
 lean_ctor_set_tag(x_455, 7);
}
lean_ctor_set(x_455, 0, x_453);
lean_ctor_set(x_455, 1, x_454);
x_456 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_456);
lean_ctor_set(x_22, 0, x_455);
x_457 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_436, x_22, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_448);
x_458 = lean_ctor_get(x_457, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_457, 1);
lean_inc(x_459);
lean_dec(x_457);
x_460 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_34, x_458, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_459);
lean_dec(x_458);
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_460, 1);
lean_inc(x_462);
lean_dec(x_460);
x_25 = x_461;
x_26 = x_462;
goto block_31;
}
else
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
lean_dec(x_446);
lean_dec(x_435);
lean_dec(x_398);
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
x_463 = lean_ctor_get(x_447, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_447, 1);
lean_inc(x_464);
if (lean_is_exclusive(x_447)) {
 lean_ctor_release(x_447, 0);
 lean_ctor_release(x_447, 1);
 x_465 = x_447;
} else {
 lean_dec_ref(x_447);
 x_465 = lean_box(0);
}
if (lean_is_scalar(x_465)) {
 x_466 = lean_alloc_ctor(1, 2, 0);
} else {
 x_466 = x_465;
}
lean_ctor_set(x_466, 0, x_463);
lean_ctor_set(x_466, 1, x_464);
return x_466;
}
}
}
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
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
x_467 = lean_ctor_get(x_381, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_381, 1);
lean_inc(x_468);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 x_469 = x_381;
} else {
 lean_dec_ref(x_381);
 x_469 = lean_box(0);
}
if (lean_is_scalar(x_469)) {
 x_470 = lean_alloc_ctor(1, 2, 0);
} else {
 x_470 = x_469;
}
lean_ctor_set(x_470, 0, x_467);
lean_ctor_set(x_470, 1, x_468);
return x_470;
}
}
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
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
x_471 = lean_ctor_get(x_375, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_375, 1);
lean_inc(x_472);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_473 = x_375;
} else {
 lean_dec_ref(x_375);
 x_473 = lean_box(0);
}
if (lean_is_scalar(x_473)) {
 x_474 = lean_alloc_ctor(1, 2, 0);
} else {
 x_474 = x_473;
}
lean_ctor_set(x_474, 0, x_471);
lean_ctor_set(x_474, 1, x_472);
return x_474;
}
}
}
else
{
lean_object* x_475; lean_object* x_476; uint64_t x_477; uint8_t x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; uint8_t x_485; uint8_t x_486; uint8_t x_487; uint8_t x_488; uint8_t x_489; uint8_t x_490; uint8_t x_491; uint8_t x_492; uint8_t x_493; uint8_t x_494; uint8_t x_495; uint8_t x_496; uint8_t x_497; uint8_t x_498; uint8_t x_499; uint8_t x_500; uint8_t x_501; uint8_t x_502; uint8_t x_503; lean_object* x_504; uint8_t x_505; lean_object* x_506; uint64_t x_507; uint64_t x_508; uint64_t x_509; uint64_t x_510; uint64_t x_511; lean_object* x_512; lean_object* x_513; 
x_475 = lean_ctor_get(x_22, 0);
x_476 = lean_ctor_get(x_22, 1);
lean_inc(x_476);
lean_inc(x_475);
lean_dec(x_22);
x_477 = lean_ctor_get_uint64(x_16, sizeof(void*)*7);
x_478 = lean_ctor_get_uint8(x_16, sizeof(void*)*7 + 8);
x_479 = lean_ctor_get(x_16, 1);
lean_inc(x_479);
x_480 = lean_ctor_get(x_16, 2);
lean_inc(x_480);
x_481 = lean_ctor_get(x_16, 3);
lean_inc(x_481);
x_482 = lean_ctor_get(x_16, 4);
lean_inc(x_482);
x_483 = lean_ctor_get(x_16, 5);
lean_inc(x_483);
x_484 = lean_ctor_get(x_16, 6);
lean_inc(x_484);
x_485 = lean_ctor_get_uint8(x_16, sizeof(void*)*7 + 9);
x_486 = lean_ctor_get_uint8(x_16, sizeof(void*)*7 + 10);
x_487 = lean_ctor_get_uint8(x_32, 0);
x_488 = lean_ctor_get_uint8(x_32, 1);
x_489 = lean_ctor_get_uint8(x_32, 2);
x_490 = lean_ctor_get_uint8(x_32, 3);
x_491 = lean_ctor_get_uint8(x_32, 4);
x_492 = lean_ctor_get_uint8(x_32, 5);
x_493 = lean_ctor_get_uint8(x_32, 6);
x_494 = lean_ctor_get_uint8(x_32, 7);
x_495 = lean_ctor_get_uint8(x_32, 8);
x_496 = lean_ctor_get_uint8(x_32, 10);
x_497 = lean_ctor_get_uint8(x_32, 11);
x_498 = lean_ctor_get_uint8(x_32, 12);
x_499 = lean_ctor_get_uint8(x_32, 13);
x_500 = lean_ctor_get_uint8(x_32, 14);
x_501 = lean_ctor_get_uint8(x_32, 15);
x_502 = lean_ctor_get_uint8(x_32, 16);
x_503 = lean_ctor_get_uint8(x_32, 17);
if (lean_is_exclusive(x_32)) {
 x_504 = x_32;
} else {
 lean_dec_ref(x_32);
 x_504 = lean_box(0);
}
x_505 = 1;
if (lean_is_scalar(x_504)) {
 x_506 = lean_alloc_ctor(0, 0, 18);
} else {
 x_506 = x_504;
}
lean_ctor_set_uint8(x_506, 0, x_487);
lean_ctor_set_uint8(x_506, 1, x_488);
lean_ctor_set_uint8(x_506, 2, x_489);
lean_ctor_set_uint8(x_506, 3, x_490);
lean_ctor_set_uint8(x_506, 4, x_491);
lean_ctor_set_uint8(x_506, 5, x_492);
lean_ctor_set_uint8(x_506, 6, x_493);
lean_ctor_set_uint8(x_506, 7, x_494);
lean_ctor_set_uint8(x_506, 8, x_495);
lean_ctor_set_uint8(x_506, 9, x_505);
lean_ctor_set_uint8(x_506, 10, x_496);
lean_ctor_set_uint8(x_506, 11, x_497);
lean_ctor_set_uint8(x_506, 12, x_498);
lean_ctor_set_uint8(x_506, 13, x_499);
lean_ctor_set_uint8(x_506, 14, x_500);
lean_ctor_set_uint8(x_506, 15, x_501);
lean_ctor_set_uint8(x_506, 16, x_502);
lean_ctor_set_uint8(x_506, 17, x_503);
x_507 = 2;
x_508 = lean_uint64_shift_right(x_477, x_507);
x_509 = lean_uint64_shift_left(x_508, x_507);
x_510 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lambda__3___closed__1;
x_511 = lean_uint64_lor(x_509, x_510);
x_512 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_512, 0, x_506);
lean_ctor_set(x_512, 1, x_479);
lean_ctor_set(x_512, 2, x_480);
lean_ctor_set(x_512, 3, x_481);
lean_ctor_set(x_512, 4, x_482);
lean_ctor_set(x_512, 5, x_483);
lean_ctor_set(x_512, 6, x_484);
lean_ctor_set_uint64(x_512, sizeof(void*)*7, x_511);
lean_ctor_set_uint8(x_512, sizeof(void*)*7 + 8, x_478);
lean_ctor_set_uint8(x_512, sizeof(void*)*7 + 9, x_485);
lean_ctor_set_uint8(x_512, sizeof(void*)*7 + 10, x_486);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_4);
x_513 = l_Lean_Meta_isExprDefEq(x_4, x_476, x_512, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_514; uint8_t x_515; 
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
x_515 = lean_unbox(x_514);
lean_dec(x_514);
if (x_515 == 0)
{
lean_object* x_516; lean_object* x_517; 
lean_dec(x_475);
x_516 = lean_ctor_get(x_513, 1);
lean_inc(x_516);
lean_dec(x_513);
lean_inc(x_6);
x_517 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_517, 0, x_6);
x_25 = x_517;
x_26 = x_516;
goto block_31;
}
else
{
lean_object* x_518; lean_object* x_519; 
x_518 = lean_ctor_get(x_513, 1);
lean_inc(x_518);
lean_dec(x_513);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_475);
lean_inc(x_2);
x_519 = l_Lean_Meta_isExprDefEq(x_2, x_475, x_16, x_17, x_18, x_19, x_518);
if (lean_obj_tag(x_519) == 0)
{
lean_object* x_520; uint8_t x_521; 
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
x_521 = lean_unbox(x_520);
lean_dec(x_520);
if (x_521 == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; 
x_522 = lean_ctor_get(x_519, 1);
lean_inc(x_522);
lean_dec(x_519);
x_523 = lean_box(0);
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
x_524 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2(x_3, x_6, x_2, x_475, x_1, x_523, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_522);
if (lean_obj_tag(x_524) == 0)
{
lean_object* x_525; lean_object* x_526; 
x_525 = lean_ctor_get(x_524, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_524, 1);
lean_inc(x_526);
lean_dec(x_524);
x_25 = x_525;
x_26 = x_526;
goto block_31;
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
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
x_527 = lean_ctor_get(x_524, 0);
lean_inc(x_527);
x_528 = lean_ctor_get(x_524, 1);
lean_inc(x_528);
if (lean_is_exclusive(x_524)) {
 lean_ctor_release(x_524, 0);
 lean_ctor_release(x_524, 1);
 x_529 = x_524;
} else {
 lean_dec_ref(x_524);
 x_529 = lean_box(0);
}
if (lean_is_scalar(x_529)) {
 x_530 = lean_alloc_ctor(1, 2, 0);
} else {
 x_530 = x_529;
}
lean_ctor_set(x_530, 0, x_527);
lean_ctor_set(x_530, 1, x_528);
return x_530;
}
}
else
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; uint8_t x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; uint8_t x_577; 
x_531 = lean_ctor_get(x_519, 1);
lean_inc(x_531);
lean_dec(x_519);
x_532 = lean_st_ref_take(x_12, x_531);
x_533 = lean_ctor_get(x_532, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_533, 1);
lean_inc(x_534);
x_535 = lean_ctor_get(x_532, 1);
lean_inc(x_535);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 lean_ctor_release(x_532, 1);
 x_536 = x_532;
} else {
 lean_dec_ref(x_532);
 x_536 = lean_box(0);
}
x_537 = lean_ctor_get(x_533, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_533, 2);
lean_inc(x_538);
x_539 = lean_ctor_get(x_533, 3);
lean_inc(x_539);
x_540 = lean_ctor_get(x_533, 4);
lean_inc(x_540);
x_541 = lean_ctor_get(x_533, 5);
lean_inc(x_541);
x_542 = lean_ctor_get(x_533, 6);
lean_inc(x_542);
x_543 = lean_ctor_get_uint8(x_533, sizeof(void*)*26);
x_544 = lean_ctor_get(x_533, 7);
lean_inc(x_544);
x_545 = lean_ctor_get(x_533, 8);
lean_inc(x_545);
x_546 = lean_ctor_get(x_533, 9);
lean_inc(x_546);
x_547 = lean_ctor_get(x_533, 10);
lean_inc(x_547);
x_548 = lean_ctor_get(x_533, 11);
lean_inc(x_548);
x_549 = lean_ctor_get(x_533, 12);
lean_inc(x_549);
x_550 = lean_ctor_get(x_533, 13);
lean_inc(x_550);
x_551 = lean_ctor_get(x_533, 14);
lean_inc(x_551);
x_552 = lean_ctor_get(x_533, 15);
lean_inc(x_552);
x_553 = lean_ctor_get(x_533, 16);
lean_inc(x_553);
x_554 = lean_ctor_get(x_533, 17);
lean_inc(x_554);
x_555 = lean_ctor_get(x_533, 18);
lean_inc(x_555);
x_556 = lean_ctor_get(x_533, 19);
lean_inc(x_556);
x_557 = lean_ctor_get(x_533, 20);
lean_inc(x_557);
x_558 = lean_ctor_get(x_533, 21);
lean_inc(x_558);
x_559 = lean_ctor_get(x_533, 22);
lean_inc(x_559);
x_560 = lean_ctor_get(x_533, 23);
lean_inc(x_560);
x_561 = lean_ctor_get(x_533, 24);
lean_inc(x_561);
x_562 = lean_ctor_get(x_533, 25);
lean_inc(x_562);
if (lean_is_exclusive(x_533)) {
 lean_ctor_release(x_533, 0);
 lean_ctor_release(x_533, 1);
 lean_ctor_release(x_533, 2);
 lean_ctor_release(x_533, 3);
 lean_ctor_release(x_533, 4);
 lean_ctor_release(x_533, 5);
 lean_ctor_release(x_533, 6);
 lean_ctor_release(x_533, 7);
 lean_ctor_release(x_533, 8);
 lean_ctor_release(x_533, 9);
 lean_ctor_release(x_533, 10);
 lean_ctor_release(x_533, 11);
 lean_ctor_release(x_533, 12);
 lean_ctor_release(x_533, 13);
 lean_ctor_release(x_533, 14);
 lean_ctor_release(x_533, 15);
 lean_ctor_release(x_533, 16);
 lean_ctor_release(x_533, 17);
 lean_ctor_release(x_533, 18);
 lean_ctor_release(x_533, 19);
 lean_ctor_release(x_533, 20);
 lean_ctor_release(x_533, 21);
 lean_ctor_release(x_533, 22);
 lean_ctor_release(x_533, 23);
 lean_ctor_release(x_533, 24);
 lean_ctor_release(x_533, 25);
 x_563 = x_533;
} else {
 lean_dec_ref(x_533);
 x_563 = lean_box(0);
}
x_564 = lean_ctor_get(x_534, 0);
lean_inc(x_564);
x_565 = lean_ctor_get(x_534, 1);
lean_inc(x_565);
x_566 = lean_ctor_get(x_534, 2);
lean_inc(x_566);
if (lean_is_exclusive(x_534)) {
 lean_ctor_release(x_534, 0);
 lean_ctor_release(x_534, 1);
 lean_ctor_release(x_534, 2);
 x_567 = x_534;
} else {
 lean_dec_ref(x_534);
 x_567 = lean_box(0);
}
lean_inc(x_475);
lean_inc(x_2);
x_568 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_565, x_2, x_475);
if (lean_is_scalar(x_567)) {
 x_569 = lean_alloc_ctor(0, 3, 0);
} else {
 x_569 = x_567;
}
lean_ctor_set(x_569, 0, x_564);
lean_ctor_set(x_569, 1, x_568);
lean_ctor_set(x_569, 2, x_566);
if (lean_is_scalar(x_563)) {
 x_570 = lean_alloc_ctor(0, 26, 1);
} else {
 x_570 = x_563;
}
lean_ctor_set(x_570, 0, x_537);
lean_ctor_set(x_570, 1, x_569);
lean_ctor_set(x_570, 2, x_538);
lean_ctor_set(x_570, 3, x_539);
lean_ctor_set(x_570, 4, x_540);
lean_ctor_set(x_570, 5, x_541);
lean_ctor_set(x_570, 6, x_542);
lean_ctor_set(x_570, 7, x_544);
lean_ctor_set(x_570, 8, x_545);
lean_ctor_set(x_570, 9, x_546);
lean_ctor_set(x_570, 10, x_547);
lean_ctor_set(x_570, 11, x_548);
lean_ctor_set(x_570, 12, x_549);
lean_ctor_set(x_570, 13, x_550);
lean_ctor_set(x_570, 14, x_551);
lean_ctor_set(x_570, 15, x_552);
lean_ctor_set(x_570, 16, x_553);
lean_ctor_set(x_570, 17, x_554);
lean_ctor_set(x_570, 18, x_555);
lean_ctor_set(x_570, 19, x_556);
lean_ctor_set(x_570, 20, x_557);
lean_ctor_set(x_570, 21, x_558);
lean_ctor_set(x_570, 22, x_559);
lean_ctor_set(x_570, 23, x_560);
lean_ctor_set(x_570, 24, x_561);
lean_ctor_set(x_570, 25, x_562);
lean_ctor_set_uint8(x_570, sizeof(void*)*26, x_543);
x_571 = lean_st_ref_set(x_12, x_570, x_535);
x_572 = lean_ctor_get(x_571, 1);
lean_inc(x_572);
if (lean_is_exclusive(x_571)) {
 lean_ctor_release(x_571, 0);
 lean_ctor_release(x_571, 1);
 x_573 = x_571;
} else {
 lean_dec_ref(x_571);
 x_573 = lean_box(0);
}
x_574 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__4;
x_575 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_574, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_572);
x_576 = lean_ctor_get(x_575, 0);
lean_inc(x_576);
x_577 = lean_unbox(x_576);
lean_dec(x_576);
if (x_577 == 0)
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
lean_dec(x_573);
lean_dec(x_536);
x_578 = lean_ctor_get(x_575, 1);
lean_inc(x_578);
lean_dec(x_575);
x_579 = lean_box(0);
x_580 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_475, x_579, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_578);
x_581 = lean_ctor_get(x_580, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_580, 1);
lean_inc(x_582);
lean_dec(x_580);
x_25 = x_581;
x_26 = x_582;
goto block_31;
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; 
x_583 = lean_ctor_get(x_575, 1);
lean_inc(x_583);
if (lean_is_exclusive(x_575)) {
 lean_ctor_release(x_575, 0);
 lean_ctor_release(x_575, 1);
 x_584 = x_575;
} else {
 lean_dec_ref(x_575);
 x_584 = lean_box(0);
}
x_585 = l_Lean_Meta_Grind_updateLastTag(x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_583);
if (lean_obj_tag(x_585) == 0)
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; 
x_586 = lean_ctor_get(x_585, 1);
lean_inc(x_586);
lean_dec(x_585);
lean_inc(x_2);
x_587 = l_Lean_MessageData_ofExpr(x_2);
x_588 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___closed__2;
if (lean_is_scalar(x_584)) {
 x_589 = lean_alloc_ctor(7, 2, 0);
} else {
 x_589 = x_584;
 lean_ctor_set_tag(x_589, 7);
}
lean_ctor_set(x_589, 0, x_588);
lean_ctor_set(x_589, 1, x_587);
x_590 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__8;
if (lean_is_scalar(x_573)) {
 x_591 = lean_alloc_ctor(7, 2, 0);
} else {
 x_591 = x_573;
 lean_ctor_set_tag(x_591, 7);
}
lean_ctor_set(x_591, 0, x_589);
lean_ctor_set(x_591, 1, x_590);
lean_inc(x_475);
x_592 = l_Lean_MessageData_ofExpr(x_475);
if (lean_is_scalar(x_536)) {
 x_593 = lean_alloc_ctor(7, 2, 0);
} else {
 x_593 = x_536;
 lean_ctor_set_tag(x_593, 7);
}
lean_ctor_set(x_593, 0, x_591);
lean_ctor_set(x_593, 1, x_592);
x_594 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__2___closed__10;
x_595 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_595, 0, x_593);
lean_ctor_set(x_595, 1, x_594);
x_596 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_574, x_595, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_586);
x_597 = lean_ctor_get(x_596, 0);
lean_inc(x_597);
x_598 = lean_ctor_get(x_596, 1);
lean_inc(x_598);
lean_dec(x_596);
x_599 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___lambda__1(x_475, x_597, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_598);
lean_dec(x_597);
x_600 = lean_ctor_get(x_599, 0);
lean_inc(x_600);
x_601 = lean_ctor_get(x_599, 1);
lean_inc(x_601);
lean_dec(x_599);
x_25 = x_600;
x_26 = x_601;
goto block_31;
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; 
lean_dec(x_584);
lean_dec(x_573);
lean_dec(x_536);
lean_dec(x_475);
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
x_602 = lean_ctor_get(x_585, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_585, 1);
lean_inc(x_603);
if (lean_is_exclusive(x_585)) {
 lean_ctor_release(x_585, 0);
 lean_ctor_release(x_585, 1);
 x_604 = x_585;
} else {
 lean_dec_ref(x_585);
 x_604 = lean_box(0);
}
if (lean_is_scalar(x_604)) {
 x_605 = lean_alloc_ctor(1, 2, 0);
} else {
 x_605 = x_604;
}
lean_ctor_set(x_605, 0, x_602);
lean_ctor_set(x_605, 1, x_603);
return x_605;
}
}
}
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; 
lean_dec(x_475);
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
x_606 = lean_ctor_get(x_519, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_519, 1);
lean_inc(x_607);
if (lean_is_exclusive(x_519)) {
 lean_ctor_release(x_519, 0);
 lean_ctor_release(x_519, 1);
 x_608 = x_519;
} else {
 lean_dec_ref(x_519);
 x_608 = lean_box(0);
}
if (lean_is_scalar(x_608)) {
 x_609 = lean_alloc_ctor(1, 2, 0);
} else {
 x_609 = x_608;
}
lean_ctor_set(x_609, 0, x_606);
lean_ctor_set(x_609, 1, x_607);
return x_609;
}
}
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
lean_dec(x_475);
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
x_610 = lean_ctor_get(x_513, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_513, 1);
lean_inc(x_611);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 lean_ctor_release(x_513, 1);
 x_612 = x_513;
} else {
 lean_dec_ref(x_513);
 x_612 = lean_box(0);
}
if (lean_is_scalar(x_612)) {
 x_613 = lean_alloc_ctor(1, 2, 0);
} else {
 x_613 = x_612;
}
lean_ctor_set(x_613, 0, x_610);
lean_ctor_set(x_613, 1, x_611);
return x_613;
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
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_45 = lean_ctor_get(x_16, 0);
x_46 = lean_ctor_get(x_16, 2);
x_47 = lean_ctor_get(x_16, 3);
x_48 = lean_ctor_get(x_16, 4);
x_49 = lean_ctor_get(x_16, 5);
x_50 = lean_ctor_get(x_16, 6);
x_51 = lean_ctor_get_uint8(x_16, sizeof(void*)*26);
x_52 = lean_ctor_get(x_16, 7);
x_53 = lean_ctor_get(x_16, 8);
x_54 = lean_ctor_get(x_16, 9);
x_55 = lean_ctor_get(x_16, 10);
x_56 = lean_ctor_get(x_16, 11);
x_57 = lean_ctor_get(x_16, 12);
x_58 = lean_ctor_get(x_16, 13);
x_59 = lean_ctor_get(x_16, 14);
x_60 = lean_ctor_get(x_16, 15);
x_61 = lean_ctor_get(x_16, 16);
x_62 = lean_ctor_get(x_16, 17);
x_63 = lean_ctor_get(x_16, 18);
x_64 = lean_ctor_get(x_16, 19);
x_65 = lean_ctor_get(x_16, 20);
x_66 = lean_ctor_get(x_16, 21);
x_67 = lean_ctor_get(x_16, 22);
x_68 = lean_ctor_get(x_16, 23);
x_69 = lean_ctor_get(x_16, 24);
x_70 = lean_ctor_get(x_16, 25);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
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
x_71 = lean_ctor_get(x_17, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_17, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_17, 2);
lean_inc(x_73);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 x_74 = x_17;
} else {
 lean_dec_ref(x_17);
 x_74 = lean_box(0);
}
lean_inc(x_1);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 0, x_1);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_15);
lean_ctor_set(x_75, 1, x_3);
x_76 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__9(x_71, x_4, x_75);
lean_inc_n(x_1, 2);
x_77 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_72, x_1, x_1);
if (lean_is_scalar(x_74)) {
 x_78 = lean_alloc_ctor(0, 3, 0);
} else {
 x_78 = x_74;
}
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set(x_78, 2, x_73);
x_79 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_79, 0, x_45);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_79, 2, x_46);
lean_ctor_set(x_79, 3, x_47);
lean_ctor_set(x_79, 4, x_48);
lean_ctor_set(x_79, 5, x_49);
lean_ctor_set(x_79, 6, x_50);
lean_ctor_set(x_79, 7, x_52);
lean_ctor_set(x_79, 8, x_53);
lean_ctor_set(x_79, 9, x_54);
lean_ctor_set(x_79, 10, x_55);
lean_ctor_set(x_79, 11, x_56);
lean_ctor_set(x_79, 12, x_57);
lean_ctor_set(x_79, 13, x_58);
lean_ctor_set(x_79, 14, x_59);
lean_ctor_set(x_79, 15, x_60);
lean_ctor_set(x_79, 16, x_61);
lean_ctor_set(x_79, 17, x_62);
lean_ctor_set(x_79, 18, x_63);
lean_ctor_set(x_79, 19, x_64);
lean_ctor_set(x_79, 20, x_65);
lean_ctor_set(x_79, 21, x_66);
lean_ctor_set(x_79, 22, x_67);
lean_ctor_set(x_79, 23, x_68);
lean_ctor_set(x_79, 24, x_69);
lean_ctor_set(x_79, 25, x_70);
lean_ctor_set_uint8(x_79, sizeof(void*)*26, x_51);
x_80 = lean_st_ref_set(x_6, x_79, x_19);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_82 = x_80;
} else {
 lean_dec_ref(x_80);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_84 = lean_ctor_get(x_15, 1);
lean_inc(x_84);
lean_dec(x_15);
x_85 = lean_ctor_get(x_16, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_16, 2);
lean_inc(x_86);
x_87 = lean_ctor_get(x_16, 3);
lean_inc(x_87);
x_88 = lean_ctor_get(x_16, 4);
lean_inc(x_88);
x_89 = lean_ctor_get(x_16, 5);
lean_inc(x_89);
x_90 = lean_ctor_get(x_16, 6);
lean_inc(x_90);
x_91 = lean_ctor_get_uint8(x_16, sizeof(void*)*26);
x_92 = lean_ctor_get(x_16, 7);
lean_inc(x_92);
x_93 = lean_ctor_get(x_16, 8);
lean_inc(x_93);
x_94 = lean_ctor_get(x_16, 9);
lean_inc(x_94);
x_95 = lean_ctor_get(x_16, 10);
lean_inc(x_95);
x_96 = lean_ctor_get(x_16, 11);
lean_inc(x_96);
x_97 = lean_ctor_get(x_16, 12);
lean_inc(x_97);
x_98 = lean_ctor_get(x_16, 13);
lean_inc(x_98);
x_99 = lean_ctor_get(x_16, 14);
lean_inc(x_99);
x_100 = lean_ctor_get(x_16, 15);
lean_inc(x_100);
x_101 = lean_ctor_get(x_16, 16);
lean_inc(x_101);
x_102 = lean_ctor_get(x_16, 17);
lean_inc(x_102);
x_103 = lean_ctor_get(x_16, 18);
lean_inc(x_103);
x_104 = lean_ctor_get(x_16, 19);
lean_inc(x_104);
x_105 = lean_ctor_get(x_16, 20);
lean_inc(x_105);
x_106 = lean_ctor_get(x_16, 21);
lean_inc(x_106);
x_107 = lean_ctor_get(x_16, 22);
lean_inc(x_107);
x_108 = lean_ctor_get(x_16, 23);
lean_inc(x_108);
x_109 = lean_ctor_get(x_16, 24);
lean_inc(x_109);
x_110 = lean_ctor_get(x_16, 25);
lean_inc(x_110);
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
 lean_ctor_release(x_16, 15);
 lean_ctor_release(x_16, 16);
 lean_ctor_release(x_16, 17);
 lean_ctor_release(x_16, 18);
 lean_ctor_release(x_16, 19);
 lean_ctor_release(x_16, 20);
 lean_ctor_release(x_16, 21);
 lean_ctor_release(x_16, 22);
 lean_ctor_release(x_16, 23);
 lean_ctor_release(x_16, 24);
 lean_ctor_release(x_16, 25);
 x_111 = x_16;
} else {
 lean_dec_ref(x_16);
 x_111 = lean_box(0);
}
x_112 = lean_ctor_get(x_17, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_17, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_17, 2);
lean_inc(x_114);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 x_115 = x_17;
} else {
 lean_dec_ref(x_17);
 x_115 = lean_box(0);
}
lean_inc(x_1);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_1);
lean_ctor_set(x_116, 1, x_2);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_3);
x_118 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__9(x_112, x_4, x_117);
lean_inc_n(x_1, 2);
x_119 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_113, x_1, x_1);
if (lean_is_scalar(x_115)) {
 x_120 = lean_alloc_ctor(0, 3, 0);
} else {
 x_120 = x_115;
}
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
lean_ctor_set(x_120, 2, x_114);
if (lean_is_scalar(x_111)) {
 x_121 = lean_alloc_ctor(0, 26, 1);
} else {
 x_121 = x_111;
}
lean_ctor_set(x_121, 0, x_85);
lean_ctor_set(x_121, 1, x_120);
lean_ctor_set(x_121, 2, x_86);
lean_ctor_set(x_121, 3, x_87);
lean_ctor_set(x_121, 4, x_88);
lean_ctor_set(x_121, 5, x_89);
lean_ctor_set(x_121, 6, x_90);
lean_ctor_set(x_121, 7, x_92);
lean_ctor_set(x_121, 8, x_93);
lean_ctor_set(x_121, 9, x_94);
lean_ctor_set(x_121, 10, x_95);
lean_ctor_set(x_121, 11, x_96);
lean_ctor_set(x_121, 12, x_97);
lean_ctor_set(x_121, 13, x_98);
lean_ctor_set(x_121, 14, x_99);
lean_ctor_set(x_121, 15, x_100);
lean_ctor_set(x_121, 16, x_101);
lean_ctor_set(x_121, 17, x_102);
lean_ctor_set(x_121, 18, x_103);
lean_ctor_set(x_121, 19, x_104);
lean_ctor_set(x_121, 20, x_105);
lean_ctor_set(x_121, 21, x_106);
lean_ctor_set(x_121, 22, x_107);
lean_ctor_set(x_121, 23, x_108);
lean_ctor_set(x_121, 24, x_109);
lean_ctor_set(x_121, 25, x_110);
lean_ctor_set_uint8(x_121, sizeof(void*)*26, x_91);
x_122 = lean_st_ref_set(x_6, x_121, x_84);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_124 = x_122;
} else {
 lean_dec_ref(x_122);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_1);
lean_ctor_set(x_125, 1, x_123);
return x_125;
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
lean_object* x_22; lean_object* x_220; lean_object* x_258; uint8_t x_259; 
lean_dec(x_11);
x_258 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_259 = l_Lean_Expr_isConstOf(x_9, x_258);
if (x_259 == 0)
{
lean_object* x_260; 
x_260 = lean_box(0);
x_220 = x_260;
goto block_257;
}
else
{
lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_261 = lean_array_get_size(x_10);
x_262 = lean_unsigned_to_nat(2u);
x_263 = lean_nat_dec_eq(x_261, x_262);
if (x_263 == 0)
{
lean_object* x_264; 
lean_dec(x_261);
x_264 = lean_box(0);
x_220 = x_264;
goto block_257;
}
else
{
lean_object* x_265; uint8_t x_266; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_265 = lean_unsigned_to_nat(0u);
x_266 = lean_nat_dec_lt(x_265, x_261);
lean_dec(x_261);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; 
x_267 = l_Lean_instInhabitedExpr;
x_268 = l_outOfBounds___rarg(x_267);
x_22 = x_268;
goto block_219;
}
else
{
lean_object* x_269; 
x_269 = lean_array_fget(x_10, x_265);
x_22 = x_269;
goto block_219;
}
}
}
block_219:
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
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
x_54 = lean_ctor_get_uint8(x_40, sizeof(void*)*26);
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
x_63 = lean_ctor_get(x_40, 15);
lean_inc(x_63);
x_64 = lean_ctor_get(x_40, 16);
lean_inc(x_64);
x_65 = lean_ctor_get(x_40, 17);
lean_inc(x_65);
x_66 = lean_ctor_get(x_40, 18);
lean_inc(x_66);
x_67 = lean_ctor_get(x_40, 19);
lean_inc(x_67);
x_68 = lean_ctor_get(x_40, 20);
lean_inc(x_68);
x_69 = lean_ctor_get(x_40, 21);
lean_inc(x_69);
x_70 = lean_ctor_get(x_40, 22);
lean_inc(x_70);
x_71 = lean_ctor_get(x_40, 23);
lean_inc(x_71);
x_72 = lean_ctor_get(x_40, 24);
lean_inc(x_72);
x_73 = lean_ctor_get(x_40, 25);
lean_inc(x_73);
lean_dec(x_40);
x_74 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_74, 0, x_42);
lean_ctor_set(x_74, 1, x_48);
lean_ctor_set(x_74, 2, x_49);
lean_ctor_set(x_74, 3, x_50);
lean_ctor_set(x_74, 4, x_51);
lean_ctor_set(x_74, 5, x_52);
lean_ctor_set(x_74, 6, x_53);
lean_ctor_set(x_74, 7, x_55);
lean_ctor_set(x_74, 8, x_56);
lean_ctor_set(x_74, 9, x_57);
lean_ctor_set(x_74, 10, x_58);
lean_ctor_set(x_74, 11, x_59);
lean_ctor_set(x_74, 12, x_60);
lean_ctor_set(x_74, 13, x_61);
lean_ctor_set(x_74, 14, x_62);
lean_ctor_set(x_74, 15, x_63);
lean_ctor_set(x_74, 16, x_64);
lean_ctor_set(x_74, 17, x_65);
lean_ctor_set(x_74, 18, x_66);
lean_ctor_set(x_74, 19, x_67);
lean_ctor_set(x_74, 20, x_68);
lean_ctor_set(x_74, 21, x_69);
lean_ctor_set(x_74, 22, x_70);
lean_ctor_set(x_74, 23, x_71);
lean_ctor_set(x_74, 24, x_72);
lean_ctor_set(x_74, 25, x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*26, x_54);
x_75 = lean_st_ref_set(x_13, x_74, x_41);
lean_dec(x_13);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_75, 0);
lean_dec(x_77);
lean_ctor_set(x_75, 0, x_38);
return x_75;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_38);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
lean_dec(x_10);
lean_dec(x_9);
x_80 = lean_st_ref_take(x_13, x_29);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_84, 2);
lean_inc(x_87);
lean_dec(x_84);
lean_inc(x_1);
x_88 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_87, x_24, x_1);
x_89 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_89, 0, x_85);
lean_ctor_set(x_89, 1, x_86);
lean_ctor_set(x_89, 2, x_88);
x_90 = lean_ctor_get(x_81, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_81, 3);
lean_inc(x_91);
x_92 = lean_ctor_get(x_81, 4);
lean_inc(x_92);
x_93 = lean_ctor_get(x_81, 5);
lean_inc(x_93);
x_94 = lean_ctor_get(x_81, 6);
lean_inc(x_94);
x_95 = lean_ctor_get_uint8(x_81, sizeof(void*)*26);
x_96 = lean_ctor_get(x_81, 7);
lean_inc(x_96);
x_97 = lean_ctor_get(x_81, 8);
lean_inc(x_97);
x_98 = lean_ctor_get(x_81, 9);
lean_inc(x_98);
x_99 = lean_ctor_get(x_81, 10);
lean_inc(x_99);
x_100 = lean_ctor_get(x_81, 11);
lean_inc(x_100);
x_101 = lean_ctor_get(x_81, 12);
lean_inc(x_101);
x_102 = lean_ctor_get(x_81, 13);
lean_inc(x_102);
x_103 = lean_ctor_get(x_81, 14);
lean_inc(x_103);
x_104 = lean_ctor_get(x_81, 15);
lean_inc(x_104);
x_105 = lean_ctor_get(x_81, 16);
lean_inc(x_105);
x_106 = lean_ctor_get(x_81, 17);
lean_inc(x_106);
x_107 = lean_ctor_get(x_81, 18);
lean_inc(x_107);
x_108 = lean_ctor_get(x_81, 19);
lean_inc(x_108);
x_109 = lean_ctor_get(x_81, 20);
lean_inc(x_109);
x_110 = lean_ctor_get(x_81, 21);
lean_inc(x_110);
x_111 = lean_ctor_get(x_81, 22);
lean_inc(x_111);
x_112 = lean_ctor_get(x_81, 23);
lean_inc(x_112);
x_113 = lean_ctor_get(x_81, 24);
lean_inc(x_113);
x_114 = lean_ctor_get(x_81, 25);
lean_inc(x_114);
lean_dec(x_81);
x_115 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_115, 0, x_83);
lean_ctor_set(x_115, 1, x_89);
lean_ctor_set(x_115, 2, x_90);
lean_ctor_set(x_115, 3, x_91);
lean_ctor_set(x_115, 4, x_92);
lean_ctor_set(x_115, 5, x_93);
lean_ctor_set(x_115, 6, x_94);
lean_ctor_set(x_115, 7, x_96);
lean_ctor_set(x_115, 8, x_97);
lean_ctor_set(x_115, 9, x_98);
lean_ctor_set(x_115, 10, x_99);
lean_ctor_set(x_115, 11, x_100);
lean_ctor_set(x_115, 12, x_101);
lean_ctor_set(x_115, 13, x_102);
lean_ctor_set(x_115, 14, x_103);
lean_ctor_set(x_115, 15, x_104);
lean_ctor_set(x_115, 16, x_105);
lean_ctor_set(x_115, 17, x_106);
lean_ctor_set(x_115, 18, x_107);
lean_ctor_set(x_115, 19, x_108);
lean_ctor_set(x_115, 20, x_109);
lean_ctor_set(x_115, 21, x_110);
lean_ctor_set(x_115, 22, x_111);
lean_ctor_set(x_115, 23, x_112);
lean_ctor_set(x_115, 24, x_113);
lean_ctor_set(x_115, 25, x_114);
lean_ctor_set_uint8(x_115, sizeof(void*)*26, x_95);
x_116 = lean_st_ref_set(x_13, x_115, x_82);
lean_dec(x_13);
x_117 = !lean_is_exclusive(x_116);
if (x_117 == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_116, 0);
lean_dec(x_118);
lean_ctor_set(x_116, 0, x_1);
return x_116;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
lean_dec(x_116);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_1);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
lean_object* x_121; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_121 = lean_ctor_get(x_32, 0);
lean_inc(x_121);
lean_dec(x_32);
lean_ctor_set(x_26, 0, x_121);
return x_26;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_122 = lean_ctor_get(x_26, 0);
x_123 = lean_ctor_get(x_26, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_26);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_ctor_get(x_124, 2);
lean_inc(x_125);
lean_dec(x_124);
x_126 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_125, x_24);
if (lean_obj_tag(x_126) == 0)
{
size_t x_127; size_t x_128; uint8_t x_129; 
x_127 = lean_ptr_addr(x_22);
lean_dec(x_22);
x_128 = lean_ptr_addr(x_24);
x_129 = lean_usize_dec_eq(x_127, x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_1);
x_130 = lean_unsigned_to_nat(0u);
lean_inc(x_24);
x_131 = lean_array_set(x_10, x_130, x_24);
x_132 = l_Lean_mkAppN(x_9, x_131);
lean_dec(x_131);
x_133 = lean_st_ref_take(x_13, x_123);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_137, 2);
lean_inc(x_140);
lean_dec(x_137);
lean_inc(x_132);
x_141 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_140, x_24, x_132);
x_142 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_142, 0, x_138);
lean_ctor_set(x_142, 1, x_139);
lean_ctor_set(x_142, 2, x_141);
x_143 = lean_ctor_get(x_134, 2);
lean_inc(x_143);
x_144 = lean_ctor_get(x_134, 3);
lean_inc(x_144);
x_145 = lean_ctor_get(x_134, 4);
lean_inc(x_145);
x_146 = lean_ctor_get(x_134, 5);
lean_inc(x_146);
x_147 = lean_ctor_get(x_134, 6);
lean_inc(x_147);
x_148 = lean_ctor_get_uint8(x_134, sizeof(void*)*26);
x_149 = lean_ctor_get(x_134, 7);
lean_inc(x_149);
x_150 = lean_ctor_get(x_134, 8);
lean_inc(x_150);
x_151 = lean_ctor_get(x_134, 9);
lean_inc(x_151);
x_152 = lean_ctor_get(x_134, 10);
lean_inc(x_152);
x_153 = lean_ctor_get(x_134, 11);
lean_inc(x_153);
x_154 = lean_ctor_get(x_134, 12);
lean_inc(x_154);
x_155 = lean_ctor_get(x_134, 13);
lean_inc(x_155);
x_156 = lean_ctor_get(x_134, 14);
lean_inc(x_156);
x_157 = lean_ctor_get(x_134, 15);
lean_inc(x_157);
x_158 = lean_ctor_get(x_134, 16);
lean_inc(x_158);
x_159 = lean_ctor_get(x_134, 17);
lean_inc(x_159);
x_160 = lean_ctor_get(x_134, 18);
lean_inc(x_160);
x_161 = lean_ctor_get(x_134, 19);
lean_inc(x_161);
x_162 = lean_ctor_get(x_134, 20);
lean_inc(x_162);
x_163 = lean_ctor_get(x_134, 21);
lean_inc(x_163);
x_164 = lean_ctor_get(x_134, 22);
lean_inc(x_164);
x_165 = lean_ctor_get(x_134, 23);
lean_inc(x_165);
x_166 = lean_ctor_get(x_134, 24);
lean_inc(x_166);
x_167 = lean_ctor_get(x_134, 25);
lean_inc(x_167);
lean_dec(x_134);
x_168 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_168, 0, x_136);
lean_ctor_set(x_168, 1, x_142);
lean_ctor_set(x_168, 2, x_143);
lean_ctor_set(x_168, 3, x_144);
lean_ctor_set(x_168, 4, x_145);
lean_ctor_set(x_168, 5, x_146);
lean_ctor_set(x_168, 6, x_147);
lean_ctor_set(x_168, 7, x_149);
lean_ctor_set(x_168, 8, x_150);
lean_ctor_set(x_168, 9, x_151);
lean_ctor_set(x_168, 10, x_152);
lean_ctor_set(x_168, 11, x_153);
lean_ctor_set(x_168, 12, x_154);
lean_ctor_set(x_168, 13, x_155);
lean_ctor_set(x_168, 14, x_156);
lean_ctor_set(x_168, 15, x_157);
lean_ctor_set(x_168, 16, x_158);
lean_ctor_set(x_168, 17, x_159);
lean_ctor_set(x_168, 18, x_160);
lean_ctor_set(x_168, 19, x_161);
lean_ctor_set(x_168, 20, x_162);
lean_ctor_set(x_168, 21, x_163);
lean_ctor_set(x_168, 22, x_164);
lean_ctor_set(x_168, 23, x_165);
lean_ctor_set(x_168, 24, x_166);
lean_ctor_set(x_168, 25, x_167);
lean_ctor_set_uint8(x_168, sizeof(void*)*26, x_148);
x_169 = lean_st_ref_set(x_13, x_168, x_135);
lean_dec(x_13);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_171 = x_169;
} else {
 lean_dec_ref(x_169);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_132);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_10);
lean_dec(x_9);
x_173 = lean_st_ref_take(x_13, x_123);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_ctor_get(x_174, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_174, 1);
lean_inc(x_177);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
x_180 = lean_ctor_get(x_177, 2);
lean_inc(x_180);
lean_dec(x_177);
lean_inc(x_1);
x_181 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_180, x_24, x_1);
x_182 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_182, 0, x_178);
lean_ctor_set(x_182, 1, x_179);
lean_ctor_set(x_182, 2, x_181);
x_183 = lean_ctor_get(x_174, 2);
lean_inc(x_183);
x_184 = lean_ctor_get(x_174, 3);
lean_inc(x_184);
x_185 = lean_ctor_get(x_174, 4);
lean_inc(x_185);
x_186 = lean_ctor_get(x_174, 5);
lean_inc(x_186);
x_187 = lean_ctor_get(x_174, 6);
lean_inc(x_187);
x_188 = lean_ctor_get_uint8(x_174, sizeof(void*)*26);
x_189 = lean_ctor_get(x_174, 7);
lean_inc(x_189);
x_190 = lean_ctor_get(x_174, 8);
lean_inc(x_190);
x_191 = lean_ctor_get(x_174, 9);
lean_inc(x_191);
x_192 = lean_ctor_get(x_174, 10);
lean_inc(x_192);
x_193 = lean_ctor_get(x_174, 11);
lean_inc(x_193);
x_194 = lean_ctor_get(x_174, 12);
lean_inc(x_194);
x_195 = lean_ctor_get(x_174, 13);
lean_inc(x_195);
x_196 = lean_ctor_get(x_174, 14);
lean_inc(x_196);
x_197 = lean_ctor_get(x_174, 15);
lean_inc(x_197);
x_198 = lean_ctor_get(x_174, 16);
lean_inc(x_198);
x_199 = lean_ctor_get(x_174, 17);
lean_inc(x_199);
x_200 = lean_ctor_get(x_174, 18);
lean_inc(x_200);
x_201 = lean_ctor_get(x_174, 19);
lean_inc(x_201);
x_202 = lean_ctor_get(x_174, 20);
lean_inc(x_202);
x_203 = lean_ctor_get(x_174, 21);
lean_inc(x_203);
x_204 = lean_ctor_get(x_174, 22);
lean_inc(x_204);
x_205 = lean_ctor_get(x_174, 23);
lean_inc(x_205);
x_206 = lean_ctor_get(x_174, 24);
lean_inc(x_206);
x_207 = lean_ctor_get(x_174, 25);
lean_inc(x_207);
lean_dec(x_174);
x_208 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_208, 0, x_176);
lean_ctor_set(x_208, 1, x_182);
lean_ctor_set(x_208, 2, x_183);
lean_ctor_set(x_208, 3, x_184);
lean_ctor_set(x_208, 4, x_185);
lean_ctor_set(x_208, 5, x_186);
lean_ctor_set(x_208, 6, x_187);
lean_ctor_set(x_208, 7, x_189);
lean_ctor_set(x_208, 8, x_190);
lean_ctor_set(x_208, 9, x_191);
lean_ctor_set(x_208, 10, x_192);
lean_ctor_set(x_208, 11, x_193);
lean_ctor_set(x_208, 12, x_194);
lean_ctor_set(x_208, 13, x_195);
lean_ctor_set(x_208, 14, x_196);
lean_ctor_set(x_208, 15, x_197);
lean_ctor_set(x_208, 16, x_198);
lean_ctor_set(x_208, 17, x_199);
lean_ctor_set(x_208, 18, x_200);
lean_ctor_set(x_208, 19, x_201);
lean_ctor_set(x_208, 20, x_202);
lean_ctor_set(x_208, 21, x_203);
lean_ctor_set(x_208, 22, x_204);
lean_ctor_set(x_208, 23, x_205);
lean_ctor_set(x_208, 24, x_206);
lean_ctor_set(x_208, 25, x_207);
lean_ctor_set_uint8(x_208, sizeof(void*)*26, x_188);
x_209 = lean_st_ref_set(x_13, x_208, x_175);
lean_dec(x_13);
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_211 = x_209;
} else {
 lean_dec_ref(x_209);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_1);
lean_ctor_set(x_212, 1, x_210);
return x_212;
}
}
else
{
lean_object* x_213; lean_object* x_214; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_213 = lean_ctor_get(x_126, 0);
lean_inc(x_213);
lean_dec(x_126);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_123);
return x_214;
}
}
}
else
{
uint8_t x_215; 
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_215 = !lean_is_exclusive(x_23);
if (x_215 == 0)
{
return x_23;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_23, 0);
x_217 = lean_ctor_get(x_23, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_23);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
block_257:
{
lean_object* x_221; 
lean_dec(x_220);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_9);
x_221 = l_Lean_Meta_getFunInfo(x_9, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_224 = lean_ctor_get(x_222, 0);
lean_inc(x_224);
lean_dec(x_222);
x_225 = lean_array_get_size(x_10);
x_226 = lean_unsigned_to_nat(0u);
x_227 = lean_unsigned_to_nat(1u);
lean_inc(x_225);
x_228 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_225);
lean_ctor_set(x_228, 2, x_227);
x_229 = 0;
x_230 = lean_box(x_229);
lean_inc(x_10);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_10);
lean_ctor_set(x_231, 1, x_230);
x_232 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_228);
lean_inc(x_9);
lean_inc(x_1);
x_233 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_232, x_224, x_225, x_228, x_228, x_231, x_226, lean_box(0), lean_box(0), x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_223);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_234, 1);
lean_inc(x_235);
x_236 = lean_unbox(x_235);
lean_dec(x_235);
if (x_236 == 0)
{
uint8_t x_237; 
lean_dec(x_234);
lean_dec(x_9);
x_237 = !lean_is_exclusive(x_233);
if (x_237 == 0)
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_233, 0);
lean_dec(x_238);
lean_ctor_set(x_233, 0, x_1);
return x_233;
}
else
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_233, 1);
lean_inc(x_239);
lean_dec(x_233);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_1);
lean_ctor_set(x_240, 1, x_239);
return x_240;
}
}
else
{
uint8_t x_241; 
lean_dec(x_1);
x_241 = !lean_is_exclusive(x_233);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_233, 0);
lean_dec(x_242);
x_243 = lean_ctor_get(x_234, 0);
lean_inc(x_243);
lean_dec(x_234);
x_244 = l_Lean_mkAppN(x_9, x_243);
lean_dec(x_243);
lean_ctor_set(x_233, 0, x_244);
return x_233;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_245 = lean_ctor_get(x_233, 1);
lean_inc(x_245);
lean_dec(x_233);
x_246 = lean_ctor_get(x_234, 0);
lean_inc(x_246);
lean_dec(x_234);
x_247 = l_Lean_mkAppN(x_9, x_246);
lean_dec(x_246);
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_245);
return x_248;
}
}
}
else
{
uint8_t x_249; 
lean_dec(x_9);
lean_dec(x_1);
x_249 = !lean_is_exclusive(x_233);
if (x_249 == 0)
{
return x_233;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_233, 0);
x_251 = lean_ctor_get(x_233, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_233);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
}
}
else
{
uint8_t x_253; 
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
x_253 = !lean_is_exclusive(x_221);
if (x_253 == 0)
{
return x_221;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_221, 0);
x_255 = lean_ctor_get(x_221, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_221);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
}
case 1:
{
lean_object* x_270; lean_object* x_468; lean_object* x_506; uint8_t x_507; 
lean_dec(x_11);
x_506 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_507 = l_Lean_Expr_isConstOf(x_9, x_506);
if (x_507 == 0)
{
lean_object* x_508; 
x_508 = lean_box(0);
x_468 = x_508;
goto block_505;
}
else
{
lean_object* x_509; lean_object* x_510; uint8_t x_511; 
x_509 = lean_array_get_size(x_10);
x_510 = lean_unsigned_to_nat(2u);
x_511 = lean_nat_dec_eq(x_509, x_510);
if (x_511 == 0)
{
lean_object* x_512; 
lean_dec(x_509);
x_512 = lean_box(0);
x_468 = x_512;
goto block_505;
}
else
{
lean_object* x_513; uint8_t x_514; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_513 = lean_unsigned_to_nat(0u);
x_514 = lean_nat_dec_lt(x_513, x_509);
lean_dec(x_509);
if (x_514 == 0)
{
lean_object* x_515; lean_object* x_516; 
x_515 = l_Lean_instInhabitedExpr;
x_516 = l_outOfBounds___rarg(x_515);
x_270 = x_516;
goto block_467;
}
else
{
lean_object* x_517; 
x_517 = lean_array_fget(x_10, x_513);
x_270 = x_517;
goto block_467;
}
}
}
block_467:
{
lean_object* x_271; 
lean_inc(x_13);
lean_inc(x_270);
x_271 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_270, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
x_274 = lean_st_ref_get(x_13, x_273);
x_275 = !lean_is_exclusive(x_274);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_276 = lean_ctor_get(x_274, 0);
x_277 = lean_ctor_get(x_274, 1);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec(x_276);
x_279 = lean_ctor_get(x_278, 2);
lean_inc(x_279);
lean_dec(x_278);
x_280 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_279, x_272);
if (lean_obj_tag(x_280) == 0)
{
size_t x_281; size_t x_282; uint8_t x_283; 
lean_free_object(x_274);
x_281 = lean_ptr_addr(x_270);
lean_dec(x_270);
x_282 = lean_ptr_addr(x_272);
x_283 = lean_usize_dec_eq(x_281, x_282);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
lean_dec(x_1);
x_284 = lean_unsigned_to_nat(0u);
lean_inc(x_272);
x_285 = lean_array_set(x_10, x_284, x_272);
x_286 = l_Lean_mkAppN(x_9, x_285);
lean_dec(x_285);
x_287 = lean_st_ref_take(x_13, x_277);
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec(x_287);
x_290 = lean_ctor_get(x_288, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_288, 1);
lean_inc(x_291);
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
x_294 = lean_ctor_get(x_291, 2);
lean_inc(x_294);
lean_dec(x_291);
lean_inc(x_286);
x_295 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_294, x_272, x_286);
x_296 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_296, 0, x_292);
lean_ctor_set(x_296, 1, x_293);
lean_ctor_set(x_296, 2, x_295);
x_297 = lean_ctor_get(x_288, 2);
lean_inc(x_297);
x_298 = lean_ctor_get(x_288, 3);
lean_inc(x_298);
x_299 = lean_ctor_get(x_288, 4);
lean_inc(x_299);
x_300 = lean_ctor_get(x_288, 5);
lean_inc(x_300);
x_301 = lean_ctor_get(x_288, 6);
lean_inc(x_301);
x_302 = lean_ctor_get_uint8(x_288, sizeof(void*)*26);
x_303 = lean_ctor_get(x_288, 7);
lean_inc(x_303);
x_304 = lean_ctor_get(x_288, 8);
lean_inc(x_304);
x_305 = lean_ctor_get(x_288, 9);
lean_inc(x_305);
x_306 = lean_ctor_get(x_288, 10);
lean_inc(x_306);
x_307 = lean_ctor_get(x_288, 11);
lean_inc(x_307);
x_308 = lean_ctor_get(x_288, 12);
lean_inc(x_308);
x_309 = lean_ctor_get(x_288, 13);
lean_inc(x_309);
x_310 = lean_ctor_get(x_288, 14);
lean_inc(x_310);
x_311 = lean_ctor_get(x_288, 15);
lean_inc(x_311);
x_312 = lean_ctor_get(x_288, 16);
lean_inc(x_312);
x_313 = lean_ctor_get(x_288, 17);
lean_inc(x_313);
x_314 = lean_ctor_get(x_288, 18);
lean_inc(x_314);
x_315 = lean_ctor_get(x_288, 19);
lean_inc(x_315);
x_316 = lean_ctor_get(x_288, 20);
lean_inc(x_316);
x_317 = lean_ctor_get(x_288, 21);
lean_inc(x_317);
x_318 = lean_ctor_get(x_288, 22);
lean_inc(x_318);
x_319 = lean_ctor_get(x_288, 23);
lean_inc(x_319);
x_320 = lean_ctor_get(x_288, 24);
lean_inc(x_320);
x_321 = lean_ctor_get(x_288, 25);
lean_inc(x_321);
lean_dec(x_288);
x_322 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_322, 0, x_290);
lean_ctor_set(x_322, 1, x_296);
lean_ctor_set(x_322, 2, x_297);
lean_ctor_set(x_322, 3, x_298);
lean_ctor_set(x_322, 4, x_299);
lean_ctor_set(x_322, 5, x_300);
lean_ctor_set(x_322, 6, x_301);
lean_ctor_set(x_322, 7, x_303);
lean_ctor_set(x_322, 8, x_304);
lean_ctor_set(x_322, 9, x_305);
lean_ctor_set(x_322, 10, x_306);
lean_ctor_set(x_322, 11, x_307);
lean_ctor_set(x_322, 12, x_308);
lean_ctor_set(x_322, 13, x_309);
lean_ctor_set(x_322, 14, x_310);
lean_ctor_set(x_322, 15, x_311);
lean_ctor_set(x_322, 16, x_312);
lean_ctor_set(x_322, 17, x_313);
lean_ctor_set(x_322, 18, x_314);
lean_ctor_set(x_322, 19, x_315);
lean_ctor_set(x_322, 20, x_316);
lean_ctor_set(x_322, 21, x_317);
lean_ctor_set(x_322, 22, x_318);
lean_ctor_set(x_322, 23, x_319);
lean_ctor_set(x_322, 24, x_320);
lean_ctor_set(x_322, 25, x_321);
lean_ctor_set_uint8(x_322, sizeof(void*)*26, x_302);
x_323 = lean_st_ref_set(x_13, x_322, x_289);
lean_dec(x_13);
x_324 = !lean_is_exclusive(x_323);
if (x_324 == 0)
{
lean_object* x_325; 
x_325 = lean_ctor_get(x_323, 0);
lean_dec(x_325);
lean_ctor_set(x_323, 0, x_286);
return x_323;
}
else
{
lean_object* x_326; lean_object* x_327; 
x_326 = lean_ctor_get(x_323, 1);
lean_inc(x_326);
lean_dec(x_323);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_286);
lean_ctor_set(x_327, 1, x_326);
return x_327;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; uint8_t x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; uint8_t x_365; 
lean_dec(x_10);
lean_dec(x_9);
x_328 = lean_st_ref_take(x_13, x_277);
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
lean_dec(x_328);
x_331 = lean_ctor_get(x_329, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_329, 1);
lean_inc(x_332);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
x_335 = lean_ctor_get(x_332, 2);
lean_inc(x_335);
lean_dec(x_332);
lean_inc(x_1);
x_336 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_335, x_272, x_1);
x_337 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_337, 0, x_333);
lean_ctor_set(x_337, 1, x_334);
lean_ctor_set(x_337, 2, x_336);
x_338 = lean_ctor_get(x_329, 2);
lean_inc(x_338);
x_339 = lean_ctor_get(x_329, 3);
lean_inc(x_339);
x_340 = lean_ctor_get(x_329, 4);
lean_inc(x_340);
x_341 = lean_ctor_get(x_329, 5);
lean_inc(x_341);
x_342 = lean_ctor_get(x_329, 6);
lean_inc(x_342);
x_343 = lean_ctor_get_uint8(x_329, sizeof(void*)*26);
x_344 = lean_ctor_get(x_329, 7);
lean_inc(x_344);
x_345 = lean_ctor_get(x_329, 8);
lean_inc(x_345);
x_346 = lean_ctor_get(x_329, 9);
lean_inc(x_346);
x_347 = lean_ctor_get(x_329, 10);
lean_inc(x_347);
x_348 = lean_ctor_get(x_329, 11);
lean_inc(x_348);
x_349 = lean_ctor_get(x_329, 12);
lean_inc(x_349);
x_350 = lean_ctor_get(x_329, 13);
lean_inc(x_350);
x_351 = lean_ctor_get(x_329, 14);
lean_inc(x_351);
x_352 = lean_ctor_get(x_329, 15);
lean_inc(x_352);
x_353 = lean_ctor_get(x_329, 16);
lean_inc(x_353);
x_354 = lean_ctor_get(x_329, 17);
lean_inc(x_354);
x_355 = lean_ctor_get(x_329, 18);
lean_inc(x_355);
x_356 = lean_ctor_get(x_329, 19);
lean_inc(x_356);
x_357 = lean_ctor_get(x_329, 20);
lean_inc(x_357);
x_358 = lean_ctor_get(x_329, 21);
lean_inc(x_358);
x_359 = lean_ctor_get(x_329, 22);
lean_inc(x_359);
x_360 = lean_ctor_get(x_329, 23);
lean_inc(x_360);
x_361 = lean_ctor_get(x_329, 24);
lean_inc(x_361);
x_362 = lean_ctor_get(x_329, 25);
lean_inc(x_362);
lean_dec(x_329);
x_363 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_363, 0, x_331);
lean_ctor_set(x_363, 1, x_337);
lean_ctor_set(x_363, 2, x_338);
lean_ctor_set(x_363, 3, x_339);
lean_ctor_set(x_363, 4, x_340);
lean_ctor_set(x_363, 5, x_341);
lean_ctor_set(x_363, 6, x_342);
lean_ctor_set(x_363, 7, x_344);
lean_ctor_set(x_363, 8, x_345);
lean_ctor_set(x_363, 9, x_346);
lean_ctor_set(x_363, 10, x_347);
lean_ctor_set(x_363, 11, x_348);
lean_ctor_set(x_363, 12, x_349);
lean_ctor_set(x_363, 13, x_350);
lean_ctor_set(x_363, 14, x_351);
lean_ctor_set(x_363, 15, x_352);
lean_ctor_set(x_363, 16, x_353);
lean_ctor_set(x_363, 17, x_354);
lean_ctor_set(x_363, 18, x_355);
lean_ctor_set(x_363, 19, x_356);
lean_ctor_set(x_363, 20, x_357);
lean_ctor_set(x_363, 21, x_358);
lean_ctor_set(x_363, 22, x_359);
lean_ctor_set(x_363, 23, x_360);
lean_ctor_set(x_363, 24, x_361);
lean_ctor_set(x_363, 25, x_362);
lean_ctor_set_uint8(x_363, sizeof(void*)*26, x_343);
x_364 = lean_st_ref_set(x_13, x_363, x_330);
lean_dec(x_13);
x_365 = !lean_is_exclusive(x_364);
if (x_365 == 0)
{
lean_object* x_366; 
x_366 = lean_ctor_get(x_364, 0);
lean_dec(x_366);
lean_ctor_set(x_364, 0, x_1);
return x_364;
}
else
{
lean_object* x_367; lean_object* x_368; 
x_367 = lean_ctor_get(x_364, 1);
lean_inc(x_367);
lean_dec(x_364);
x_368 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_368, 0, x_1);
lean_ctor_set(x_368, 1, x_367);
return x_368;
}
}
}
else
{
lean_object* x_369; 
lean_dec(x_272);
lean_dec(x_270);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_369 = lean_ctor_get(x_280, 0);
lean_inc(x_369);
lean_dec(x_280);
lean_ctor_set(x_274, 0, x_369);
return x_274;
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_370 = lean_ctor_get(x_274, 0);
x_371 = lean_ctor_get(x_274, 1);
lean_inc(x_371);
lean_inc(x_370);
lean_dec(x_274);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
lean_dec(x_370);
x_373 = lean_ctor_get(x_372, 2);
lean_inc(x_373);
lean_dec(x_372);
x_374 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_373, x_272);
if (lean_obj_tag(x_374) == 0)
{
size_t x_375; size_t x_376; uint8_t x_377; 
x_375 = lean_ptr_addr(x_270);
lean_dec(x_270);
x_376 = lean_ptr_addr(x_272);
x_377 = lean_usize_dec_eq(x_375, x_376);
if (x_377 == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
lean_dec(x_1);
x_378 = lean_unsigned_to_nat(0u);
lean_inc(x_272);
x_379 = lean_array_set(x_10, x_378, x_272);
x_380 = l_Lean_mkAppN(x_9, x_379);
lean_dec(x_379);
x_381 = lean_st_ref_take(x_13, x_371);
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
lean_dec(x_381);
x_384 = lean_ctor_get(x_382, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_382, 1);
lean_inc(x_385);
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_385, 1);
lean_inc(x_387);
x_388 = lean_ctor_get(x_385, 2);
lean_inc(x_388);
lean_dec(x_385);
lean_inc(x_380);
x_389 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_388, x_272, x_380);
x_390 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_390, 0, x_386);
lean_ctor_set(x_390, 1, x_387);
lean_ctor_set(x_390, 2, x_389);
x_391 = lean_ctor_get(x_382, 2);
lean_inc(x_391);
x_392 = lean_ctor_get(x_382, 3);
lean_inc(x_392);
x_393 = lean_ctor_get(x_382, 4);
lean_inc(x_393);
x_394 = lean_ctor_get(x_382, 5);
lean_inc(x_394);
x_395 = lean_ctor_get(x_382, 6);
lean_inc(x_395);
x_396 = lean_ctor_get_uint8(x_382, sizeof(void*)*26);
x_397 = lean_ctor_get(x_382, 7);
lean_inc(x_397);
x_398 = lean_ctor_get(x_382, 8);
lean_inc(x_398);
x_399 = lean_ctor_get(x_382, 9);
lean_inc(x_399);
x_400 = lean_ctor_get(x_382, 10);
lean_inc(x_400);
x_401 = lean_ctor_get(x_382, 11);
lean_inc(x_401);
x_402 = lean_ctor_get(x_382, 12);
lean_inc(x_402);
x_403 = lean_ctor_get(x_382, 13);
lean_inc(x_403);
x_404 = lean_ctor_get(x_382, 14);
lean_inc(x_404);
x_405 = lean_ctor_get(x_382, 15);
lean_inc(x_405);
x_406 = lean_ctor_get(x_382, 16);
lean_inc(x_406);
x_407 = lean_ctor_get(x_382, 17);
lean_inc(x_407);
x_408 = lean_ctor_get(x_382, 18);
lean_inc(x_408);
x_409 = lean_ctor_get(x_382, 19);
lean_inc(x_409);
x_410 = lean_ctor_get(x_382, 20);
lean_inc(x_410);
x_411 = lean_ctor_get(x_382, 21);
lean_inc(x_411);
x_412 = lean_ctor_get(x_382, 22);
lean_inc(x_412);
x_413 = lean_ctor_get(x_382, 23);
lean_inc(x_413);
x_414 = lean_ctor_get(x_382, 24);
lean_inc(x_414);
x_415 = lean_ctor_get(x_382, 25);
lean_inc(x_415);
lean_dec(x_382);
x_416 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_416, 0, x_384);
lean_ctor_set(x_416, 1, x_390);
lean_ctor_set(x_416, 2, x_391);
lean_ctor_set(x_416, 3, x_392);
lean_ctor_set(x_416, 4, x_393);
lean_ctor_set(x_416, 5, x_394);
lean_ctor_set(x_416, 6, x_395);
lean_ctor_set(x_416, 7, x_397);
lean_ctor_set(x_416, 8, x_398);
lean_ctor_set(x_416, 9, x_399);
lean_ctor_set(x_416, 10, x_400);
lean_ctor_set(x_416, 11, x_401);
lean_ctor_set(x_416, 12, x_402);
lean_ctor_set(x_416, 13, x_403);
lean_ctor_set(x_416, 14, x_404);
lean_ctor_set(x_416, 15, x_405);
lean_ctor_set(x_416, 16, x_406);
lean_ctor_set(x_416, 17, x_407);
lean_ctor_set(x_416, 18, x_408);
lean_ctor_set(x_416, 19, x_409);
lean_ctor_set(x_416, 20, x_410);
lean_ctor_set(x_416, 21, x_411);
lean_ctor_set(x_416, 22, x_412);
lean_ctor_set(x_416, 23, x_413);
lean_ctor_set(x_416, 24, x_414);
lean_ctor_set(x_416, 25, x_415);
lean_ctor_set_uint8(x_416, sizeof(void*)*26, x_396);
x_417 = lean_st_ref_set(x_13, x_416, x_383);
lean_dec(x_13);
x_418 = lean_ctor_get(x_417, 1);
lean_inc(x_418);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 x_419 = x_417;
} else {
 lean_dec_ref(x_417);
 x_419 = lean_box(0);
}
if (lean_is_scalar(x_419)) {
 x_420 = lean_alloc_ctor(0, 2, 0);
} else {
 x_420 = x_419;
}
lean_ctor_set(x_420, 0, x_380);
lean_ctor_set(x_420, 1, x_418);
return x_420;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; uint8_t x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
lean_dec(x_10);
lean_dec(x_9);
x_421 = lean_st_ref_take(x_13, x_371);
x_422 = lean_ctor_get(x_421, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_421, 1);
lean_inc(x_423);
lean_dec(x_421);
x_424 = lean_ctor_get(x_422, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_422, 1);
lean_inc(x_425);
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_425, 1);
lean_inc(x_427);
x_428 = lean_ctor_get(x_425, 2);
lean_inc(x_428);
lean_dec(x_425);
lean_inc(x_1);
x_429 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_428, x_272, x_1);
x_430 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_430, 0, x_426);
lean_ctor_set(x_430, 1, x_427);
lean_ctor_set(x_430, 2, x_429);
x_431 = lean_ctor_get(x_422, 2);
lean_inc(x_431);
x_432 = lean_ctor_get(x_422, 3);
lean_inc(x_432);
x_433 = lean_ctor_get(x_422, 4);
lean_inc(x_433);
x_434 = lean_ctor_get(x_422, 5);
lean_inc(x_434);
x_435 = lean_ctor_get(x_422, 6);
lean_inc(x_435);
x_436 = lean_ctor_get_uint8(x_422, sizeof(void*)*26);
x_437 = lean_ctor_get(x_422, 7);
lean_inc(x_437);
x_438 = lean_ctor_get(x_422, 8);
lean_inc(x_438);
x_439 = lean_ctor_get(x_422, 9);
lean_inc(x_439);
x_440 = lean_ctor_get(x_422, 10);
lean_inc(x_440);
x_441 = lean_ctor_get(x_422, 11);
lean_inc(x_441);
x_442 = lean_ctor_get(x_422, 12);
lean_inc(x_442);
x_443 = lean_ctor_get(x_422, 13);
lean_inc(x_443);
x_444 = lean_ctor_get(x_422, 14);
lean_inc(x_444);
x_445 = lean_ctor_get(x_422, 15);
lean_inc(x_445);
x_446 = lean_ctor_get(x_422, 16);
lean_inc(x_446);
x_447 = lean_ctor_get(x_422, 17);
lean_inc(x_447);
x_448 = lean_ctor_get(x_422, 18);
lean_inc(x_448);
x_449 = lean_ctor_get(x_422, 19);
lean_inc(x_449);
x_450 = lean_ctor_get(x_422, 20);
lean_inc(x_450);
x_451 = lean_ctor_get(x_422, 21);
lean_inc(x_451);
x_452 = lean_ctor_get(x_422, 22);
lean_inc(x_452);
x_453 = lean_ctor_get(x_422, 23);
lean_inc(x_453);
x_454 = lean_ctor_get(x_422, 24);
lean_inc(x_454);
x_455 = lean_ctor_get(x_422, 25);
lean_inc(x_455);
lean_dec(x_422);
x_456 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_456, 0, x_424);
lean_ctor_set(x_456, 1, x_430);
lean_ctor_set(x_456, 2, x_431);
lean_ctor_set(x_456, 3, x_432);
lean_ctor_set(x_456, 4, x_433);
lean_ctor_set(x_456, 5, x_434);
lean_ctor_set(x_456, 6, x_435);
lean_ctor_set(x_456, 7, x_437);
lean_ctor_set(x_456, 8, x_438);
lean_ctor_set(x_456, 9, x_439);
lean_ctor_set(x_456, 10, x_440);
lean_ctor_set(x_456, 11, x_441);
lean_ctor_set(x_456, 12, x_442);
lean_ctor_set(x_456, 13, x_443);
lean_ctor_set(x_456, 14, x_444);
lean_ctor_set(x_456, 15, x_445);
lean_ctor_set(x_456, 16, x_446);
lean_ctor_set(x_456, 17, x_447);
lean_ctor_set(x_456, 18, x_448);
lean_ctor_set(x_456, 19, x_449);
lean_ctor_set(x_456, 20, x_450);
lean_ctor_set(x_456, 21, x_451);
lean_ctor_set(x_456, 22, x_452);
lean_ctor_set(x_456, 23, x_453);
lean_ctor_set(x_456, 24, x_454);
lean_ctor_set(x_456, 25, x_455);
lean_ctor_set_uint8(x_456, sizeof(void*)*26, x_436);
x_457 = lean_st_ref_set(x_13, x_456, x_423);
lean_dec(x_13);
x_458 = lean_ctor_get(x_457, 1);
lean_inc(x_458);
if (lean_is_exclusive(x_457)) {
 lean_ctor_release(x_457, 0);
 lean_ctor_release(x_457, 1);
 x_459 = x_457;
} else {
 lean_dec_ref(x_457);
 x_459 = lean_box(0);
}
if (lean_is_scalar(x_459)) {
 x_460 = lean_alloc_ctor(0, 2, 0);
} else {
 x_460 = x_459;
}
lean_ctor_set(x_460, 0, x_1);
lean_ctor_set(x_460, 1, x_458);
return x_460;
}
}
else
{
lean_object* x_461; lean_object* x_462; 
lean_dec(x_272);
lean_dec(x_270);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_461 = lean_ctor_get(x_374, 0);
lean_inc(x_461);
lean_dec(x_374);
x_462 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_462, 0, x_461);
lean_ctor_set(x_462, 1, x_371);
return x_462;
}
}
}
else
{
uint8_t x_463; 
lean_dec(x_270);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_463 = !lean_is_exclusive(x_271);
if (x_463 == 0)
{
return x_271;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_464 = lean_ctor_get(x_271, 0);
x_465 = lean_ctor_get(x_271, 1);
lean_inc(x_465);
lean_inc(x_464);
lean_dec(x_271);
x_466 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_466, 0, x_464);
lean_ctor_set(x_466, 1, x_465);
return x_466;
}
}
}
block_505:
{
lean_object* x_469; 
lean_dec(x_468);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_9);
x_469 = l_Lean_Meta_getFunInfo(x_9, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; uint8_t x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_469, 1);
lean_inc(x_471);
lean_dec(x_469);
x_472 = lean_ctor_get(x_470, 0);
lean_inc(x_472);
lean_dec(x_470);
x_473 = lean_array_get_size(x_10);
x_474 = lean_unsigned_to_nat(0u);
x_475 = lean_unsigned_to_nat(1u);
lean_inc(x_473);
x_476 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_476, 0, x_474);
lean_ctor_set(x_476, 1, x_473);
lean_ctor_set(x_476, 2, x_475);
x_477 = 0;
x_478 = lean_box(x_477);
lean_inc(x_10);
x_479 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_479, 0, x_10);
lean_ctor_set(x_479, 1, x_478);
x_480 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_476);
lean_inc(x_9);
lean_inc(x_1);
x_481 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_480, x_472, x_473, x_476, x_476, x_479, x_474, lean_box(0), lean_box(0), x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_471);
if (lean_obj_tag(x_481) == 0)
{
lean_object* x_482; lean_object* x_483; uint8_t x_484; 
x_482 = lean_ctor_get(x_481, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_482, 1);
lean_inc(x_483);
x_484 = lean_unbox(x_483);
lean_dec(x_483);
if (x_484 == 0)
{
uint8_t x_485; 
lean_dec(x_482);
lean_dec(x_9);
x_485 = !lean_is_exclusive(x_481);
if (x_485 == 0)
{
lean_object* x_486; 
x_486 = lean_ctor_get(x_481, 0);
lean_dec(x_486);
lean_ctor_set(x_481, 0, x_1);
return x_481;
}
else
{
lean_object* x_487; lean_object* x_488; 
x_487 = lean_ctor_get(x_481, 1);
lean_inc(x_487);
lean_dec(x_481);
x_488 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_488, 0, x_1);
lean_ctor_set(x_488, 1, x_487);
return x_488;
}
}
else
{
uint8_t x_489; 
lean_dec(x_1);
x_489 = !lean_is_exclusive(x_481);
if (x_489 == 0)
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_490 = lean_ctor_get(x_481, 0);
lean_dec(x_490);
x_491 = lean_ctor_get(x_482, 0);
lean_inc(x_491);
lean_dec(x_482);
x_492 = l_Lean_mkAppN(x_9, x_491);
lean_dec(x_491);
lean_ctor_set(x_481, 0, x_492);
return x_481;
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_493 = lean_ctor_get(x_481, 1);
lean_inc(x_493);
lean_dec(x_481);
x_494 = lean_ctor_get(x_482, 0);
lean_inc(x_494);
lean_dec(x_482);
x_495 = l_Lean_mkAppN(x_9, x_494);
lean_dec(x_494);
x_496 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_496, 0, x_495);
lean_ctor_set(x_496, 1, x_493);
return x_496;
}
}
}
else
{
uint8_t x_497; 
lean_dec(x_9);
lean_dec(x_1);
x_497 = !lean_is_exclusive(x_481);
if (x_497 == 0)
{
return x_481;
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_498 = lean_ctor_get(x_481, 0);
x_499 = lean_ctor_get(x_481, 1);
lean_inc(x_499);
lean_inc(x_498);
lean_dec(x_481);
x_500 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_500, 0, x_498);
lean_ctor_set(x_500, 1, x_499);
return x_500;
}
}
}
else
{
uint8_t x_501; 
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
x_501 = !lean_is_exclusive(x_469);
if (x_501 == 0)
{
return x_469;
}
else
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_502 = lean_ctor_get(x_469, 0);
x_503 = lean_ctor_get(x_469, 1);
lean_inc(x_503);
lean_inc(x_502);
lean_dec(x_469);
x_504 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_504, 0, x_502);
lean_ctor_set(x_504, 1, x_503);
return x_504;
}
}
}
}
case 2:
{
lean_object* x_518; lean_object* x_716; lean_object* x_754; uint8_t x_755; 
lean_dec(x_11);
x_754 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_755 = l_Lean_Expr_isConstOf(x_9, x_754);
if (x_755 == 0)
{
lean_object* x_756; 
x_756 = lean_box(0);
x_716 = x_756;
goto block_753;
}
else
{
lean_object* x_757; lean_object* x_758; uint8_t x_759; 
x_757 = lean_array_get_size(x_10);
x_758 = lean_unsigned_to_nat(2u);
x_759 = lean_nat_dec_eq(x_757, x_758);
if (x_759 == 0)
{
lean_object* x_760; 
lean_dec(x_757);
x_760 = lean_box(0);
x_716 = x_760;
goto block_753;
}
else
{
lean_object* x_761; uint8_t x_762; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_761 = lean_unsigned_to_nat(0u);
x_762 = lean_nat_dec_lt(x_761, x_757);
lean_dec(x_757);
if (x_762 == 0)
{
lean_object* x_763; lean_object* x_764; 
x_763 = l_Lean_instInhabitedExpr;
x_764 = l_outOfBounds___rarg(x_763);
x_518 = x_764;
goto block_715;
}
else
{
lean_object* x_765; 
x_765 = lean_array_fget(x_10, x_761);
x_518 = x_765;
goto block_715;
}
}
}
block_715:
{
lean_object* x_519; 
lean_inc(x_13);
lean_inc(x_518);
x_519 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_518, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_519) == 0)
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; uint8_t x_523; 
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_519, 1);
lean_inc(x_521);
lean_dec(x_519);
x_522 = lean_st_ref_get(x_13, x_521);
x_523 = !lean_is_exclusive(x_522);
if (x_523 == 0)
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_524 = lean_ctor_get(x_522, 0);
x_525 = lean_ctor_get(x_522, 1);
x_526 = lean_ctor_get(x_524, 1);
lean_inc(x_526);
lean_dec(x_524);
x_527 = lean_ctor_get(x_526, 2);
lean_inc(x_527);
lean_dec(x_526);
x_528 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_527, x_520);
if (lean_obj_tag(x_528) == 0)
{
size_t x_529; size_t x_530; uint8_t x_531; 
lean_free_object(x_522);
x_529 = lean_ptr_addr(x_518);
lean_dec(x_518);
x_530 = lean_ptr_addr(x_520);
x_531 = lean_usize_dec_eq(x_529, x_530);
if (x_531 == 0)
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; uint8_t x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; uint8_t x_572; 
lean_dec(x_1);
x_532 = lean_unsigned_to_nat(0u);
lean_inc(x_520);
x_533 = lean_array_set(x_10, x_532, x_520);
x_534 = l_Lean_mkAppN(x_9, x_533);
lean_dec(x_533);
x_535 = lean_st_ref_take(x_13, x_525);
x_536 = lean_ctor_get(x_535, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_535, 1);
lean_inc(x_537);
lean_dec(x_535);
x_538 = lean_ctor_get(x_536, 0);
lean_inc(x_538);
x_539 = lean_ctor_get(x_536, 1);
lean_inc(x_539);
x_540 = lean_ctor_get(x_539, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_539, 1);
lean_inc(x_541);
x_542 = lean_ctor_get(x_539, 2);
lean_inc(x_542);
lean_dec(x_539);
lean_inc(x_534);
x_543 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_542, x_520, x_534);
x_544 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_544, 0, x_540);
lean_ctor_set(x_544, 1, x_541);
lean_ctor_set(x_544, 2, x_543);
x_545 = lean_ctor_get(x_536, 2);
lean_inc(x_545);
x_546 = lean_ctor_get(x_536, 3);
lean_inc(x_546);
x_547 = lean_ctor_get(x_536, 4);
lean_inc(x_547);
x_548 = lean_ctor_get(x_536, 5);
lean_inc(x_548);
x_549 = lean_ctor_get(x_536, 6);
lean_inc(x_549);
x_550 = lean_ctor_get_uint8(x_536, sizeof(void*)*26);
x_551 = lean_ctor_get(x_536, 7);
lean_inc(x_551);
x_552 = lean_ctor_get(x_536, 8);
lean_inc(x_552);
x_553 = lean_ctor_get(x_536, 9);
lean_inc(x_553);
x_554 = lean_ctor_get(x_536, 10);
lean_inc(x_554);
x_555 = lean_ctor_get(x_536, 11);
lean_inc(x_555);
x_556 = lean_ctor_get(x_536, 12);
lean_inc(x_556);
x_557 = lean_ctor_get(x_536, 13);
lean_inc(x_557);
x_558 = lean_ctor_get(x_536, 14);
lean_inc(x_558);
x_559 = lean_ctor_get(x_536, 15);
lean_inc(x_559);
x_560 = lean_ctor_get(x_536, 16);
lean_inc(x_560);
x_561 = lean_ctor_get(x_536, 17);
lean_inc(x_561);
x_562 = lean_ctor_get(x_536, 18);
lean_inc(x_562);
x_563 = lean_ctor_get(x_536, 19);
lean_inc(x_563);
x_564 = lean_ctor_get(x_536, 20);
lean_inc(x_564);
x_565 = lean_ctor_get(x_536, 21);
lean_inc(x_565);
x_566 = lean_ctor_get(x_536, 22);
lean_inc(x_566);
x_567 = lean_ctor_get(x_536, 23);
lean_inc(x_567);
x_568 = lean_ctor_get(x_536, 24);
lean_inc(x_568);
x_569 = lean_ctor_get(x_536, 25);
lean_inc(x_569);
lean_dec(x_536);
x_570 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_570, 0, x_538);
lean_ctor_set(x_570, 1, x_544);
lean_ctor_set(x_570, 2, x_545);
lean_ctor_set(x_570, 3, x_546);
lean_ctor_set(x_570, 4, x_547);
lean_ctor_set(x_570, 5, x_548);
lean_ctor_set(x_570, 6, x_549);
lean_ctor_set(x_570, 7, x_551);
lean_ctor_set(x_570, 8, x_552);
lean_ctor_set(x_570, 9, x_553);
lean_ctor_set(x_570, 10, x_554);
lean_ctor_set(x_570, 11, x_555);
lean_ctor_set(x_570, 12, x_556);
lean_ctor_set(x_570, 13, x_557);
lean_ctor_set(x_570, 14, x_558);
lean_ctor_set(x_570, 15, x_559);
lean_ctor_set(x_570, 16, x_560);
lean_ctor_set(x_570, 17, x_561);
lean_ctor_set(x_570, 18, x_562);
lean_ctor_set(x_570, 19, x_563);
lean_ctor_set(x_570, 20, x_564);
lean_ctor_set(x_570, 21, x_565);
lean_ctor_set(x_570, 22, x_566);
lean_ctor_set(x_570, 23, x_567);
lean_ctor_set(x_570, 24, x_568);
lean_ctor_set(x_570, 25, x_569);
lean_ctor_set_uint8(x_570, sizeof(void*)*26, x_550);
x_571 = lean_st_ref_set(x_13, x_570, x_537);
lean_dec(x_13);
x_572 = !lean_is_exclusive(x_571);
if (x_572 == 0)
{
lean_object* x_573; 
x_573 = lean_ctor_get(x_571, 0);
lean_dec(x_573);
lean_ctor_set(x_571, 0, x_534);
return x_571;
}
else
{
lean_object* x_574; lean_object* x_575; 
x_574 = lean_ctor_get(x_571, 1);
lean_inc(x_574);
lean_dec(x_571);
x_575 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_575, 0, x_534);
lean_ctor_set(x_575, 1, x_574);
return x_575;
}
}
else
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; uint8_t x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; uint8_t x_613; 
lean_dec(x_10);
lean_dec(x_9);
x_576 = lean_st_ref_take(x_13, x_525);
x_577 = lean_ctor_get(x_576, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_576, 1);
lean_inc(x_578);
lean_dec(x_576);
x_579 = lean_ctor_get(x_577, 0);
lean_inc(x_579);
x_580 = lean_ctor_get(x_577, 1);
lean_inc(x_580);
x_581 = lean_ctor_get(x_580, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_580, 1);
lean_inc(x_582);
x_583 = lean_ctor_get(x_580, 2);
lean_inc(x_583);
lean_dec(x_580);
lean_inc(x_1);
x_584 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_583, x_520, x_1);
x_585 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_585, 0, x_581);
lean_ctor_set(x_585, 1, x_582);
lean_ctor_set(x_585, 2, x_584);
x_586 = lean_ctor_get(x_577, 2);
lean_inc(x_586);
x_587 = lean_ctor_get(x_577, 3);
lean_inc(x_587);
x_588 = lean_ctor_get(x_577, 4);
lean_inc(x_588);
x_589 = lean_ctor_get(x_577, 5);
lean_inc(x_589);
x_590 = lean_ctor_get(x_577, 6);
lean_inc(x_590);
x_591 = lean_ctor_get_uint8(x_577, sizeof(void*)*26);
x_592 = lean_ctor_get(x_577, 7);
lean_inc(x_592);
x_593 = lean_ctor_get(x_577, 8);
lean_inc(x_593);
x_594 = lean_ctor_get(x_577, 9);
lean_inc(x_594);
x_595 = lean_ctor_get(x_577, 10);
lean_inc(x_595);
x_596 = lean_ctor_get(x_577, 11);
lean_inc(x_596);
x_597 = lean_ctor_get(x_577, 12);
lean_inc(x_597);
x_598 = lean_ctor_get(x_577, 13);
lean_inc(x_598);
x_599 = lean_ctor_get(x_577, 14);
lean_inc(x_599);
x_600 = lean_ctor_get(x_577, 15);
lean_inc(x_600);
x_601 = lean_ctor_get(x_577, 16);
lean_inc(x_601);
x_602 = lean_ctor_get(x_577, 17);
lean_inc(x_602);
x_603 = lean_ctor_get(x_577, 18);
lean_inc(x_603);
x_604 = lean_ctor_get(x_577, 19);
lean_inc(x_604);
x_605 = lean_ctor_get(x_577, 20);
lean_inc(x_605);
x_606 = lean_ctor_get(x_577, 21);
lean_inc(x_606);
x_607 = lean_ctor_get(x_577, 22);
lean_inc(x_607);
x_608 = lean_ctor_get(x_577, 23);
lean_inc(x_608);
x_609 = lean_ctor_get(x_577, 24);
lean_inc(x_609);
x_610 = lean_ctor_get(x_577, 25);
lean_inc(x_610);
lean_dec(x_577);
x_611 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_611, 0, x_579);
lean_ctor_set(x_611, 1, x_585);
lean_ctor_set(x_611, 2, x_586);
lean_ctor_set(x_611, 3, x_587);
lean_ctor_set(x_611, 4, x_588);
lean_ctor_set(x_611, 5, x_589);
lean_ctor_set(x_611, 6, x_590);
lean_ctor_set(x_611, 7, x_592);
lean_ctor_set(x_611, 8, x_593);
lean_ctor_set(x_611, 9, x_594);
lean_ctor_set(x_611, 10, x_595);
lean_ctor_set(x_611, 11, x_596);
lean_ctor_set(x_611, 12, x_597);
lean_ctor_set(x_611, 13, x_598);
lean_ctor_set(x_611, 14, x_599);
lean_ctor_set(x_611, 15, x_600);
lean_ctor_set(x_611, 16, x_601);
lean_ctor_set(x_611, 17, x_602);
lean_ctor_set(x_611, 18, x_603);
lean_ctor_set(x_611, 19, x_604);
lean_ctor_set(x_611, 20, x_605);
lean_ctor_set(x_611, 21, x_606);
lean_ctor_set(x_611, 22, x_607);
lean_ctor_set(x_611, 23, x_608);
lean_ctor_set(x_611, 24, x_609);
lean_ctor_set(x_611, 25, x_610);
lean_ctor_set_uint8(x_611, sizeof(void*)*26, x_591);
x_612 = lean_st_ref_set(x_13, x_611, x_578);
lean_dec(x_13);
x_613 = !lean_is_exclusive(x_612);
if (x_613 == 0)
{
lean_object* x_614; 
x_614 = lean_ctor_get(x_612, 0);
lean_dec(x_614);
lean_ctor_set(x_612, 0, x_1);
return x_612;
}
else
{
lean_object* x_615; lean_object* x_616; 
x_615 = lean_ctor_get(x_612, 1);
lean_inc(x_615);
lean_dec(x_612);
x_616 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_616, 0, x_1);
lean_ctor_set(x_616, 1, x_615);
return x_616;
}
}
}
else
{
lean_object* x_617; 
lean_dec(x_520);
lean_dec(x_518);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_617 = lean_ctor_get(x_528, 0);
lean_inc(x_617);
lean_dec(x_528);
lean_ctor_set(x_522, 0, x_617);
return x_522;
}
}
else
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; 
x_618 = lean_ctor_get(x_522, 0);
x_619 = lean_ctor_get(x_522, 1);
lean_inc(x_619);
lean_inc(x_618);
lean_dec(x_522);
x_620 = lean_ctor_get(x_618, 1);
lean_inc(x_620);
lean_dec(x_618);
x_621 = lean_ctor_get(x_620, 2);
lean_inc(x_621);
lean_dec(x_620);
x_622 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_621, x_520);
if (lean_obj_tag(x_622) == 0)
{
size_t x_623; size_t x_624; uint8_t x_625; 
x_623 = lean_ptr_addr(x_518);
lean_dec(x_518);
x_624 = lean_ptr_addr(x_520);
x_625 = lean_usize_dec_eq(x_623, x_624);
if (x_625 == 0)
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; uint8_t x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; 
lean_dec(x_1);
x_626 = lean_unsigned_to_nat(0u);
lean_inc(x_520);
x_627 = lean_array_set(x_10, x_626, x_520);
x_628 = l_Lean_mkAppN(x_9, x_627);
lean_dec(x_627);
x_629 = lean_st_ref_take(x_13, x_619);
x_630 = lean_ctor_get(x_629, 0);
lean_inc(x_630);
x_631 = lean_ctor_get(x_629, 1);
lean_inc(x_631);
lean_dec(x_629);
x_632 = lean_ctor_get(x_630, 0);
lean_inc(x_632);
x_633 = lean_ctor_get(x_630, 1);
lean_inc(x_633);
x_634 = lean_ctor_get(x_633, 0);
lean_inc(x_634);
x_635 = lean_ctor_get(x_633, 1);
lean_inc(x_635);
x_636 = lean_ctor_get(x_633, 2);
lean_inc(x_636);
lean_dec(x_633);
lean_inc(x_628);
x_637 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_636, x_520, x_628);
x_638 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_638, 0, x_634);
lean_ctor_set(x_638, 1, x_635);
lean_ctor_set(x_638, 2, x_637);
x_639 = lean_ctor_get(x_630, 2);
lean_inc(x_639);
x_640 = lean_ctor_get(x_630, 3);
lean_inc(x_640);
x_641 = lean_ctor_get(x_630, 4);
lean_inc(x_641);
x_642 = lean_ctor_get(x_630, 5);
lean_inc(x_642);
x_643 = lean_ctor_get(x_630, 6);
lean_inc(x_643);
x_644 = lean_ctor_get_uint8(x_630, sizeof(void*)*26);
x_645 = lean_ctor_get(x_630, 7);
lean_inc(x_645);
x_646 = lean_ctor_get(x_630, 8);
lean_inc(x_646);
x_647 = lean_ctor_get(x_630, 9);
lean_inc(x_647);
x_648 = lean_ctor_get(x_630, 10);
lean_inc(x_648);
x_649 = lean_ctor_get(x_630, 11);
lean_inc(x_649);
x_650 = lean_ctor_get(x_630, 12);
lean_inc(x_650);
x_651 = lean_ctor_get(x_630, 13);
lean_inc(x_651);
x_652 = lean_ctor_get(x_630, 14);
lean_inc(x_652);
x_653 = lean_ctor_get(x_630, 15);
lean_inc(x_653);
x_654 = lean_ctor_get(x_630, 16);
lean_inc(x_654);
x_655 = lean_ctor_get(x_630, 17);
lean_inc(x_655);
x_656 = lean_ctor_get(x_630, 18);
lean_inc(x_656);
x_657 = lean_ctor_get(x_630, 19);
lean_inc(x_657);
x_658 = lean_ctor_get(x_630, 20);
lean_inc(x_658);
x_659 = lean_ctor_get(x_630, 21);
lean_inc(x_659);
x_660 = lean_ctor_get(x_630, 22);
lean_inc(x_660);
x_661 = lean_ctor_get(x_630, 23);
lean_inc(x_661);
x_662 = lean_ctor_get(x_630, 24);
lean_inc(x_662);
x_663 = lean_ctor_get(x_630, 25);
lean_inc(x_663);
lean_dec(x_630);
x_664 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_664, 0, x_632);
lean_ctor_set(x_664, 1, x_638);
lean_ctor_set(x_664, 2, x_639);
lean_ctor_set(x_664, 3, x_640);
lean_ctor_set(x_664, 4, x_641);
lean_ctor_set(x_664, 5, x_642);
lean_ctor_set(x_664, 6, x_643);
lean_ctor_set(x_664, 7, x_645);
lean_ctor_set(x_664, 8, x_646);
lean_ctor_set(x_664, 9, x_647);
lean_ctor_set(x_664, 10, x_648);
lean_ctor_set(x_664, 11, x_649);
lean_ctor_set(x_664, 12, x_650);
lean_ctor_set(x_664, 13, x_651);
lean_ctor_set(x_664, 14, x_652);
lean_ctor_set(x_664, 15, x_653);
lean_ctor_set(x_664, 16, x_654);
lean_ctor_set(x_664, 17, x_655);
lean_ctor_set(x_664, 18, x_656);
lean_ctor_set(x_664, 19, x_657);
lean_ctor_set(x_664, 20, x_658);
lean_ctor_set(x_664, 21, x_659);
lean_ctor_set(x_664, 22, x_660);
lean_ctor_set(x_664, 23, x_661);
lean_ctor_set(x_664, 24, x_662);
lean_ctor_set(x_664, 25, x_663);
lean_ctor_set_uint8(x_664, sizeof(void*)*26, x_644);
x_665 = lean_st_ref_set(x_13, x_664, x_631);
lean_dec(x_13);
x_666 = lean_ctor_get(x_665, 1);
lean_inc(x_666);
if (lean_is_exclusive(x_665)) {
 lean_ctor_release(x_665, 0);
 lean_ctor_release(x_665, 1);
 x_667 = x_665;
} else {
 lean_dec_ref(x_665);
 x_667 = lean_box(0);
}
if (lean_is_scalar(x_667)) {
 x_668 = lean_alloc_ctor(0, 2, 0);
} else {
 x_668 = x_667;
}
lean_ctor_set(x_668, 0, x_628);
lean_ctor_set(x_668, 1, x_666);
return x_668;
}
else
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; uint8_t x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; 
lean_dec(x_10);
lean_dec(x_9);
x_669 = lean_st_ref_take(x_13, x_619);
x_670 = lean_ctor_get(x_669, 0);
lean_inc(x_670);
x_671 = lean_ctor_get(x_669, 1);
lean_inc(x_671);
lean_dec(x_669);
x_672 = lean_ctor_get(x_670, 0);
lean_inc(x_672);
x_673 = lean_ctor_get(x_670, 1);
lean_inc(x_673);
x_674 = lean_ctor_get(x_673, 0);
lean_inc(x_674);
x_675 = lean_ctor_get(x_673, 1);
lean_inc(x_675);
x_676 = lean_ctor_get(x_673, 2);
lean_inc(x_676);
lean_dec(x_673);
lean_inc(x_1);
x_677 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_676, x_520, x_1);
x_678 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_678, 0, x_674);
lean_ctor_set(x_678, 1, x_675);
lean_ctor_set(x_678, 2, x_677);
x_679 = lean_ctor_get(x_670, 2);
lean_inc(x_679);
x_680 = lean_ctor_get(x_670, 3);
lean_inc(x_680);
x_681 = lean_ctor_get(x_670, 4);
lean_inc(x_681);
x_682 = lean_ctor_get(x_670, 5);
lean_inc(x_682);
x_683 = lean_ctor_get(x_670, 6);
lean_inc(x_683);
x_684 = lean_ctor_get_uint8(x_670, sizeof(void*)*26);
x_685 = lean_ctor_get(x_670, 7);
lean_inc(x_685);
x_686 = lean_ctor_get(x_670, 8);
lean_inc(x_686);
x_687 = lean_ctor_get(x_670, 9);
lean_inc(x_687);
x_688 = lean_ctor_get(x_670, 10);
lean_inc(x_688);
x_689 = lean_ctor_get(x_670, 11);
lean_inc(x_689);
x_690 = lean_ctor_get(x_670, 12);
lean_inc(x_690);
x_691 = lean_ctor_get(x_670, 13);
lean_inc(x_691);
x_692 = lean_ctor_get(x_670, 14);
lean_inc(x_692);
x_693 = lean_ctor_get(x_670, 15);
lean_inc(x_693);
x_694 = lean_ctor_get(x_670, 16);
lean_inc(x_694);
x_695 = lean_ctor_get(x_670, 17);
lean_inc(x_695);
x_696 = lean_ctor_get(x_670, 18);
lean_inc(x_696);
x_697 = lean_ctor_get(x_670, 19);
lean_inc(x_697);
x_698 = lean_ctor_get(x_670, 20);
lean_inc(x_698);
x_699 = lean_ctor_get(x_670, 21);
lean_inc(x_699);
x_700 = lean_ctor_get(x_670, 22);
lean_inc(x_700);
x_701 = lean_ctor_get(x_670, 23);
lean_inc(x_701);
x_702 = lean_ctor_get(x_670, 24);
lean_inc(x_702);
x_703 = lean_ctor_get(x_670, 25);
lean_inc(x_703);
lean_dec(x_670);
x_704 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_704, 0, x_672);
lean_ctor_set(x_704, 1, x_678);
lean_ctor_set(x_704, 2, x_679);
lean_ctor_set(x_704, 3, x_680);
lean_ctor_set(x_704, 4, x_681);
lean_ctor_set(x_704, 5, x_682);
lean_ctor_set(x_704, 6, x_683);
lean_ctor_set(x_704, 7, x_685);
lean_ctor_set(x_704, 8, x_686);
lean_ctor_set(x_704, 9, x_687);
lean_ctor_set(x_704, 10, x_688);
lean_ctor_set(x_704, 11, x_689);
lean_ctor_set(x_704, 12, x_690);
lean_ctor_set(x_704, 13, x_691);
lean_ctor_set(x_704, 14, x_692);
lean_ctor_set(x_704, 15, x_693);
lean_ctor_set(x_704, 16, x_694);
lean_ctor_set(x_704, 17, x_695);
lean_ctor_set(x_704, 18, x_696);
lean_ctor_set(x_704, 19, x_697);
lean_ctor_set(x_704, 20, x_698);
lean_ctor_set(x_704, 21, x_699);
lean_ctor_set(x_704, 22, x_700);
lean_ctor_set(x_704, 23, x_701);
lean_ctor_set(x_704, 24, x_702);
lean_ctor_set(x_704, 25, x_703);
lean_ctor_set_uint8(x_704, sizeof(void*)*26, x_684);
x_705 = lean_st_ref_set(x_13, x_704, x_671);
lean_dec(x_13);
x_706 = lean_ctor_get(x_705, 1);
lean_inc(x_706);
if (lean_is_exclusive(x_705)) {
 lean_ctor_release(x_705, 0);
 lean_ctor_release(x_705, 1);
 x_707 = x_705;
} else {
 lean_dec_ref(x_705);
 x_707 = lean_box(0);
}
if (lean_is_scalar(x_707)) {
 x_708 = lean_alloc_ctor(0, 2, 0);
} else {
 x_708 = x_707;
}
lean_ctor_set(x_708, 0, x_1);
lean_ctor_set(x_708, 1, x_706);
return x_708;
}
}
else
{
lean_object* x_709; lean_object* x_710; 
lean_dec(x_520);
lean_dec(x_518);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_709 = lean_ctor_get(x_622, 0);
lean_inc(x_709);
lean_dec(x_622);
x_710 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_710, 0, x_709);
lean_ctor_set(x_710, 1, x_619);
return x_710;
}
}
}
else
{
uint8_t x_711; 
lean_dec(x_518);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_711 = !lean_is_exclusive(x_519);
if (x_711 == 0)
{
return x_519;
}
else
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; 
x_712 = lean_ctor_get(x_519, 0);
x_713 = lean_ctor_get(x_519, 1);
lean_inc(x_713);
lean_inc(x_712);
lean_dec(x_519);
x_714 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_714, 0, x_712);
lean_ctor_set(x_714, 1, x_713);
return x_714;
}
}
}
block_753:
{
lean_object* x_717; 
lean_dec(x_716);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_9);
x_717 = l_Lean_Meta_getFunInfo(x_9, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_717) == 0)
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; uint8_t x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; 
x_718 = lean_ctor_get(x_717, 0);
lean_inc(x_718);
x_719 = lean_ctor_get(x_717, 1);
lean_inc(x_719);
lean_dec(x_717);
x_720 = lean_ctor_get(x_718, 0);
lean_inc(x_720);
lean_dec(x_718);
x_721 = lean_array_get_size(x_10);
x_722 = lean_unsigned_to_nat(0u);
x_723 = lean_unsigned_to_nat(1u);
lean_inc(x_721);
x_724 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_724, 0, x_722);
lean_ctor_set(x_724, 1, x_721);
lean_ctor_set(x_724, 2, x_723);
x_725 = 0;
x_726 = lean_box(x_725);
lean_inc(x_10);
x_727 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_727, 0, x_10);
lean_ctor_set(x_727, 1, x_726);
x_728 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_724);
lean_inc(x_9);
lean_inc(x_1);
x_729 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_728, x_720, x_721, x_724, x_724, x_727, x_722, lean_box(0), lean_box(0), x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_719);
if (lean_obj_tag(x_729) == 0)
{
lean_object* x_730; lean_object* x_731; uint8_t x_732; 
x_730 = lean_ctor_get(x_729, 0);
lean_inc(x_730);
x_731 = lean_ctor_get(x_730, 1);
lean_inc(x_731);
x_732 = lean_unbox(x_731);
lean_dec(x_731);
if (x_732 == 0)
{
uint8_t x_733; 
lean_dec(x_730);
lean_dec(x_9);
x_733 = !lean_is_exclusive(x_729);
if (x_733 == 0)
{
lean_object* x_734; 
x_734 = lean_ctor_get(x_729, 0);
lean_dec(x_734);
lean_ctor_set(x_729, 0, x_1);
return x_729;
}
else
{
lean_object* x_735; lean_object* x_736; 
x_735 = lean_ctor_get(x_729, 1);
lean_inc(x_735);
lean_dec(x_729);
x_736 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_736, 0, x_1);
lean_ctor_set(x_736, 1, x_735);
return x_736;
}
}
else
{
uint8_t x_737; 
lean_dec(x_1);
x_737 = !lean_is_exclusive(x_729);
if (x_737 == 0)
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; 
x_738 = lean_ctor_get(x_729, 0);
lean_dec(x_738);
x_739 = lean_ctor_get(x_730, 0);
lean_inc(x_739);
lean_dec(x_730);
x_740 = l_Lean_mkAppN(x_9, x_739);
lean_dec(x_739);
lean_ctor_set(x_729, 0, x_740);
return x_729;
}
else
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; 
x_741 = lean_ctor_get(x_729, 1);
lean_inc(x_741);
lean_dec(x_729);
x_742 = lean_ctor_get(x_730, 0);
lean_inc(x_742);
lean_dec(x_730);
x_743 = l_Lean_mkAppN(x_9, x_742);
lean_dec(x_742);
x_744 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_744, 0, x_743);
lean_ctor_set(x_744, 1, x_741);
return x_744;
}
}
}
else
{
uint8_t x_745; 
lean_dec(x_9);
lean_dec(x_1);
x_745 = !lean_is_exclusive(x_729);
if (x_745 == 0)
{
return x_729;
}
else
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; 
x_746 = lean_ctor_get(x_729, 0);
x_747 = lean_ctor_get(x_729, 1);
lean_inc(x_747);
lean_inc(x_746);
lean_dec(x_729);
x_748 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_748, 0, x_746);
lean_ctor_set(x_748, 1, x_747);
return x_748;
}
}
}
else
{
uint8_t x_749; 
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
x_749 = !lean_is_exclusive(x_717);
if (x_749 == 0)
{
return x_717;
}
else
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; 
x_750 = lean_ctor_get(x_717, 0);
x_751 = lean_ctor_get(x_717, 1);
lean_inc(x_751);
lean_inc(x_750);
lean_dec(x_717);
x_752 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_752, 0, x_750);
lean_ctor_set(x_752, 1, x_751);
return x_752;
}
}
}
}
case 3:
{
lean_object* x_766; lean_object* x_964; lean_object* x_1002; uint8_t x_1003; 
lean_dec(x_11);
x_1002 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_1003 = l_Lean_Expr_isConstOf(x_9, x_1002);
if (x_1003 == 0)
{
lean_object* x_1004; 
x_1004 = lean_box(0);
x_964 = x_1004;
goto block_1001;
}
else
{
lean_object* x_1005; lean_object* x_1006; uint8_t x_1007; 
x_1005 = lean_array_get_size(x_10);
x_1006 = lean_unsigned_to_nat(2u);
x_1007 = lean_nat_dec_eq(x_1005, x_1006);
if (x_1007 == 0)
{
lean_object* x_1008; 
lean_dec(x_1005);
x_1008 = lean_box(0);
x_964 = x_1008;
goto block_1001;
}
else
{
lean_object* x_1009; uint8_t x_1010; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1009 = lean_unsigned_to_nat(0u);
x_1010 = lean_nat_dec_lt(x_1009, x_1005);
lean_dec(x_1005);
if (x_1010 == 0)
{
lean_object* x_1011; lean_object* x_1012; 
x_1011 = l_Lean_instInhabitedExpr;
x_1012 = l_outOfBounds___rarg(x_1011);
x_766 = x_1012;
goto block_963;
}
else
{
lean_object* x_1013; 
x_1013 = lean_array_fget(x_10, x_1009);
x_766 = x_1013;
goto block_963;
}
}
}
block_963:
{
lean_object* x_767; 
lean_inc(x_13);
lean_inc(x_766);
x_767 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_766, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_767) == 0)
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; uint8_t x_771; 
x_768 = lean_ctor_get(x_767, 0);
lean_inc(x_768);
x_769 = lean_ctor_get(x_767, 1);
lean_inc(x_769);
lean_dec(x_767);
x_770 = lean_st_ref_get(x_13, x_769);
x_771 = !lean_is_exclusive(x_770);
if (x_771 == 0)
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; 
x_772 = lean_ctor_get(x_770, 0);
x_773 = lean_ctor_get(x_770, 1);
x_774 = lean_ctor_get(x_772, 1);
lean_inc(x_774);
lean_dec(x_772);
x_775 = lean_ctor_get(x_774, 2);
lean_inc(x_775);
lean_dec(x_774);
x_776 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_775, x_768);
if (lean_obj_tag(x_776) == 0)
{
size_t x_777; size_t x_778; uint8_t x_779; 
lean_free_object(x_770);
x_777 = lean_ptr_addr(x_766);
lean_dec(x_766);
x_778 = lean_ptr_addr(x_768);
x_779 = lean_usize_dec_eq(x_777, x_778);
if (x_779 == 0)
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; uint8_t x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; uint8_t x_820; 
lean_dec(x_1);
x_780 = lean_unsigned_to_nat(0u);
lean_inc(x_768);
x_781 = lean_array_set(x_10, x_780, x_768);
x_782 = l_Lean_mkAppN(x_9, x_781);
lean_dec(x_781);
x_783 = lean_st_ref_take(x_13, x_773);
x_784 = lean_ctor_get(x_783, 0);
lean_inc(x_784);
x_785 = lean_ctor_get(x_783, 1);
lean_inc(x_785);
lean_dec(x_783);
x_786 = lean_ctor_get(x_784, 0);
lean_inc(x_786);
x_787 = lean_ctor_get(x_784, 1);
lean_inc(x_787);
x_788 = lean_ctor_get(x_787, 0);
lean_inc(x_788);
x_789 = lean_ctor_get(x_787, 1);
lean_inc(x_789);
x_790 = lean_ctor_get(x_787, 2);
lean_inc(x_790);
lean_dec(x_787);
lean_inc(x_782);
x_791 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_790, x_768, x_782);
x_792 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_792, 0, x_788);
lean_ctor_set(x_792, 1, x_789);
lean_ctor_set(x_792, 2, x_791);
x_793 = lean_ctor_get(x_784, 2);
lean_inc(x_793);
x_794 = lean_ctor_get(x_784, 3);
lean_inc(x_794);
x_795 = lean_ctor_get(x_784, 4);
lean_inc(x_795);
x_796 = lean_ctor_get(x_784, 5);
lean_inc(x_796);
x_797 = lean_ctor_get(x_784, 6);
lean_inc(x_797);
x_798 = lean_ctor_get_uint8(x_784, sizeof(void*)*26);
x_799 = lean_ctor_get(x_784, 7);
lean_inc(x_799);
x_800 = lean_ctor_get(x_784, 8);
lean_inc(x_800);
x_801 = lean_ctor_get(x_784, 9);
lean_inc(x_801);
x_802 = lean_ctor_get(x_784, 10);
lean_inc(x_802);
x_803 = lean_ctor_get(x_784, 11);
lean_inc(x_803);
x_804 = lean_ctor_get(x_784, 12);
lean_inc(x_804);
x_805 = lean_ctor_get(x_784, 13);
lean_inc(x_805);
x_806 = lean_ctor_get(x_784, 14);
lean_inc(x_806);
x_807 = lean_ctor_get(x_784, 15);
lean_inc(x_807);
x_808 = lean_ctor_get(x_784, 16);
lean_inc(x_808);
x_809 = lean_ctor_get(x_784, 17);
lean_inc(x_809);
x_810 = lean_ctor_get(x_784, 18);
lean_inc(x_810);
x_811 = lean_ctor_get(x_784, 19);
lean_inc(x_811);
x_812 = lean_ctor_get(x_784, 20);
lean_inc(x_812);
x_813 = lean_ctor_get(x_784, 21);
lean_inc(x_813);
x_814 = lean_ctor_get(x_784, 22);
lean_inc(x_814);
x_815 = lean_ctor_get(x_784, 23);
lean_inc(x_815);
x_816 = lean_ctor_get(x_784, 24);
lean_inc(x_816);
x_817 = lean_ctor_get(x_784, 25);
lean_inc(x_817);
lean_dec(x_784);
x_818 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_818, 0, x_786);
lean_ctor_set(x_818, 1, x_792);
lean_ctor_set(x_818, 2, x_793);
lean_ctor_set(x_818, 3, x_794);
lean_ctor_set(x_818, 4, x_795);
lean_ctor_set(x_818, 5, x_796);
lean_ctor_set(x_818, 6, x_797);
lean_ctor_set(x_818, 7, x_799);
lean_ctor_set(x_818, 8, x_800);
lean_ctor_set(x_818, 9, x_801);
lean_ctor_set(x_818, 10, x_802);
lean_ctor_set(x_818, 11, x_803);
lean_ctor_set(x_818, 12, x_804);
lean_ctor_set(x_818, 13, x_805);
lean_ctor_set(x_818, 14, x_806);
lean_ctor_set(x_818, 15, x_807);
lean_ctor_set(x_818, 16, x_808);
lean_ctor_set(x_818, 17, x_809);
lean_ctor_set(x_818, 18, x_810);
lean_ctor_set(x_818, 19, x_811);
lean_ctor_set(x_818, 20, x_812);
lean_ctor_set(x_818, 21, x_813);
lean_ctor_set(x_818, 22, x_814);
lean_ctor_set(x_818, 23, x_815);
lean_ctor_set(x_818, 24, x_816);
lean_ctor_set(x_818, 25, x_817);
lean_ctor_set_uint8(x_818, sizeof(void*)*26, x_798);
x_819 = lean_st_ref_set(x_13, x_818, x_785);
lean_dec(x_13);
x_820 = !lean_is_exclusive(x_819);
if (x_820 == 0)
{
lean_object* x_821; 
x_821 = lean_ctor_get(x_819, 0);
lean_dec(x_821);
lean_ctor_set(x_819, 0, x_782);
return x_819;
}
else
{
lean_object* x_822; lean_object* x_823; 
x_822 = lean_ctor_get(x_819, 1);
lean_inc(x_822);
lean_dec(x_819);
x_823 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_823, 0, x_782);
lean_ctor_set(x_823, 1, x_822);
return x_823;
}
}
else
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; uint8_t x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; uint8_t x_861; 
lean_dec(x_10);
lean_dec(x_9);
x_824 = lean_st_ref_take(x_13, x_773);
x_825 = lean_ctor_get(x_824, 0);
lean_inc(x_825);
x_826 = lean_ctor_get(x_824, 1);
lean_inc(x_826);
lean_dec(x_824);
x_827 = lean_ctor_get(x_825, 0);
lean_inc(x_827);
x_828 = lean_ctor_get(x_825, 1);
lean_inc(x_828);
x_829 = lean_ctor_get(x_828, 0);
lean_inc(x_829);
x_830 = lean_ctor_get(x_828, 1);
lean_inc(x_830);
x_831 = lean_ctor_get(x_828, 2);
lean_inc(x_831);
lean_dec(x_828);
lean_inc(x_1);
x_832 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_831, x_768, x_1);
x_833 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_833, 0, x_829);
lean_ctor_set(x_833, 1, x_830);
lean_ctor_set(x_833, 2, x_832);
x_834 = lean_ctor_get(x_825, 2);
lean_inc(x_834);
x_835 = lean_ctor_get(x_825, 3);
lean_inc(x_835);
x_836 = lean_ctor_get(x_825, 4);
lean_inc(x_836);
x_837 = lean_ctor_get(x_825, 5);
lean_inc(x_837);
x_838 = lean_ctor_get(x_825, 6);
lean_inc(x_838);
x_839 = lean_ctor_get_uint8(x_825, sizeof(void*)*26);
x_840 = lean_ctor_get(x_825, 7);
lean_inc(x_840);
x_841 = lean_ctor_get(x_825, 8);
lean_inc(x_841);
x_842 = lean_ctor_get(x_825, 9);
lean_inc(x_842);
x_843 = lean_ctor_get(x_825, 10);
lean_inc(x_843);
x_844 = lean_ctor_get(x_825, 11);
lean_inc(x_844);
x_845 = lean_ctor_get(x_825, 12);
lean_inc(x_845);
x_846 = lean_ctor_get(x_825, 13);
lean_inc(x_846);
x_847 = lean_ctor_get(x_825, 14);
lean_inc(x_847);
x_848 = lean_ctor_get(x_825, 15);
lean_inc(x_848);
x_849 = lean_ctor_get(x_825, 16);
lean_inc(x_849);
x_850 = lean_ctor_get(x_825, 17);
lean_inc(x_850);
x_851 = lean_ctor_get(x_825, 18);
lean_inc(x_851);
x_852 = lean_ctor_get(x_825, 19);
lean_inc(x_852);
x_853 = lean_ctor_get(x_825, 20);
lean_inc(x_853);
x_854 = lean_ctor_get(x_825, 21);
lean_inc(x_854);
x_855 = lean_ctor_get(x_825, 22);
lean_inc(x_855);
x_856 = lean_ctor_get(x_825, 23);
lean_inc(x_856);
x_857 = lean_ctor_get(x_825, 24);
lean_inc(x_857);
x_858 = lean_ctor_get(x_825, 25);
lean_inc(x_858);
lean_dec(x_825);
x_859 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_859, 0, x_827);
lean_ctor_set(x_859, 1, x_833);
lean_ctor_set(x_859, 2, x_834);
lean_ctor_set(x_859, 3, x_835);
lean_ctor_set(x_859, 4, x_836);
lean_ctor_set(x_859, 5, x_837);
lean_ctor_set(x_859, 6, x_838);
lean_ctor_set(x_859, 7, x_840);
lean_ctor_set(x_859, 8, x_841);
lean_ctor_set(x_859, 9, x_842);
lean_ctor_set(x_859, 10, x_843);
lean_ctor_set(x_859, 11, x_844);
lean_ctor_set(x_859, 12, x_845);
lean_ctor_set(x_859, 13, x_846);
lean_ctor_set(x_859, 14, x_847);
lean_ctor_set(x_859, 15, x_848);
lean_ctor_set(x_859, 16, x_849);
lean_ctor_set(x_859, 17, x_850);
lean_ctor_set(x_859, 18, x_851);
lean_ctor_set(x_859, 19, x_852);
lean_ctor_set(x_859, 20, x_853);
lean_ctor_set(x_859, 21, x_854);
lean_ctor_set(x_859, 22, x_855);
lean_ctor_set(x_859, 23, x_856);
lean_ctor_set(x_859, 24, x_857);
lean_ctor_set(x_859, 25, x_858);
lean_ctor_set_uint8(x_859, sizeof(void*)*26, x_839);
x_860 = lean_st_ref_set(x_13, x_859, x_826);
lean_dec(x_13);
x_861 = !lean_is_exclusive(x_860);
if (x_861 == 0)
{
lean_object* x_862; 
x_862 = lean_ctor_get(x_860, 0);
lean_dec(x_862);
lean_ctor_set(x_860, 0, x_1);
return x_860;
}
else
{
lean_object* x_863; lean_object* x_864; 
x_863 = lean_ctor_get(x_860, 1);
lean_inc(x_863);
lean_dec(x_860);
x_864 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_864, 0, x_1);
lean_ctor_set(x_864, 1, x_863);
return x_864;
}
}
}
else
{
lean_object* x_865; 
lean_dec(x_768);
lean_dec(x_766);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_865 = lean_ctor_get(x_776, 0);
lean_inc(x_865);
lean_dec(x_776);
lean_ctor_set(x_770, 0, x_865);
return x_770;
}
}
else
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; 
x_866 = lean_ctor_get(x_770, 0);
x_867 = lean_ctor_get(x_770, 1);
lean_inc(x_867);
lean_inc(x_866);
lean_dec(x_770);
x_868 = lean_ctor_get(x_866, 1);
lean_inc(x_868);
lean_dec(x_866);
x_869 = lean_ctor_get(x_868, 2);
lean_inc(x_869);
lean_dec(x_868);
x_870 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_869, x_768);
if (lean_obj_tag(x_870) == 0)
{
size_t x_871; size_t x_872; uint8_t x_873; 
x_871 = lean_ptr_addr(x_766);
lean_dec(x_766);
x_872 = lean_ptr_addr(x_768);
x_873 = lean_usize_dec_eq(x_871, x_872);
if (x_873 == 0)
{
lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; uint8_t x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; 
lean_dec(x_1);
x_874 = lean_unsigned_to_nat(0u);
lean_inc(x_768);
x_875 = lean_array_set(x_10, x_874, x_768);
x_876 = l_Lean_mkAppN(x_9, x_875);
lean_dec(x_875);
x_877 = lean_st_ref_take(x_13, x_867);
x_878 = lean_ctor_get(x_877, 0);
lean_inc(x_878);
x_879 = lean_ctor_get(x_877, 1);
lean_inc(x_879);
lean_dec(x_877);
x_880 = lean_ctor_get(x_878, 0);
lean_inc(x_880);
x_881 = lean_ctor_get(x_878, 1);
lean_inc(x_881);
x_882 = lean_ctor_get(x_881, 0);
lean_inc(x_882);
x_883 = lean_ctor_get(x_881, 1);
lean_inc(x_883);
x_884 = lean_ctor_get(x_881, 2);
lean_inc(x_884);
lean_dec(x_881);
lean_inc(x_876);
x_885 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_884, x_768, x_876);
x_886 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_886, 0, x_882);
lean_ctor_set(x_886, 1, x_883);
lean_ctor_set(x_886, 2, x_885);
x_887 = lean_ctor_get(x_878, 2);
lean_inc(x_887);
x_888 = lean_ctor_get(x_878, 3);
lean_inc(x_888);
x_889 = lean_ctor_get(x_878, 4);
lean_inc(x_889);
x_890 = lean_ctor_get(x_878, 5);
lean_inc(x_890);
x_891 = lean_ctor_get(x_878, 6);
lean_inc(x_891);
x_892 = lean_ctor_get_uint8(x_878, sizeof(void*)*26);
x_893 = lean_ctor_get(x_878, 7);
lean_inc(x_893);
x_894 = lean_ctor_get(x_878, 8);
lean_inc(x_894);
x_895 = lean_ctor_get(x_878, 9);
lean_inc(x_895);
x_896 = lean_ctor_get(x_878, 10);
lean_inc(x_896);
x_897 = lean_ctor_get(x_878, 11);
lean_inc(x_897);
x_898 = lean_ctor_get(x_878, 12);
lean_inc(x_898);
x_899 = lean_ctor_get(x_878, 13);
lean_inc(x_899);
x_900 = lean_ctor_get(x_878, 14);
lean_inc(x_900);
x_901 = lean_ctor_get(x_878, 15);
lean_inc(x_901);
x_902 = lean_ctor_get(x_878, 16);
lean_inc(x_902);
x_903 = lean_ctor_get(x_878, 17);
lean_inc(x_903);
x_904 = lean_ctor_get(x_878, 18);
lean_inc(x_904);
x_905 = lean_ctor_get(x_878, 19);
lean_inc(x_905);
x_906 = lean_ctor_get(x_878, 20);
lean_inc(x_906);
x_907 = lean_ctor_get(x_878, 21);
lean_inc(x_907);
x_908 = lean_ctor_get(x_878, 22);
lean_inc(x_908);
x_909 = lean_ctor_get(x_878, 23);
lean_inc(x_909);
x_910 = lean_ctor_get(x_878, 24);
lean_inc(x_910);
x_911 = lean_ctor_get(x_878, 25);
lean_inc(x_911);
lean_dec(x_878);
x_912 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_912, 0, x_880);
lean_ctor_set(x_912, 1, x_886);
lean_ctor_set(x_912, 2, x_887);
lean_ctor_set(x_912, 3, x_888);
lean_ctor_set(x_912, 4, x_889);
lean_ctor_set(x_912, 5, x_890);
lean_ctor_set(x_912, 6, x_891);
lean_ctor_set(x_912, 7, x_893);
lean_ctor_set(x_912, 8, x_894);
lean_ctor_set(x_912, 9, x_895);
lean_ctor_set(x_912, 10, x_896);
lean_ctor_set(x_912, 11, x_897);
lean_ctor_set(x_912, 12, x_898);
lean_ctor_set(x_912, 13, x_899);
lean_ctor_set(x_912, 14, x_900);
lean_ctor_set(x_912, 15, x_901);
lean_ctor_set(x_912, 16, x_902);
lean_ctor_set(x_912, 17, x_903);
lean_ctor_set(x_912, 18, x_904);
lean_ctor_set(x_912, 19, x_905);
lean_ctor_set(x_912, 20, x_906);
lean_ctor_set(x_912, 21, x_907);
lean_ctor_set(x_912, 22, x_908);
lean_ctor_set(x_912, 23, x_909);
lean_ctor_set(x_912, 24, x_910);
lean_ctor_set(x_912, 25, x_911);
lean_ctor_set_uint8(x_912, sizeof(void*)*26, x_892);
x_913 = lean_st_ref_set(x_13, x_912, x_879);
lean_dec(x_13);
x_914 = lean_ctor_get(x_913, 1);
lean_inc(x_914);
if (lean_is_exclusive(x_913)) {
 lean_ctor_release(x_913, 0);
 lean_ctor_release(x_913, 1);
 x_915 = x_913;
} else {
 lean_dec_ref(x_913);
 x_915 = lean_box(0);
}
if (lean_is_scalar(x_915)) {
 x_916 = lean_alloc_ctor(0, 2, 0);
} else {
 x_916 = x_915;
}
lean_ctor_set(x_916, 0, x_876);
lean_ctor_set(x_916, 1, x_914);
return x_916;
}
else
{
lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; uint8_t x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; 
lean_dec(x_10);
lean_dec(x_9);
x_917 = lean_st_ref_take(x_13, x_867);
x_918 = lean_ctor_get(x_917, 0);
lean_inc(x_918);
x_919 = lean_ctor_get(x_917, 1);
lean_inc(x_919);
lean_dec(x_917);
x_920 = lean_ctor_get(x_918, 0);
lean_inc(x_920);
x_921 = lean_ctor_get(x_918, 1);
lean_inc(x_921);
x_922 = lean_ctor_get(x_921, 0);
lean_inc(x_922);
x_923 = lean_ctor_get(x_921, 1);
lean_inc(x_923);
x_924 = lean_ctor_get(x_921, 2);
lean_inc(x_924);
lean_dec(x_921);
lean_inc(x_1);
x_925 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_924, x_768, x_1);
x_926 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_926, 0, x_922);
lean_ctor_set(x_926, 1, x_923);
lean_ctor_set(x_926, 2, x_925);
x_927 = lean_ctor_get(x_918, 2);
lean_inc(x_927);
x_928 = lean_ctor_get(x_918, 3);
lean_inc(x_928);
x_929 = lean_ctor_get(x_918, 4);
lean_inc(x_929);
x_930 = lean_ctor_get(x_918, 5);
lean_inc(x_930);
x_931 = lean_ctor_get(x_918, 6);
lean_inc(x_931);
x_932 = lean_ctor_get_uint8(x_918, sizeof(void*)*26);
x_933 = lean_ctor_get(x_918, 7);
lean_inc(x_933);
x_934 = lean_ctor_get(x_918, 8);
lean_inc(x_934);
x_935 = lean_ctor_get(x_918, 9);
lean_inc(x_935);
x_936 = lean_ctor_get(x_918, 10);
lean_inc(x_936);
x_937 = lean_ctor_get(x_918, 11);
lean_inc(x_937);
x_938 = lean_ctor_get(x_918, 12);
lean_inc(x_938);
x_939 = lean_ctor_get(x_918, 13);
lean_inc(x_939);
x_940 = lean_ctor_get(x_918, 14);
lean_inc(x_940);
x_941 = lean_ctor_get(x_918, 15);
lean_inc(x_941);
x_942 = lean_ctor_get(x_918, 16);
lean_inc(x_942);
x_943 = lean_ctor_get(x_918, 17);
lean_inc(x_943);
x_944 = lean_ctor_get(x_918, 18);
lean_inc(x_944);
x_945 = lean_ctor_get(x_918, 19);
lean_inc(x_945);
x_946 = lean_ctor_get(x_918, 20);
lean_inc(x_946);
x_947 = lean_ctor_get(x_918, 21);
lean_inc(x_947);
x_948 = lean_ctor_get(x_918, 22);
lean_inc(x_948);
x_949 = lean_ctor_get(x_918, 23);
lean_inc(x_949);
x_950 = lean_ctor_get(x_918, 24);
lean_inc(x_950);
x_951 = lean_ctor_get(x_918, 25);
lean_inc(x_951);
lean_dec(x_918);
x_952 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_952, 0, x_920);
lean_ctor_set(x_952, 1, x_926);
lean_ctor_set(x_952, 2, x_927);
lean_ctor_set(x_952, 3, x_928);
lean_ctor_set(x_952, 4, x_929);
lean_ctor_set(x_952, 5, x_930);
lean_ctor_set(x_952, 6, x_931);
lean_ctor_set(x_952, 7, x_933);
lean_ctor_set(x_952, 8, x_934);
lean_ctor_set(x_952, 9, x_935);
lean_ctor_set(x_952, 10, x_936);
lean_ctor_set(x_952, 11, x_937);
lean_ctor_set(x_952, 12, x_938);
lean_ctor_set(x_952, 13, x_939);
lean_ctor_set(x_952, 14, x_940);
lean_ctor_set(x_952, 15, x_941);
lean_ctor_set(x_952, 16, x_942);
lean_ctor_set(x_952, 17, x_943);
lean_ctor_set(x_952, 18, x_944);
lean_ctor_set(x_952, 19, x_945);
lean_ctor_set(x_952, 20, x_946);
lean_ctor_set(x_952, 21, x_947);
lean_ctor_set(x_952, 22, x_948);
lean_ctor_set(x_952, 23, x_949);
lean_ctor_set(x_952, 24, x_950);
lean_ctor_set(x_952, 25, x_951);
lean_ctor_set_uint8(x_952, sizeof(void*)*26, x_932);
x_953 = lean_st_ref_set(x_13, x_952, x_919);
lean_dec(x_13);
x_954 = lean_ctor_get(x_953, 1);
lean_inc(x_954);
if (lean_is_exclusive(x_953)) {
 lean_ctor_release(x_953, 0);
 lean_ctor_release(x_953, 1);
 x_955 = x_953;
} else {
 lean_dec_ref(x_953);
 x_955 = lean_box(0);
}
if (lean_is_scalar(x_955)) {
 x_956 = lean_alloc_ctor(0, 2, 0);
} else {
 x_956 = x_955;
}
lean_ctor_set(x_956, 0, x_1);
lean_ctor_set(x_956, 1, x_954);
return x_956;
}
}
else
{
lean_object* x_957; lean_object* x_958; 
lean_dec(x_768);
lean_dec(x_766);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_957 = lean_ctor_get(x_870, 0);
lean_inc(x_957);
lean_dec(x_870);
x_958 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_958, 0, x_957);
lean_ctor_set(x_958, 1, x_867);
return x_958;
}
}
}
else
{
uint8_t x_959; 
lean_dec(x_766);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_959 = !lean_is_exclusive(x_767);
if (x_959 == 0)
{
return x_767;
}
else
{
lean_object* x_960; lean_object* x_961; lean_object* x_962; 
x_960 = lean_ctor_get(x_767, 0);
x_961 = lean_ctor_get(x_767, 1);
lean_inc(x_961);
lean_inc(x_960);
lean_dec(x_767);
x_962 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_962, 0, x_960);
lean_ctor_set(x_962, 1, x_961);
return x_962;
}
}
}
block_1001:
{
lean_object* x_965; 
lean_dec(x_964);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_9);
x_965 = l_Lean_Meta_getFunInfo(x_9, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_965) == 0)
{
lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; uint8_t x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; 
x_966 = lean_ctor_get(x_965, 0);
lean_inc(x_966);
x_967 = lean_ctor_get(x_965, 1);
lean_inc(x_967);
lean_dec(x_965);
x_968 = lean_ctor_get(x_966, 0);
lean_inc(x_968);
lean_dec(x_966);
x_969 = lean_array_get_size(x_10);
x_970 = lean_unsigned_to_nat(0u);
x_971 = lean_unsigned_to_nat(1u);
lean_inc(x_969);
x_972 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_972, 0, x_970);
lean_ctor_set(x_972, 1, x_969);
lean_ctor_set(x_972, 2, x_971);
x_973 = 0;
x_974 = lean_box(x_973);
lean_inc(x_10);
x_975 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_975, 0, x_10);
lean_ctor_set(x_975, 1, x_974);
x_976 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_972);
lean_inc(x_9);
lean_inc(x_1);
x_977 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_976, x_968, x_969, x_972, x_972, x_975, x_970, lean_box(0), lean_box(0), x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_967);
if (lean_obj_tag(x_977) == 0)
{
lean_object* x_978; lean_object* x_979; uint8_t x_980; 
x_978 = lean_ctor_get(x_977, 0);
lean_inc(x_978);
x_979 = lean_ctor_get(x_978, 1);
lean_inc(x_979);
x_980 = lean_unbox(x_979);
lean_dec(x_979);
if (x_980 == 0)
{
uint8_t x_981; 
lean_dec(x_978);
lean_dec(x_9);
x_981 = !lean_is_exclusive(x_977);
if (x_981 == 0)
{
lean_object* x_982; 
x_982 = lean_ctor_get(x_977, 0);
lean_dec(x_982);
lean_ctor_set(x_977, 0, x_1);
return x_977;
}
else
{
lean_object* x_983; lean_object* x_984; 
x_983 = lean_ctor_get(x_977, 1);
lean_inc(x_983);
lean_dec(x_977);
x_984 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_984, 0, x_1);
lean_ctor_set(x_984, 1, x_983);
return x_984;
}
}
else
{
uint8_t x_985; 
lean_dec(x_1);
x_985 = !lean_is_exclusive(x_977);
if (x_985 == 0)
{
lean_object* x_986; lean_object* x_987; lean_object* x_988; 
x_986 = lean_ctor_get(x_977, 0);
lean_dec(x_986);
x_987 = lean_ctor_get(x_978, 0);
lean_inc(x_987);
lean_dec(x_978);
x_988 = l_Lean_mkAppN(x_9, x_987);
lean_dec(x_987);
lean_ctor_set(x_977, 0, x_988);
return x_977;
}
else
{
lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; 
x_989 = lean_ctor_get(x_977, 1);
lean_inc(x_989);
lean_dec(x_977);
x_990 = lean_ctor_get(x_978, 0);
lean_inc(x_990);
lean_dec(x_978);
x_991 = l_Lean_mkAppN(x_9, x_990);
lean_dec(x_990);
x_992 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_992, 0, x_991);
lean_ctor_set(x_992, 1, x_989);
return x_992;
}
}
}
else
{
uint8_t x_993; 
lean_dec(x_9);
lean_dec(x_1);
x_993 = !lean_is_exclusive(x_977);
if (x_993 == 0)
{
return x_977;
}
else
{
lean_object* x_994; lean_object* x_995; lean_object* x_996; 
x_994 = lean_ctor_get(x_977, 0);
x_995 = lean_ctor_get(x_977, 1);
lean_inc(x_995);
lean_inc(x_994);
lean_dec(x_977);
x_996 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_996, 0, x_994);
lean_ctor_set(x_996, 1, x_995);
return x_996;
}
}
}
else
{
uint8_t x_997; 
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
x_997 = !lean_is_exclusive(x_965);
if (x_997 == 0)
{
return x_965;
}
else
{
lean_object* x_998; lean_object* x_999; lean_object* x_1000; 
x_998 = lean_ctor_get(x_965, 0);
x_999 = lean_ctor_get(x_965, 1);
lean_inc(x_999);
lean_inc(x_998);
lean_dec(x_965);
x_1000 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1000, 0, x_998);
lean_ctor_set(x_1000, 1, x_999);
return x_1000;
}
}
}
}
case 4:
{
lean_object* x_1014; lean_object* x_1212; lean_object* x_1250; uint8_t x_1251; 
lean_dec(x_11);
x_1250 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_1251 = l_Lean_Expr_isConstOf(x_9, x_1250);
if (x_1251 == 0)
{
lean_object* x_1252; 
x_1252 = lean_box(0);
x_1212 = x_1252;
goto block_1249;
}
else
{
lean_object* x_1253; lean_object* x_1254; uint8_t x_1255; 
x_1253 = lean_array_get_size(x_10);
x_1254 = lean_unsigned_to_nat(2u);
x_1255 = lean_nat_dec_eq(x_1253, x_1254);
if (x_1255 == 0)
{
lean_object* x_1256; 
lean_dec(x_1253);
x_1256 = lean_box(0);
x_1212 = x_1256;
goto block_1249;
}
else
{
lean_object* x_1257; uint8_t x_1258; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1257 = lean_unsigned_to_nat(0u);
x_1258 = lean_nat_dec_lt(x_1257, x_1253);
lean_dec(x_1253);
if (x_1258 == 0)
{
lean_object* x_1259; lean_object* x_1260; 
x_1259 = l_Lean_instInhabitedExpr;
x_1260 = l_outOfBounds___rarg(x_1259);
x_1014 = x_1260;
goto block_1211;
}
else
{
lean_object* x_1261; 
x_1261 = lean_array_fget(x_10, x_1257);
x_1014 = x_1261;
goto block_1211;
}
}
}
block_1211:
{
lean_object* x_1015; 
lean_inc(x_13);
lean_inc(x_1014);
x_1015 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_1014, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_1015) == 0)
{
lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; uint8_t x_1019; 
x_1016 = lean_ctor_get(x_1015, 0);
lean_inc(x_1016);
x_1017 = lean_ctor_get(x_1015, 1);
lean_inc(x_1017);
lean_dec(x_1015);
x_1018 = lean_st_ref_get(x_13, x_1017);
x_1019 = !lean_is_exclusive(x_1018);
if (x_1019 == 0)
{
lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; 
x_1020 = lean_ctor_get(x_1018, 0);
x_1021 = lean_ctor_get(x_1018, 1);
x_1022 = lean_ctor_get(x_1020, 1);
lean_inc(x_1022);
lean_dec(x_1020);
x_1023 = lean_ctor_get(x_1022, 2);
lean_inc(x_1023);
lean_dec(x_1022);
x_1024 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_1023, x_1016);
if (lean_obj_tag(x_1024) == 0)
{
size_t x_1025; size_t x_1026; uint8_t x_1027; 
lean_free_object(x_1018);
x_1025 = lean_ptr_addr(x_1014);
lean_dec(x_1014);
x_1026 = lean_ptr_addr(x_1016);
x_1027 = lean_usize_dec_eq(x_1025, x_1026);
if (x_1027 == 0)
{
lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; uint8_t x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; uint8_t x_1068; 
lean_dec(x_1);
x_1028 = lean_unsigned_to_nat(0u);
lean_inc(x_1016);
x_1029 = lean_array_set(x_10, x_1028, x_1016);
x_1030 = l_Lean_mkAppN(x_9, x_1029);
lean_dec(x_1029);
x_1031 = lean_st_ref_take(x_13, x_1021);
x_1032 = lean_ctor_get(x_1031, 0);
lean_inc(x_1032);
x_1033 = lean_ctor_get(x_1031, 1);
lean_inc(x_1033);
lean_dec(x_1031);
x_1034 = lean_ctor_get(x_1032, 0);
lean_inc(x_1034);
x_1035 = lean_ctor_get(x_1032, 1);
lean_inc(x_1035);
x_1036 = lean_ctor_get(x_1035, 0);
lean_inc(x_1036);
x_1037 = lean_ctor_get(x_1035, 1);
lean_inc(x_1037);
x_1038 = lean_ctor_get(x_1035, 2);
lean_inc(x_1038);
lean_dec(x_1035);
lean_inc(x_1030);
x_1039 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1038, x_1016, x_1030);
x_1040 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1040, 0, x_1036);
lean_ctor_set(x_1040, 1, x_1037);
lean_ctor_set(x_1040, 2, x_1039);
x_1041 = lean_ctor_get(x_1032, 2);
lean_inc(x_1041);
x_1042 = lean_ctor_get(x_1032, 3);
lean_inc(x_1042);
x_1043 = lean_ctor_get(x_1032, 4);
lean_inc(x_1043);
x_1044 = lean_ctor_get(x_1032, 5);
lean_inc(x_1044);
x_1045 = lean_ctor_get(x_1032, 6);
lean_inc(x_1045);
x_1046 = lean_ctor_get_uint8(x_1032, sizeof(void*)*26);
x_1047 = lean_ctor_get(x_1032, 7);
lean_inc(x_1047);
x_1048 = lean_ctor_get(x_1032, 8);
lean_inc(x_1048);
x_1049 = lean_ctor_get(x_1032, 9);
lean_inc(x_1049);
x_1050 = lean_ctor_get(x_1032, 10);
lean_inc(x_1050);
x_1051 = lean_ctor_get(x_1032, 11);
lean_inc(x_1051);
x_1052 = lean_ctor_get(x_1032, 12);
lean_inc(x_1052);
x_1053 = lean_ctor_get(x_1032, 13);
lean_inc(x_1053);
x_1054 = lean_ctor_get(x_1032, 14);
lean_inc(x_1054);
x_1055 = lean_ctor_get(x_1032, 15);
lean_inc(x_1055);
x_1056 = lean_ctor_get(x_1032, 16);
lean_inc(x_1056);
x_1057 = lean_ctor_get(x_1032, 17);
lean_inc(x_1057);
x_1058 = lean_ctor_get(x_1032, 18);
lean_inc(x_1058);
x_1059 = lean_ctor_get(x_1032, 19);
lean_inc(x_1059);
x_1060 = lean_ctor_get(x_1032, 20);
lean_inc(x_1060);
x_1061 = lean_ctor_get(x_1032, 21);
lean_inc(x_1061);
x_1062 = lean_ctor_get(x_1032, 22);
lean_inc(x_1062);
x_1063 = lean_ctor_get(x_1032, 23);
lean_inc(x_1063);
x_1064 = lean_ctor_get(x_1032, 24);
lean_inc(x_1064);
x_1065 = lean_ctor_get(x_1032, 25);
lean_inc(x_1065);
lean_dec(x_1032);
x_1066 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_1066, 0, x_1034);
lean_ctor_set(x_1066, 1, x_1040);
lean_ctor_set(x_1066, 2, x_1041);
lean_ctor_set(x_1066, 3, x_1042);
lean_ctor_set(x_1066, 4, x_1043);
lean_ctor_set(x_1066, 5, x_1044);
lean_ctor_set(x_1066, 6, x_1045);
lean_ctor_set(x_1066, 7, x_1047);
lean_ctor_set(x_1066, 8, x_1048);
lean_ctor_set(x_1066, 9, x_1049);
lean_ctor_set(x_1066, 10, x_1050);
lean_ctor_set(x_1066, 11, x_1051);
lean_ctor_set(x_1066, 12, x_1052);
lean_ctor_set(x_1066, 13, x_1053);
lean_ctor_set(x_1066, 14, x_1054);
lean_ctor_set(x_1066, 15, x_1055);
lean_ctor_set(x_1066, 16, x_1056);
lean_ctor_set(x_1066, 17, x_1057);
lean_ctor_set(x_1066, 18, x_1058);
lean_ctor_set(x_1066, 19, x_1059);
lean_ctor_set(x_1066, 20, x_1060);
lean_ctor_set(x_1066, 21, x_1061);
lean_ctor_set(x_1066, 22, x_1062);
lean_ctor_set(x_1066, 23, x_1063);
lean_ctor_set(x_1066, 24, x_1064);
lean_ctor_set(x_1066, 25, x_1065);
lean_ctor_set_uint8(x_1066, sizeof(void*)*26, x_1046);
x_1067 = lean_st_ref_set(x_13, x_1066, x_1033);
lean_dec(x_13);
x_1068 = !lean_is_exclusive(x_1067);
if (x_1068 == 0)
{
lean_object* x_1069; 
x_1069 = lean_ctor_get(x_1067, 0);
lean_dec(x_1069);
lean_ctor_set(x_1067, 0, x_1030);
return x_1067;
}
else
{
lean_object* x_1070; lean_object* x_1071; 
x_1070 = lean_ctor_get(x_1067, 1);
lean_inc(x_1070);
lean_dec(x_1067);
x_1071 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1071, 0, x_1030);
lean_ctor_set(x_1071, 1, x_1070);
return x_1071;
}
}
else
{
lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; uint8_t x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; uint8_t x_1109; 
lean_dec(x_10);
lean_dec(x_9);
x_1072 = lean_st_ref_take(x_13, x_1021);
x_1073 = lean_ctor_get(x_1072, 0);
lean_inc(x_1073);
x_1074 = lean_ctor_get(x_1072, 1);
lean_inc(x_1074);
lean_dec(x_1072);
x_1075 = lean_ctor_get(x_1073, 0);
lean_inc(x_1075);
x_1076 = lean_ctor_get(x_1073, 1);
lean_inc(x_1076);
x_1077 = lean_ctor_get(x_1076, 0);
lean_inc(x_1077);
x_1078 = lean_ctor_get(x_1076, 1);
lean_inc(x_1078);
x_1079 = lean_ctor_get(x_1076, 2);
lean_inc(x_1079);
lean_dec(x_1076);
lean_inc(x_1);
x_1080 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1079, x_1016, x_1);
x_1081 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1081, 0, x_1077);
lean_ctor_set(x_1081, 1, x_1078);
lean_ctor_set(x_1081, 2, x_1080);
x_1082 = lean_ctor_get(x_1073, 2);
lean_inc(x_1082);
x_1083 = lean_ctor_get(x_1073, 3);
lean_inc(x_1083);
x_1084 = lean_ctor_get(x_1073, 4);
lean_inc(x_1084);
x_1085 = lean_ctor_get(x_1073, 5);
lean_inc(x_1085);
x_1086 = lean_ctor_get(x_1073, 6);
lean_inc(x_1086);
x_1087 = lean_ctor_get_uint8(x_1073, sizeof(void*)*26);
x_1088 = lean_ctor_get(x_1073, 7);
lean_inc(x_1088);
x_1089 = lean_ctor_get(x_1073, 8);
lean_inc(x_1089);
x_1090 = lean_ctor_get(x_1073, 9);
lean_inc(x_1090);
x_1091 = lean_ctor_get(x_1073, 10);
lean_inc(x_1091);
x_1092 = lean_ctor_get(x_1073, 11);
lean_inc(x_1092);
x_1093 = lean_ctor_get(x_1073, 12);
lean_inc(x_1093);
x_1094 = lean_ctor_get(x_1073, 13);
lean_inc(x_1094);
x_1095 = lean_ctor_get(x_1073, 14);
lean_inc(x_1095);
x_1096 = lean_ctor_get(x_1073, 15);
lean_inc(x_1096);
x_1097 = lean_ctor_get(x_1073, 16);
lean_inc(x_1097);
x_1098 = lean_ctor_get(x_1073, 17);
lean_inc(x_1098);
x_1099 = lean_ctor_get(x_1073, 18);
lean_inc(x_1099);
x_1100 = lean_ctor_get(x_1073, 19);
lean_inc(x_1100);
x_1101 = lean_ctor_get(x_1073, 20);
lean_inc(x_1101);
x_1102 = lean_ctor_get(x_1073, 21);
lean_inc(x_1102);
x_1103 = lean_ctor_get(x_1073, 22);
lean_inc(x_1103);
x_1104 = lean_ctor_get(x_1073, 23);
lean_inc(x_1104);
x_1105 = lean_ctor_get(x_1073, 24);
lean_inc(x_1105);
x_1106 = lean_ctor_get(x_1073, 25);
lean_inc(x_1106);
lean_dec(x_1073);
x_1107 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_1107, 0, x_1075);
lean_ctor_set(x_1107, 1, x_1081);
lean_ctor_set(x_1107, 2, x_1082);
lean_ctor_set(x_1107, 3, x_1083);
lean_ctor_set(x_1107, 4, x_1084);
lean_ctor_set(x_1107, 5, x_1085);
lean_ctor_set(x_1107, 6, x_1086);
lean_ctor_set(x_1107, 7, x_1088);
lean_ctor_set(x_1107, 8, x_1089);
lean_ctor_set(x_1107, 9, x_1090);
lean_ctor_set(x_1107, 10, x_1091);
lean_ctor_set(x_1107, 11, x_1092);
lean_ctor_set(x_1107, 12, x_1093);
lean_ctor_set(x_1107, 13, x_1094);
lean_ctor_set(x_1107, 14, x_1095);
lean_ctor_set(x_1107, 15, x_1096);
lean_ctor_set(x_1107, 16, x_1097);
lean_ctor_set(x_1107, 17, x_1098);
lean_ctor_set(x_1107, 18, x_1099);
lean_ctor_set(x_1107, 19, x_1100);
lean_ctor_set(x_1107, 20, x_1101);
lean_ctor_set(x_1107, 21, x_1102);
lean_ctor_set(x_1107, 22, x_1103);
lean_ctor_set(x_1107, 23, x_1104);
lean_ctor_set(x_1107, 24, x_1105);
lean_ctor_set(x_1107, 25, x_1106);
lean_ctor_set_uint8(x_1107, sizeof(void*)*26, x_1087);
x_1108 = lean_st_ref_set(x_13, x_1107, x_1074);
lean_dec(x_13);
x_1109 = !lean_is_exclusive(x_1108);
if (x_1109 == 0)
{
lean_object* x_1110; 
x_1110 = lean_ctor_get(x_1108, 0);
lean_dec(x_1110);
lean_ctor_set(x_1108, 0, x_1);
return x_1108;
}
else
{
lean_object* x_1111; lean_object* x_1112; 
x_1111 = lean_ctor_get(x_1108, 1);
lean_inc(x_1111);
lean_dec(x_1108);
x_1112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1112, 0, x_1);
lean_ctor_set(x_1112, 1, x_1111);
return x_1112;
}
}
}
else
{
lean_object* x_1113; 
lean_dec(x_1016);
lean_dec(x_1014);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_1113 = lean_ctor_get(x_1024, 0);
lean_inc(x_1113);
lean_dec(x_1024);
lean_ctor_set(x_1018, 0, x_1113);
return x_1018;
}
}
else
{
lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; 
x_1114 = lean_ctor_get(x_1018, 0);
x_1115 = lean_ctor_get(x_1018, 1);
lean_inc(x_1115);
lean_inc(x_1114);
lean_dec(x_1018);
x_1116 = lean_ctor_get(x_1114, 1);
lean_inc(x_1116);
lean_dec(x_1114);
x_1117 = lean_ctor_get(x_1116, 2);
lean_inc(x_1117);
lean_dec(x_1116);
x_1118 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_1117, x_1016);
if (lean_obj_tag(x_1118) == 0)
{
size_t x_1119; size_t x_1120; uint8_t x_1121; 
x_1119 = lean_ptr_addr(x_1014);
lean_dec(x_1014);
x_1120 = lean_ptr_addr(x_1016);
x_1121 = lean_usize_dec_eq(x_1119, x_1120);
if (x_1121 == 0)
{
lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; uint8_t x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; 
lean_dec(x_1);
x_1122 = lean_unsigned_to_nat(0u);
lean_inc(x_1016);
x_1123 = lean_array_set(x_10, x_1122, x_1016);
x_1124 = l_Lean_mkAppN(x_9, x_1123);
lean_dec(x_1123);
x_1125 = lean_st_ref_take(x_13, x_1115);
x_1126 = lean_ctor_get(x_1125, 0);
lean_inc(x_1126);
x_1127 = lean_ctor_get(x_1125, 1);
lean_inc(x_1127);
lean_dec(x_1125);
x_1128 = lean_ctor_get(x_1126, 0);
lean_inc(x_1128);
x_1129 = lean_ctor_get(x_1126, 1);
lean_inc(x_1129);
x_1130 = lean_ctor_get(x_1129, 0);
lean_inc(x_1130);
x_1131 = lean_ctor_get(x_1129, 1);
lean_inc(x_1131);
x_1132 = lean_ctor_get(x_1129, 2);
lean_inc(x_1132);
lean_dec(x_1129);
lean_inc(x_1124);
x_1133 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1132, x_1016, x_1124);
x_1134 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1134, 0, x_1130);
lean_ctor_set(x_1134, 1, x_1131);
lean_ctor_set(x_1134, 2, x_1133);
x_1135 = lean_ctor_get(x_1126, 2);
lean_inc(x_1135);
x_1136 = lean_ctor_get(x_1126, 3);
lean_inc(x_1136);
x_1137 = lean_ctor_get(x_1126, 4);
lean_inc(x_1137);
x_1138 = lean_ctor_get(x_1126, 5);
lean_inc(x_1138);
x_1139 = lean_ctor_get(x_1126, 6);
lean_inc(x_1139);
x_1140 = lean_ctor_get_uint8(x_1126, sizeof(void*)*26);
x_1141 = lean_ctor_get(x_1126, 7);
lean_inc(x_1141);
x_1142 = lean_ctor_get(x_1126, 8);
lean_inc(x_1142);
x_1143 = lean_ctor_get(x_1126, 9);
lean_inc(x_1143);
x_1144 = lean_ctor_get(x_1126, 10);
lean_inc(x_1144);
x_1145 = lean_ctor_get(x_1126, 11);
lean_inc(x_1145);
x_1146 = lean_ctor_get(x_1126, 12);
lean_inc(x_1146);
x_1147 = lean_ctor_get(x_1126, 13);
lean_inc(x_1147);
x_1148 = lean_ctor_get(x_1126, 14);
lean_inc(x_1148);
x_1149 = lean_ctor_get(x_1126, 15);
lean_inc(x_1149);
x_1150 = lean_ctor_get(x_1126, 16);
lean_inc(x_1150);
x_1151 = lean_ctor_get(x_1126, 17);
lean_inc(x_1151);
x_1152 = lean_ctor_get(x_1126, 18);
lean_inc(x_1152);
x_1153 = lean_ctor_get(x_1126, 19);
lean_inc(x_1153);
x_1154 = lean_ctor_get(x_1126, 20);
lean_inc(x_1154);
x_1155 = lean_ctor_get(x_1126, 21);
lean_inc(x_1155);
x_1156 = lean_ctor_get(x_1126, 22);
lean_inc(x_1156);
x_1157 = lean_ctor_get(x_1126, 23);
lean_inc(x_1157);
x_1158 = lean_ctor_get(x_1126, 24);
lean_inc(x_1158);
x_1159 = lean_ctor_get(x_1126, 25);
lean_inc(x_1159);
lean_dec(x_1126);
x_1160 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_1160, 0, x_1128);
lean_ctor_set(x_1160, 1, x_1134);
lean_ctor_set(x_1160, 2, x_1135);
lean_ctor_set(x_1160, 3, x_1136);
lean_ctor_set(x_1160, 4, x_1137);
lean_ctor_set(x_1160, 5, x_1138);
lean_ctor_set(x_1160, 6, x_1139);
lean_ctor_set(x_1160, 7, x_1141);
lean_ctor_set(x_1160, 8, x_1142);
lean_ctor_set(x_1160, 9, x_1143);
lean_ctor_set(x_1160, 10, x_1144);
lean_ctor_set(x_1160, 11, x_1145);
lean_ctor_set(x_1160, 12, x_1146);
lean_ctor_set(x_1160, 13, x_1147);
lean_ctor_set(x_1160, 14, x_1148);
lean_ctor_set(x_1160, 15, x_1149);
lean_ctor_set(x_1160, 16, x_1150);
lean_ctor_set(x_1160, 17, x_1151);
lean_ctor_set(x_1160, 18, x_1152);
lean_ctor_set(x_1160, 19, x_1153);
lean_ctor_set(x_1160, 20, x_1154);
lean_ctor_set(x_1160, 21, x_1155);
lean_ctor_set(x_1160, 22, x_1156);
lean_ctor_set(x_1160, 23, x_1157);
lean_ctor_set(x_1160, 24, x_1158);
lean_ctor_set(x_1160, 25, x_1159);
lean_ctor_set_uint8(x_1160, sizeof(void*)*26, x_1140);
x_1161 = lean_st_ref_set(x_13, x_1160, x_1127);
lean_dec(x_13);
x_1162 = lean_ctor_get(x_1161, 1);
lean_inc(x_1162);
if (lean_is_exclusive(x_1161)) {
 lean_ctor_release(x_1161, 0);
 lean_ctor_release(x_1161, 1);
 x_1163 = x_1161;
} else {
 lean_dec_ref(x_1161);
 x_1163 = lean_box(0);
}
if (lean_is_scalar(x_1163)) {
 x_1164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1164 = x_1163;
}
lean_ctor_set(x_1164, 0, x_1124);
lean_ctor_set(x_1164, 1, x_1162);
return x_1164;
}
else
{
lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; uint8_t x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; 
lean_dec(x_10);
lean_dec(x_9);
x_1165 = lean_st_ref_take(x_13, x_1115);
x_1166 = lean_ctor_get(x_1165, 0);
lean_inc(x_1166);
x_1167 = lean_ctor_get(x_1165, 1);
lean_inc(x_1167);
lean_dec(x_1165);
x_1168 = lean_ctor_get(x_1166, 0);
lean_inc(x_1168);
x_1169 = lean_ctor_get(x_1166, 1);
lean_inc(x_1169);
x_1170 = lean_ctor_get(x_1169, 0);
lean_inc(x_1170);
x_1171 = lean_ctor_get(x_1169, 1);
lean_inc(x_1171);
x_1172 = lean_ctor_get(x_1169, 2);
lean_inc(x_1172);
lean_dec(x_1169);
lean_inc(x_1);
x_1173 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1172, x_1016, x_1);
x_1174 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1174, 0, x_1170);
lean_ctor_set(x_1174, 1, x_1171);
lean_ctor_set(x_1174, 2, x_1173);
x_1175 = lean_ctor_get(x_1166, 2);
lean_inc(x_1175);
x_1176 = lean_ctor_get(x_1166, 3);
lean_inc(x_1176);
x_1177 = lean_ctor_get(x_1166, 4);
lean_inc(x_1177);
x_1178 = lean_ctor_get(x_1166, 5);
lean_inc(x_1178);
x_1179 = lean_ctor_get(x_1166, 6);
lean_inc(x_1179);
x_1180 = lean_ctor_get_uint8(x_1166, sizeof(void*)*26);
x_1181 = lean_ctor_get(x_1166, 7);
lean_inc(x_1181);
x_1182 = lean_ctor_get(x_1166, 8);
lean_inc(x_1182);
x_1183 = lean_ctor_get(x_1166, 9);
lean_inc(x_1183);
x_1184 = lean_ctor_get(x_1166, 10);
lean_inc(x_1184);
x_1185 = lean_ctor_get(x_1166, 11);
lean_inc(x_1185);
x_1186 = lean_ctor_get(x_1166, 12);
lean_inc(x_1186);
x_1187 = lean_ctor_get(x_1166, 13);
lean_inc(x_1187);
x_1188 = lean_ctor_get(x_1166, 14);
lean_inc(x_1188);
x_1189 = lean_ctor_get(x_1166, 15);
lean_inc(x_1189);
x_1190 = lean_ctor_get(x_1166, 16);
lean_inc(x_1190);
x_1191 = lean_ctor_get(x_1166, 17);
lean_inc(x_1191);
x_1192 = lean_ctor_get(x_1166, 18);
lean_inc(x_1192);
x_1193 = lean_ctor_get(x_1166, 19);
lean_inc(x_1193);
x_1194 = lean_ctor_get(x_1166, 20);
lean_inc(x_1194);
x_1195 = lean_ctor_get(x_1166, 21);
lean_inc(x_1195);
x_1196 = lean_ctor_get(x_1166, 22);
lean_inc(x_1196);
x_1197 = lean_ctor_get(x_1166, 23);
lean_inc(x_1197);
x_1198 = lean_ctor_get(x_1166, 24);
lean_inc(x_1198);
x_1199 = lean_ctor_get(x_1166, 25);
lean_inc(x_1199);
lean_dec(x_1166);
x_1200 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_1200, 0, x_1168);
lean_ctor_set(x_1200, 1, x_1174);
lean_ctor_set(x_1200, 2, x_1175);
lean_ctor_set(x_1200, 3, x_1176);
lean_ctor_set(x_1200, 4, x_1177);
lean_ctor_set(x_1200, 5, x_1178);
lean_ctor_set(x_1200, 6, x_1179);
lean_ctor_set(x_1200, 7, x_1181);
lean_ctor_set(x_1200, 8, x_1182);
lean_ctor_set(x_1200, 9, x_1183);
lean_ctor_set(x_1200, 10, x_1184);
lean_ctor_set(x_1200, 11, x_1185);
lean_ctor_set(x_1200, 12, x_1186);
lean_ctor_set(x_1200, 13, x_1187);
lean_ctor_set(x_1200, 14, x_1188);
lean_ctor_set(x_1200, 15, x_1189);
lean_ctor_set(x_1200, 16, x_1190);
lean_ctor_set(x_1200, 17, x_1191);
lean_ctor_set(x_1200, 18, x_1192);
lean_ctor_set(x_1200, 19, x_1193);
lean_ctor_set(x_1200, 20, x_1194);
lean_ctor_set(x_1200, 21, x_1195);
lean_ctor_set(x_1200, 22, x_1196);
lean_ctor_set(x_1200, 23, x_1197);
lean_ctor_set(x_1200, 24, x_1198);
lean_ctor_set(x_1200, 25, x_1199);
lean_ctor_set_uint8(x_1200, sizeof(void*)*26, x_1180);
x_1201 = lean_st_ref_set(x_13, x_1200, x_1167);
lean_dec(x_13);
x_1202 = lean_ctor_get(x_1201, 1);
lean_inc(x_1202);
if (lean_is_exclusive(x_1201)) {
 lean_ctor_release(x_1201, 0);
 lean_ctor_release(x_1201, 1);
 x_1203 = x_1201;
} else {
 lean_dec_ref(x_1201);
 x_1203 = lean_box(0);
}
if (lean_is_scalar(x_1203)) {
 x_1204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1204 = x_1203;
}
lean_ctor_set(x_1204, 0, x_1);
lean_ctor_set(x_1204, 1, x_1202);
return x_1204;
}
}
else
{
lean_object* x_1205; lean_object* x_1206; 
lean_dec(x_1016);
lean_dec(x_1014);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_1205 = lean_ctor_get(x_1118, 0);
lean_inc(x_1205);
lean_dec(x_1118);
x_1206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1206, 0, x_1205);
lean_ctor_set(x_1206, 1, x_1115);
return x_1206;
}
}
}
else
{
uint8_t x_1207; 
lean_dec(x_1014);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_1207 = !lean_is_exclusive(x_1015);
if (x_1207 == 0)
{
return x_1015;
}
else
{
lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; 
x_1208 = lean_ctor_get(x_1015, 0);
x_1209 = lean_ctor_get(x_1015, 1);
lean_inc(x_1209);
lean_inc(x_1208);
lean_dec(x_1015);
x_1210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1210, 0, x_1208);
lean_ctor_set(x_1210, 1, x_1209);
return x_1210;
}
}
}
block_1249:
{
lean_object* x_1213; 
lean_dec(x_1212);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_9);
x_1213 = l_Lean_Meta_getFunInfo(x_9, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_1213) == 0)
{
lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; uint8_t x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; 
x_1214 = lean_ctor_get(x_1213, 0);
lean_inc(x_1214);
x_1215 = lean_ctor_get(x_1213, 1);
lean_inc(x_1215);
lean_dec(x_1213);
x_1216 = lean_ctor_get(x_1214, 0);
lean_inc(x_1216);
lean_dec(x_1214);
x_1217 = lean_array_get_size(x_10);
x_1218 = lean_unsigned_to_nat(0u);
x_1219 = lean_unsigned_to_nat(1u);
lean_inc(x_1217);
x_1220 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1220, 0, x_1218);
lean_ctor_set(x_1220, 1, x_1217);
lean_ctor_set(x_1220, 2, x_1219);
x_1221 = 0;
x_1222 = lean_box(x_1221);
lean_inc(x_10);
x_1223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1223, 0, x_10);
lean_ctor_set(x_1223, 1, x_1222);
x_1224 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_1220);
lean_inc(x_9);
lean_inc(x_1);
x_1225 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1224, x_1216, x_1217, x_1220, x_1220, x_1223, x_1218, lean_box(0), lean_box(0), x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_1215);
if (lean_obj_tag(x_1225) == 0)
{
lean_object* x_1226; lean_object* x_1227; uint8_t x_1228; 
x_1226 = lean_ctor_get(x_1225, 0);
lean_inc(x_1226);
x_1227 = lean_ctor_get(x_1226, 1);
lean_inc(x_1227);
x_1228 = lean_unbox(x_1227);
lean_dec(x_1227);
if (x_1228 == 0)
{
uint8_t x_1229; 
lean_dec(x_1226);
lean_dec(x_9);
x_1229 = !lean_is_exclusive(x_1225);
if (x_1229 == 0)
{
lean_object* x_1230; 
x_1230 = lean_ctor_get(x_1225, 0);
lean_dec(x_1230);
lean_ctor_set(x_1225, 0, x_1);
return x_1225;
}
else
{
lean_object* x_1231; lean_object* x_1232; 
x_1231 = lean_ctor_get(x_1225, 1);
lean_inc(x_1231);
lean_dec(x_1225);
x_1232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1232, 0, x_1);
lean_ctor_set(x_1232, 1, x_1231);
return x_1232;
}
}
else
{
uint8_t x_1233; 
lean_dec(x_1);
x_1233 = !lean_is_exclusive(x_1225);
if (x_1233 == 0)
{
lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; 
x_1234 = lean_ctor_get(x_1225, 0);
lean_dec(x_1234);
x_1235 = lean_ctor_get(x_1226, 0);
lean_inc(x_1235);
lean_dec(x_1226);
x_1236 = l_Lean_mkAppN(x_9, x_1235);
lean_dec(x_1235);
lean_ctor_set(x_1225, 0, x_1236);
return x_1225;
}
else
{
lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; 
x_1237 = lean_ctor_get(x_1225, 1);
lean_inc(x_1237);
lean_dec(x_1225);
x_1238 = lean_ctor_get(x_1226, 0);
lean_inc(x_1238);
lean_dec(x_1226);
x_1239 = l_Lean_mkAppN(x_9, x_1238);
lean_dec(x_1238);
x_1240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1240, 0, x_1239);
lean_ctor_set(x_1240, 1, x_1237);
return x_1240;
}
}
}
else
{
uint8_t x_1241; 
lean_dec(x_9);
lean_dec(x_1);
x_1241 = !lean_is_exclusive(x_1225);
if (x_1241 == 0)
{
return x_1225;
}
else
{
lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; 
x_1242 = lean_ctor_get(x_1225, 0);
x_1243 = lean_ctor_get(x_1225, 1);
lean_inc(x_1243);
lean_inc(x_1242);
lean_dec(x_1225);
x_1244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1244, 0, x_1242);
lean_ctor_set(x_1244, 1, x_1243);
return x_1244;
}
}
}
else
{
uint8_t x_1245; 
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
x_1245 = !lean_is_exclusive(x_1213);
if (x_1245 == 0)
{
return x_1213;
}
else
{
lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; 
x_1246 = lean_ctor_get(x_1213, 0);
x_1247 = lean_ctor_get(x_1213, 1);
lean_inc(x_1247);
lean_inc(x_1246);
lean_dec(x_1213);
x_1248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1248, 0, x_1246);
lean_ctor_set(x_1248, 1, x_1247);
return x_1248;
}
}
}
}
case 5:
{
lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; 
x_1262 = lean_ctor_get(x_9, 0);
lean_inc(x_1262);
x_1263 = lean_ctor_get(x_9, 1);
lean_inc(x_1263);
lean_dec(x_9);
x_1264 = lean_array_set(x_10, x_11, x_1263);
x_1265 = lean_unsigned_to_nat(1u);
x_1266 = lean_nat_sub(x_11, x_1265);
lean_dec(x_11);
x_9 = x_1262;
x_10 = x_1264;
x_11 = x_1266;
goto _start;
}
case 6:
{
lean_object* x_1268; lean_object* x_1466; lean_object* x_1504; uint8_t x_1505; 
lean_dec(x_11);
x_1504 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_1505 = l_Lean_Expr_isConstOf(x_9, x_1504);
if (x_1505 == 0)
{
lean_object* x_1506; 
x_1506 = lean_box(0);
x_1466 = x_1506;
goto block_1503;
}
else
{
lean_object* x_1507; lean_object* x_1508; uint8_t x_1509; 
x_1507 = lean_array_get_size(x_10);
x_1508 = lean_unsigned_to_nat(2u);
x_1509 = lean_nat_dec_eq(x_1507, x_1508);
if (x_1509 == 0)
{
lean_object* x_1510; 
lean_dec(x_1507);
x_1510 = lean_box(0);
x_1466 = x_1510;
goto block_1503;
}
else
{
lean_object* x_1511; uint8_t x_1512; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1511 = lean_unsigned_to_nat(0u);
x_1512 = lean_nat_dec_lt(x_1511, x_1507);
lean_dec(x_1507);
if (x_1512 == 0)
{
lean_object* x_1513; lean_object* x_1514; 
x_1513 = l_Lean_instInhabitedExpr;
x_1514 = l_outOfBounds___rarg(x_1513);
x_1268 = x_1514;
goto block_1465;
}
else
{
lean_object* x_1515; 
x_1515 = lean_array_fget(x_10, x_1511);
x_1268 = x_1515;
goto block_1465;
}
}
}
block_1465:
{
lean_object* x_1269; 
lean_inc(x_13);
lean_inc(x_1268);
x_1269 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_1268, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_1269) == 0)
{
lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; uint8_t x_1273; 
x_1270 = lean_ctor_get(x_1269, 0);
lean_inc(x_1270);
x_1271 = lean_ctor_get(x_1269, 1);
lean_inc(x_1271);
lean_dec(x_1269);
x_1272 = lean_st_ref_get(x_13, x_1271);
x_1273 = !lean_is_exclusive(x_1272);
if (x_1273 == 0)
{
lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; 
x_1274 = lean_ctor_get(x_1272, 0);
x_1275 = lean_ctor_get(x_1272, 1);
x_1276 = lean_ctor_get(x_1274, 1);
lean_inc(x_1276);
lean_dec(x_1274);
x_1277 = lean_ctor_get(x_1276, 2);
lean_inc(x_1277);
lean_dec(x_1276);
x_1278 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_1277, x_1270);
if (lean_obj_tag(x_1278) == 0)
{
size_t x_1279; size_t x_1280; uint8_t x_1281; 
lean_free_object(x_1272);
x_1279 = lean_ptr_addr(x_1268);
lean_dec(x_1268);
x_1280 = lean_ptr_addr(x_1270);
x_1281 = lean_usize_dec_eq(x_1279, x_1280);
if (x_1281 == 0)
{
lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; uint8_t x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; uint8_t x_1322; 
lean_dec(x_1);
x_1282 = lean_unsigned_to_nat(0u);
lean_inc(x_1270);
x_1283 = lean_array_set(x_10, x_1282, x_1270);
x_1284 = l_Lean_mkAppN(x_9, x_1283);
lean_dec(x_1283);
x_1285 = lean_st_ref_take(x_13, x_1275);
x_1286 = lean_ctor_get(x_1285, 0);
lean_inc(x_1286);
x_1287 = lean_ctor_get(x_1285, 1);
lean_inc(x_1287);
lean_dec(x_1285);
x_1288 = lean_ctor_get(x_1286, 0);
lean_inc(x_1288);
x_1289 = lean_ctor_get(x_1286, 1);
lean_inc(x_1289);
x_1290 = lean_ctor_get(x_1289, 0);
lean_inc(x_1290);
x_1291 = lean_ctor_get(x_1289, 1);
lean_inc(x_1291);
x_1292 = lean_ctor_get(x_1289, 2);
lean_inc(x_1292);
lean_dec(x_1289);
lean_inc(x_1284);
x_1293 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1292, x_1270, x_1284);
x_1294 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1294, 0, x_1290);
lean_ctor_set(x_1294, 1, x_1291);
lean_ctor_set(x_1294, 2, x_1293);
x_1295 = lean_ctor_get(x_1286, 2);
lean_inc(x_1295);
x_1296 = lean_ctor_get(x_1286, 3);
lean_inc(x_1296);
x_1297 = lean_ctor_get(x_1286, 4);
lean_inc(x_1297);
x_1298 = lean_ctor_get(x_1286, 5);
lean_inc(x_1298);
x_1299 = lean_ctor_get(x_1286, 6);
lean_inc(x_1299);
x_1300 = lean_ctor_get_uint8(x_1286, sizeof(void*)*26);
x_1301 = lean_ctor_get(x_1286, 7);
lean_inc(x_1301);
x_1302 = lean_ctor_get(x_1286, 8);
lean_inc(x_1302);
x_1303 = lean_ctor_get(x_1286, 9);
lean_inc(x_1303);
x_1304 = lean_ctor_get(x_1286, 10);
lean_inc(x_1304);
x_1305 = lean_ctor_get(x_1286, 11);
lean_inc(x_1305);
x_1306 = lean_ctor_get(x_1286, 12);
lean_inc(x_1306);
x_1307 = lean_ctor_get(x_1286, 13);
lean_inc(x_1307);
x_1308 = lean_ctor_get(x_1286, 14);
lean_inc(x_1308);
x_1309 = lean_ctor_get(x_1286, 15);
lean_inc(x_1309);
x_1310 = lean_ctor_get(x_1286, 16);
lean_inc(x_1310);
x_1311 = lean_ctor_get(x_1286, 17);
lean_inc(x_1311);
x_1312 = lean_ctor_get(x_1286, 18);
lean_inc(x_1312);
x_1313 = lean_ctor_get(x_1286, 19);
lean_inc(x_1313);
x_1314 = lean_ctor_get(x_1286, 20);
lean_inc(x_1314);
x_1315 = lean_ctor_get(x_1286, 21);
lean_inc(x_1315);
x_1316 = lean_ctor_get(x_1286, 22);
lean_inc(x_1316);
x_1317 = lean_ctor_get(x_1286, 23);
lean_inc(x_1317);
x_1318 = lean_ctor_get(x_1286, 24);
lean_inc(x_1318);
x_1319 = lean_ctor_get(x_1286, 25);
lean_inc(x_1319);
lean_dec(x_1286);
x_1320 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_1320, 0, x_1288);
lean_ctor_set(x_1320, 1, x_1294);
lean_ctor_set(x_1320, 2, x_1295);
lean_ctor_set(x_1320, 3, x_1296);
lean_ctor_set(x_1320, 4, x_1297);
lean_ctor_set(x_1320, 5, x_1298);
lean_ctor_set(x_1320, 6, x_1299);
lean_ctor_set(x_1320, 7, x_1301);
lean_ctor_set(x_1320, 8, x_1302);
lean_ctor_set(x_1320, 9, x_1303);
lean_ctor_set(x_1320, 10, x_1304);
lean_ctor_set(x_1320, 11, x_1305);
lean_ctor_set(x_1320, 12, x_1306);
lean_ctor_set(x_1320, 13, x_1307);
lean_ctor_set(x_1320, 14, x_1308);
lean_ctor_set(x_1320, 15, x_1309);
lean_ctor_set(x_1320, 16, x_1310);
lean_ctor_set(x_1320, 17, x_1311);
lean_ctor_set(x_1320, 18, x_1312);
lean_ctor_set(x_1320, 19, x_1313);
lean_ctor_set(x_1320, 20, x_1314);
lean_ctor_set(x_1320, 21, x_1315);
lean_ctor_set(x_1320, 22, x_1316);
lean_ctor_set(x_1320, 23, x_1317);
lean_ctor_set(x_1320, 24, x_1318);
lean_ctor_set(x_1320, 25, x_1319);
lean_ctor_set_uint8(x_1320, sizeof(void*)*26, x_1300);
x_1321 = lean_st_ref_set(x_13, x_1320, x_1287);
lean_dec(x_13);
x_1322 = !lean_is_exclusive(x_1321);
if (x_1322 == 0)
{
lean_object* x_1323; 
x_1323 = lean_ctor_get(x_1321, 0);
lean_dec(x_1323);
lean_ctor_set(x_1321, 0, x_1284);
return x_1321;
}
else
{
lean_object* x_1324; lean_object* x_1325; 
x_1324 = lean_ctor_get(x_1321, 1);
lean_inc(x_1324);
lean_dec(x_1321);
x_1325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1325, 0, x_1284);
lean_ctor_set(x_1325, 1, x_1324);
return x_1325;
}
}
else
{
lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; uint8_t x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; uint8_t x_1363; 
lean_dec(x_10);
lean_dec(x_9);
x_1326 = lean_st_ref_take(x_13, x_1275);
x_1327 = lean_ctor_get(x_1326, 0);
lean_inc(x_1327);
x_1328 = lean_ctor_get(x_1326, 1);
lean_inc(x_1328);
lean_dec(x_1326);
x_1329 = lean_ctor_get(x_1327, 0);
lean_inc(x_1329);
x_1330 = lean_ctor_get(x_1327, 1);
lean_inc(x_1330);
x_1331 = lean_ctor_get(x_1330, 0);
lean_inc(x_1331);
x_1332 = lean_ctor_get(x_1330, 1);
lean_inc(x_1332);
x_1333 = lean_ctor_get(x_1330, 2);
lean_inc(x_1333);
lean_dec(x_1330);
lean_inc(x_1);
x_1334 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1333, x_1270, x_1);
x_1335 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1335, 0, x_1331);
lean_ctor_set(x_1335, 1, x_1332);
lean_ctor_set(x_1335, 2, x_1334);
x_1336 = lean_ctor_get(x_1327, 2);
lean_inc(x_1336);
x_1337 = lean_ctor_get(x_1327, 3);
lean_inc(x_1337);
x_1338 = lean_ctor_get(x_1327, 4);
lean_inc(x_1338);
x_1339 = lean_ctor_get(x_1327, 5);
lean_inc(x_1339);
x_1340 = lean_ctor_get(x_1327, 6);
lean_inc(x_1340);
x_1341 = lean_ctor_get_uint8(x_1327, sizeof(void*)*26);
x_1342 = lean_ctor_get(x_1327, 7);
lean_inc(x_1342);
x_1343 = lean_ctor_get(x_1327, 8);
lean_inc(x_1343);
x_1344 = lean_ctor_get(x_1327, 9);
lean_inc(x_1344);
x_1345 = lean_ctor_get(x_1327, 10);
lean_inc(x_1345);
x_1346 = lean_ctor_get(x_1327, 11);
lean_inc(x_1346);
x_1347 = lean_ctor_get(x_1327, 12);
lean_inc(x_1347);
x_1348 = lean_ctor_get(x_1327, 13);
lean_inc(x_1348);
x_1349 = lean_ctor_get(x_1327, 14);
lean_inc(x_1349);
x_1350 = lean_ctor_get(x_1327, 15);
lean_inc(x_1350);
x_1351 = lean_ctor_get(x_1327, 16);
lean_inc(x_1351);
x_1352 = lean_ctor_get(x_1327, 17);
lean_inc(x_1352);
x_1353 = lean_ctor_get(x_1327, 18);
lean_inc(x_1353);
x_1354 = lean_ctor_get(x_1327, 19);
lean_inc(x_1354);
x_1355 = lean_ctor_get(x_1327, 20);
lean_inc(x_1355);
x_1356 = lean_ctor_get(x_1327, 21);
lean_inc(x_1356);
x_1357 = lean_ctor_get(x_1327, 22);
lean_inc(x_1357);
x_1358 = lean_ctor_get(x_1327, 23);
lean_inc(x_1358);
x_1359 = lean_ctor_get(x_1327, 24);
lean_inc(x_1359);
x_1360 = lean_ctor_get(x_1327, 25);
lean_inc(x_1360);
lean_dec(x_1327);
x_1361 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_1361, 0, x_1329);
lean_ctor_set(x_1361, 1, x_1335);
lean_ctor_set(x_1361, 2, x_1336);
lean_ctor_set(x_1361, 3, x_1337);
lean_ctor_set(x_1361, 4, x_1338);
lean_ctor_set(x_1361, 5, x_1339);
lean_ctor_set(x_1361, 6, x_1340);
lean_ctor_set(x_1361, 7, x_1342);
lean_ctor_set(x_1361, 8, x_1343);
lean_ctor_set(x_1361, 9, x_1344);
lean_ctor_set(x_1361, 10, x_1345);
lean_ctor_set(x_1361, 11, x_1346);
lean_ctor_set(x_1361, 12, x_1347);
lean_ctor_set(x_1361, 13, x_1348);
lean_ctor_set(x_1361, 14, x_1349);
lean_ctor_set(x_1361, 15, x_1350);
lean_ctor_set(x_1361, 16, x_1351);
lean_ctor_set(x_1361, 17, x_1352);
lean_ctor_set(x_1361, 18, x_1353);
lean_ctor_set(x_1361, 19, x_1354);
lean_ctor_set(x_1361, 20, x_1355);
lean_ctor_set(x_1361, 21, x_1356);
lean_ctor_set(x_1361, 22, x_1357);
lean_ctor_set(x_1361, 23, x_1358);
lean_ctor_set(x_1361, 24, x_1359);
lean_ctor_set(x_1361, 25, x_1360);
lean_ctor_set_uint8(x_1361, sizeof(void*)*26, x_1341);
x_1362 = lean_st_ref_set(x_13, x_1361, x_1328);
lean_dec(x_13);
x_1363 = !lean_is_exclusive(x_1362);
if (x_1363 == 0)
{
lean_object* x_1364; 
x_1364 = lean_ctor_get(x_1362, 0);
lean_dec(x_1364);
lean_ctor_set(x_1362, 0, x_1);
return x_1362;
}
else
{
lean_object* x_1365; lean_object* x_1366; 
x_1365 = lean_ctor_get(x_1362, 1);
lean_inc(x_1365);
lean_dec(x_1362);
x_1366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1366, 0, x_1);
lean_ctor_set(x_1366, 1, x_1365);
return x_1366;
}
}
}
else
{
lean_object* x_1367; 
lean_dec(x_1270);
lean_dec(x_1268);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_1367 = lean_ctor_get(x_1278, 0);
lean_inc(x_1367);
lean_dec(x_1278);
lean_ctor_set(x_1272, 0, x_1367);
return x_1272;
}
}
else
{
lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; 
x_1368 = lean_ctor_get(x_1272, 0);
x_1369 = lean_ctor_get(x_1272, 1);
lean_inc(x_1369);
lean_inc(x_1368);
lean_dec(x_1272);
x_1370 = lean_ctor_get(x_1368, 1);
lean_inc(x_1370);
lean_dec(x_1368);
x_1371 = lean_ctor_get(x_1370, 2);
lean_inc(x_1371);
lean_dec(x_1370);
x_1372 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_1371, x_1270);
if (lean_obj_tag(x_1372) == 0)
{
size_t x_1373; size_t x_1374; uint8_t x_1375; 
x_1373 = lean_ptr_addr(x_1268);
lean_dec(x_1268);
x_1374 = lean_ptr_addr(x_1270);
x_1375 = lean_usize_dec_eq(x_1373, x_1374);
if (x_1375 == 0)
{
lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; uint8_t x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; 
lean_dec(x_1);
x_1376 = lean_unsigned_to_nat(0u);
lean_inc(x_1270);
x_1377 = lean_array_set(x_10, x_1376, x_1270);
x_1378 = l_Lean_mkAppN(x_9, x_1377);
lean_dec(x_1377);
x_1379 = lean_st_ref_take(x_13, x_1369);
x_1380 = lean_ctor_get(x_1379, 0);
lean_inc(x_1380);
x_1381 = lean_ctor_get(x_1379, 1);
lean_inc(x_1381);
lean_dec(x_1379);
x_1382 = lean_ctor_get(x_1380, 0);
lean_inc(x_1382);
x_1383 = lean_ctor_get(x_1380, 1);
lean_inc(x_1383);
x_1384 = lean_ctor_get(x_1383, 0);
lean_inc(x_1384);
x_1385 = lean_ctor_get(x_1383, 1);
lean_inc(x_1385);
x_1386 = lean_ctor_get(x_1383, 2);
lean_inc(x_1386);
lean_dec(x_1383);
lean_inc(x_1378);
x_1387 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1386, x_1270, x_1378);
x_1388 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1388, 0, x_1384);
lean_ctor_set(x_1388, 1, x_1385);
lean_ctor_set(x_1388, 2, x_1387);
x_1389 = lean_ctor_get(x_1380, 2);
lean_inc(x_1389);
x_1390 = lean_ctor_get(x_1380, 3);
lean_inc(x_1390);
x_1391 = lean_ctor_get(x_1380, 4);
lean_inc(x_1391);
x_1392 = lean_ctor_get(x_1380, 5);
lean_inc(x_1392);
x_1393 = lean_ctor_get(x_1380, 6);
lean_inc(x_1393);
x_1394 = lean_ctor_get_uint8(x_1380, sizeof(void*)*26);
x_1395 = lean_ctor_get(x_1380, 7);
lean_inc(x_1395);
x_1396 = lean_ctor_get(x_1380, 8);
lean_inc(x_1396);
x_1397 = lean_ctor_get(x_1380, 9);
lean_inc(x_1397);
x_1398 = lean_ctor_get(x_1380, 10);
lean_inc(x_1398);
x_1399 = lean_ctor_get(x_1380, 11);
lean_inc(x_1399);
x_1400 = lean_ctor_get(x_1380, 12);
lean_inc(x_1400);
x_1401 = lean_ctor_get(x_1380, 13);
lean_inc(x_1401);
x_1402 = lean_ctor_get(x_1380, 14);
lean_inc(x_1402);
x_1403 = lean_ctor_get(x_1380, 15);
lean_inc(x_1403);
x_1404 = lean_ctor_get(x_1380, 16);
lean_inc(x_1404);
x_1405 = lean_ctor_get(x_1380, 17);
lean_inc(x_1405);
x_1406 = lean_ctor_get(x_1380, 18);
lean_inc(x_1406);
x_1407 = lean_ctor_get(x_1380, 19);
lean_inc(x_1407);
x_1408 = lean_ctor_get(x_1380, 20);
lean_inc(x_1408);
x_1409 = lean_ctor_get(x_1380, 21);
lean_inc(x_1409);
x_1410 = lean_ctor_get(x_1380, 22);
lean_inc(x_1410);
x_1411 = lean_ctor_get(x_1380, 23);
lean_inc(x_1411);
x_1412 = lean_ctor_get(x_1380, 24);
lean_inc(x_1412);
x_1413 = lean_ctor_get(x_1380, 25);
lean_inc(x_1413);
lean_dec(x_1380);
x_1414 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_1414, 0, x_1382);
lean_ctor_set(x_1414, 1, x_1388);
lean_ctor_set(x_1414, 2, x_1389);
lean_ctor_set(x_1414, 3, x_1390);
lean_ctor_set(x_1414, 4, x_1391);
lean_ctor_set(x_1414, 5, x_1392);
lean_ctor_set(x_1414, 6, x_1393);
lean_ctor_set(x_1414, 7, x_1395);
lean_ctor_set(x_1414, 8, x_1396);
lean_ctor_set(x_1414, 9, x_1397);
lean_ctor_set(x_1414, 10, x_1398);
lean_ctor_set(x_1414, 11, x_1399);
lean_ctor_set(x_1414, 12, x_1400);
lean_ctor_set(x_1414, 13, x_1401);
lean_ctor_set(x_1414, 14, x_1402);
lean_ctor_set(x_1414, 15, x_1403);
lean_ctor_set(x_1414, 16, x_1404);
lean_ctor_set(x_1414, 17, x_1405);
lean_ctor_set(x_1414, 18, x_1406);
lean_ctor_set(x_1414, 19, x_1407);
lean_ctor_set(x_1414, 20, x_1408);
lean_ctor_set(x_1414, 21, x_1409);
lean_ctor_set(x_1414, 22, x_1410);
lean_ctor_set(x_1414, 23, x_1411);
lean_ctor_set(x_1414, 24, x_1412);
lean_ctor_set(x_1414, 25, x_1413);
lean_ctor_set_uint8(x_1414, sizeof(void*)*26, x_1394);
x_1415 = lean_st_ref_set(x_13, x_1414, x_1381);
lean_dec(x_13);
x_1416 = lean_ctor_get(x_1415, 1);
lean_inc(x_1416);
if (lean_is_exclusive(x_1415)) {
 lean_ctor_release(x_1415, 0);
 lean_ctor_release(x_1415, 1);
 x_1417 = x_1415;
} else {
 lean_dec_ref(x_1415);
 x_1417 = lean_box(0);
}
if (lean_is_scalar(x_1417)) {
 x_1418 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1418 = x_1417;
}
lean_ctor_set(x_1418, 0, x_1378);
lean_ctor_set(x_1418, 1, x_1416);
return x_1418;
}
else
{
lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; uint8_t x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; 
lean_dec(x_10);
lean_dec(x_9);
x_1419 = lean_st_ref_take(x_13, x_1369);
x_1420 = lean_ctor_get(x_1419, 0);
lean_inc(x_1420);
x_1421 = lean_ctor_get(x_1419, 1);
lean_inc(x_1421);
lean_dec(x_1419);
x_1422 = lean_ctor_get(x_1420, 0);
lean_inc(x_1422);
x_1423 = lean_ctor_get(x_1420, 1);
lean_inc(x_1423);
x_1424 = lean_ctor_get(x_1423, 0);
lean_inc(x_1424);
x_1425 = lean_ctor_get(x_1423, 1);
lean_inc(x_1425);
x_1426 = lean_ctor_get(x_1423, 2);
lean_inc(x_1426);
lean_dec(x_1423);
lean_inc(x_1);
x_1427 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1426, x_1270, x_1);
x_1428 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1428, 0, x_1424);
lean_ctor_set(x_1428, 1, x_1425);
lean_ctor_set(x_1428, 2, x_1427);
x_1429 = lean_ctor_get(x_1420, 2);
lean_inc(x_1429);
x_1430 = lean_ctor_get(x_1420, 3);
lean_inc(x_1430);
x_1431 = lean_ctor_get(x_1420, 4);
lean_inc(x_1431);
x_1432 = lean_ctor_get(x_1420, 5);
lean_inc(x_1432);
x_1433 = lean_ctor_get(x_1420, 6);
lean_inc(x_1433);
x_1434 = lean_ctor_get_uint8(x_1420, sizeof(void*)*26);
x_1435 = lean_ctor_get(x_1420, 7);
lean_inc(x_1435);
x_1436 = lean_ctor_get(x_1420, 8);
lean_inc(x_1436);
x_1437 = lean_ctor_get(x_1420, 9);
lean_inc(x_1437);
x_1438 = lean_ctor_get(x_1420, 10);
lean_inc(x_1438);
x_1439 = lean_ctor_get(x_1420, 11);
lean_inc(x_1439);
x_1440 = lean_ctor_get(x_1420, 12);
lean_inc(x_1440);
x_1441 = lean_ctor_get(x_1420, 13);
lean_inc(x_1441);
x_1442 = lean_ctor_get(x_1420, 14);
lean_inc(x_1442);
x_1443 = lean_ctor_get(x_1420, 15);
lean_inc(x_1443);
x_1444 = lean_ctor_get(x_1420, 16);
lean_inc(x_1444);
x_1445 = lean_ctor_get(x_1420, 17);
lean_inc(x_1445);
x_1446 = lean_ctor_get(x_1420, 18);
lean_inc(x_1446);
x_1447 = lean_ctor_get(x_1420, 19);
lean_inc(x_1447);
x_1448 = lean_ctor_get(x_1420, 20);
lean_inc(x_1448);
x_1449 = lean_ctor_get(x_1420, 21);
lean_inc(x_1449);
x_1450 = lean_ctor_get(x_1420, 22);
lean_inc(x_1450);
x_1451 = lean_ctor_get(x_1420, 23);
lean_inc(x_1451);
x_1452 = lean_ctor_get(x_1420, 24);
lean_inc(x_1452);
x_1453 = lean_ctor_get(x_1420, 25);
lean_inc(x_1453);
lean_dec(x_1420);
x_1454 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_1454, 0, x_1422);
lean_ctor_set(x_1454, 1, x_1428);
lean_ctor_set(x_1454, 2, x_1429);
lean_ctor_set(x_1454, 3, x_1430);
lean_ctor_set(x_1454, 4, x_1431);
lean_ctor_set(x_1454, 5, x_1432);
lean_ctor_set(x_1454, 6, x_1433);
lean_ctor_set(x_1454, 7, x_1435);
lean_ctor_set(x_1454, 8, x_1436);
lean_ctor_set(x_1454, 9, x_1437);
lean_ctor_set(x_1454, 10, x_1438);
lean_ctor_set(x_1454, 11, x_1439);
lean_ctor_set(x_1454, 12, x_1440);
lean_ctor_set(x_1454, 13, x_1441);
lean_ctor_set(x_1454, 14, x_1442);
lean_ctor_set(x_1454, 15, x_1443);
lean_ctor_set(x_1454, 16, x_1444);
lean_ctor_set(x_1454, 17, x_1445);
lean_ctor_set(x_1454, 18, x_1446);
lean_ctor_set(x_1454, 19, x_1447);
lean_ctor_set(x_1454, 20, x_1448);
lean_ctor_set(x_1454, 21, x_1449);
lean_ctor_set(x_1454, 22, x_1450);
lean_ctor_set(x_1454, 23, x_1451);
lean_ctor_set(x_1454, 24, x_1452);
lean_ctor_set(x_1454, 25, x_1453);
lean_ctor_set_uint8(x_1454, sizeof(void*)*26, x_1434);
x_1455 = lean_st_ref_set(x_13, x_1454, x_1421);
lean_dec(x_13);
x_1456 = lean_ctor_get(x_1455, 1);
lean_inc(x_1456);
if (lean_is_exclusive(x_1455)) {
 lean_ctor_release(x_1455, 0);
 lean_ctor_release(x_1455, 1);
 x_1457 = x_1455;
} else {
 lean_dec_ref(x_1455);
 x_1457 = lean_box(0);
}
if (lean_is_scalar(x_1457)) {
 x_1458 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1458 = x_1457;
}
lean_ctor_set(x_1458, 0, x_1);
lean_ctor_set(x_1458, 1, x_1456);
return x_1458;
}
}
else
{
lean_object* x_1459; lean_object* x_1460; 
lean_dec(x_1270);
lean_dec(x_1268);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_1459 = lean_ctor_get(x_1372, 0);
lean_inc(x_1459);
lean_dec(x_1372);
x_1460 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1460, 0, x_1459);
lean_ctor_set(x_1460, 1, x_1369);
return x_1460;
}
}
}
else
{
uint8_t x_1461; 
lean_dec(x_1268);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_1461 = !lean_is_exclusive(x_1269);
if (x_1461 == 0)
{
return x_1269;
}
else
{
lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; 
x_1462 = lean_ctor_get(x_1269, 0);
x_1463 = lean_ctor_get(x_1269, 1);
lean_inc(x_1463);
lean_inc(x_1462);
lean_dec(x_1269);
x_1464 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1464, 0, x_1462);
lean_ctor_set(x_1464, 1, x_1463);
return x_1464;
}
}
}
block_1503:
{
lean_object* x_1467; 
lean_dec(x_1466);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_9);
x_1467 = l_Lean_Meta_getFunInfo(x_9, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_1467) == 0)
{
lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; uint8_t x_1475; lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; lean_object* x_1479; 
x_1468 = lean_ctor_get(x_1467, 0);
lean_inc(x_1468);
x_1469 = lean_ctor_get(x_1467, 1);
lean_inc(x_1469);
lean_dec(x_1467);
x_1470 = lean_ctor_get(x_1468, 0);
lean_inc(x_1470);
lean_dec(x_1468);
x_1471 = lean_array_get_size(x_10);
x_1472 = lean_unsigned_to_nat(0u);
x_1473 = lean_unsigned_to_nat(1u);
lean_inc(x_1471);
x_1474 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1474, 0, x_1472);
lean_ctor_set(x_1474, 1, x_1471);
lean_ctor_set(x_1474, 2, x_1473);
x_1475 = 0;
x_1476 = lean_box(x_1475);
lean_inc(x_10);
x_1477 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1477, 0, x_10);
lean_ctor_set(x_1477, 1, x_1476);
x_1478 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_1474);
lean_inc(x_9);
lean_inc(x_1);
x_1479 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1478, x_1470, x_1471, x_1474, x_1474, x_1477, x_1472, lean_box(0), lean_box(0), x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_1469);
if (lean_obj_tag(x_1479) == 0)
{
lean_object* x_1480; lean_object* x_1481; uint8_t x_1482; 
x_1480 = lean_ctor_get(x_1479, 0);
lean_inc(x_1480);
x_1481 = lean_ctor_get(x_1480, 1);
lean_inc(x_1481);
x_1482 = lean_unbox(x_1481);
lean_dec(x_1481);
if (x_1482 == 0)
{
uint8_t x_1483; 
lean_dec(x_1480);
lean_dec(x_9);
x_1483 = !lean_is_exclusive(x_1479);
if (x_1483 == 0)
{
lean_object* x_1484; 
x_1484 = lean_ctor_get(x_1479, 0);
lean_dec(x_1484);
lean_ctor_set(x_1479, 0, x_1);
return x_1479;
}
else
{
lean_object* x_1485; lean_object* x_1486; 
x_1485 = lean_ctor_get(x_1479, 1);
lean_inc(x_1485);
lean_dec(x_1479);
x_1486 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1486, 0, x_1);
lean_ctor_set(x_1486, 1, x_1485);
return x_1486;
}
}
else
{
uint8_t x_1487; 
lean_dec(x_1);
x_1487 = !lean_is_exclusive(x_1479);
if (x_1487 == 0)
{
lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; 
x_1488 = lean_ctor_get(x_1479, 0);
lean_dec(x_1488);
x_1489 = lean_ctor_get(x_1480, 0);
lean_inc(x_1489);
lean_dec(x_1480);
x_1490 = l_Lean_mkAppN(x_9, x_1489);
lean_dec(x_1489);
lean_ctor_set(x_1479, 0, x_1490);
return x_1479;
}
else
{
lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; 
x_1491 = lean_ctor_get(x_1479, 1);
lean_inc(x_1491);
lean_dec(x_1479);
x_1492 = lean_ctor_get(x_1480, 0);
lean_inc(x_1492);
lean_dec(x_1480);
x_1493 = l_Lean_mkAppN(x_9, x_1492);
lean_dec(x_1492);
x_1494 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1494, 0, x_1493);
lean_ctor_set(x_1494, 1, x_1491);
return x_1494;
}
}
}
else
{
uint8_t x_1495; 
lean_dec(x_9);
lean_dec(x_1);
x_1495 = !lean_is_exclusive(x_1479);
if (x_1495 == 0)
{
return x_1479;
}
else
{
lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; 
x_1496 = lean_ctor_get(x_1479, 0);
x_1497 = lean_ctor_get(x_1479, 1);
lean_inc(x_1497);
lean_inc(x_1496);
lean_dec(x_1479);
x_1498 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1498, 0, x_1496);
lean_ctor_set(x_1498, 1, x_1497);
return x_1498;
}
}
}
else
{
uint8_t x_1499; 
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
x_1499 = !lean_is_exclusive(x_1467);
if (x_1499 == 0)
{
return x_1467;
}
else
{
lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; 
x_1500 = lean_ctor_get(x_1467, 0);
x_1501 = lean_ctor_get(x_1467, 1);
lean_inc(x_1501);
lean_inc(x_1500);
lean_dec(x_1467);
x_1502 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1502, 0, x_1500);
lean_ctor_set(x_1502, 1, x_1501);
return x_1502;
}
}
}
}
case 7:
{
lean_object* x_1516; lean_object* x_1714; lean_object* x_1752; uint8_t x_1753; 
lean_dec(x_11);
x_1752 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_1753 = l_Lean_Expr_isConstOf(x_9, x_1752);
if (x_1753 == 0)
{
lean_object* x_1754; 
x_1754 = lean_box(0);
x_1714 = x_1754;
goto block_1751;
}
else
{
lean_object* x_1755; lean_object* x_1756; uint8_t x_1757; 
x_1755 = lean_array_get_size(x_10);
x_1756 = lean_unsigned_to_nat(2u);
x_1757 = lean_nat_dec_eq(x_1755, x_1756);
if (x_1757 == 0)
{
lean_object* x_1758; 
lean_dec(x_1755);
x_1758 = lean_box(0);
x_1714 = x_1758;
goto block_1751;
}
else
{
lean_object* x_1759; uint8_t x_1760; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1759 = lean_unsigned_to_nat(0u);
x_1760 = lean_nat_dec_lt(x_1759, x_1755);
lean_dec(x_1755);
if (x_1760 == 0)
{
lean_object* x_1761; lean_object* x_1762; 
x_1761 = l_Lean_instInhabitedExpr;
x_1762 = l_outOfBounds___rarg(x_1761);
x_1516 = x_1762;
goto block_1713;
}
else
{
lean_object* x_1763; 
x_1763 = lean_array_fget(x_10, x_1759);
x_1516 = x_1763;
goto block_1713;
}
}
}
block_1713:
{
lean_object* x_1517; 
lean_inc(x_13);
lean_inc(x_1516);
x_1517 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_1516, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_1517) == 0)
{
lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; uint8_t x_1521; 
x_1518 = lean_ctor_get(x_1517, 0);
lean_inc(x_1518);
x_1519 = lean_ctor_get(x_1517, 1);
lean_inc(x_1519);
lean_dec(x_1517);
x_1520 = lean_st_ref_get(x_13, x_1519);
x_1521 = !lean_is_exclusive(x_1520);
if (x_1521 == 0)
{
lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; 
x_1522 = lean_ctor_get(x_1520, 0);
x_1523 = lean_ctor_get(x_1520, 1);
x_1524 = lean_ctor_get(x_1522, 1);
lean_inc(x_1524);
lean_dec(x_1522);
x_1525 = lean_ctor_get(x_1524, 2);
lean_inc(x_1525);
lean_dec(x_1524);
x_1526 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_1525, x_1518);
if (lean_obj_tag(x_1526) == 0)
{
size_t x_1527; size_t x_1528; uint8_t x_1529; 
lean_free_object(x_1520);
x_1527 = lean_ptr_addr(x_1516);
lean_dec(x_1516);
x_1528 = lean_ptr_addr(x_1518);
x_1529 = lean_usize_dec_eq(x_1527, x_1528);
if (x_1529 == 0)
{
lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; lean_object* x_1547; uint8_t x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; uint8_t x_1570; 
lean_dec(x_1);
x_1530 = lean_unsigned_to_nat(0u);
lean_inc(x_1518);
x_1531 = lean_array_set(x_10, x_1530, x_1518);
x_1532 = l_Lean_mkAppN(x_9, x_1531);
lean_dec(x_1531);
x_1533 = lean_st_ref_take(x_13, x_1523);
x_1534 = lean_ctor_get(x_1533, 0);
lean_inc(x_1534);
x_1535 = lean_ctor_get(x_1533, 1);
lean_inc(x_1535);
lean_dec(x_1533);
x_1536 = lean_ctor_get(x_1534, 0);
lean_inc(x_1536);
x_1537 = lean_ctor_get(x_1534, 1);
lean_inc(x_1537);
x_1538 = lean_ctor_get(x_1537, 0);
lean_inc(x_1538);
x_1539 = lean_ctor_get(x_1537, 1);
lean_inc(x_1539);
x_1540 = lean_ctor_get(x_1537, 2);
lean_inc(x_1540);
lean_dec(x_1537);
lean_inc(x_1532);
x_1541 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1540, x_1518, x_1532);
x_1542 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1542, 0, x_1538);
lean_ctor_set(x_1542, 1, x_1539);
lean_ctor_set(x_1542, 2, x_1541);
x_1543 = lean_ctor_get(x_1534, 2);
lean_inc(x_1543);
x_1544 = lean_ctor_get(x_1534, 3);
lean_inc(x_1544);
x_1545 = lean_ctor_get(x_1534, 4);
lean_inc(x_1545);
x_1546 = lean_ctor_get(x_1534, 5);
lean_inc(x_1546);
x_1547 = lean_ctor_get(x_1534, 6);
lean_inc(x_1547);
x_1548 = lean_ctor_get_uint8(x_1534, sizeof(void*)*26);
x_1549 = lean_ctor_get(x_1534, 7);
lean_inc(x_1549);
x_1550 = lean_ctor_get(x_1534, 8);
lean_inc(x_1550);
x_1551 = lean_ctor_get(x_1534, 9);
lean_inc(x_1551);
x_1552 = lean_ctor_get(x_1534, 10);
lean_inc(x_1552);
x_1553 = lean_ctor_get(x_1534, 11);
lean_inc(x_1553);
x_1554 = lean_ctor_get(x_1534, 12);
lean_inc(x_1554);
x_1555 = lean_ctor_get(x_1534, 13);
lean_inc(x_1555);
x_1556 = lean_ctor_get(x_1534, 14);
lean_inc(x_1556);
x_1557 = lean_ctor_get(x_1534, 15);
lean_inc(x_1557);
x_1558 = lean_ctor_get(x_1534, 16);
lean_inc(x_1558);
x_1559 = lean_ctor_get(x_1534, 17);
lean_inc(x_1559);
x_1560 = lean_ctor_get(x_1534, 18);
lean_inc(x_1560);
x_1561 = lean_ctor_get(x_1534, 19);
lean_inc(x_1561);
x_1562 = lean_ctor_get(x_1534, 20);
lean_inc(x_1562);
x_1563 = lean_ctor_get(x_1534, 21);
lean_inc(x_1563);
x_1564 = lean_ctor_get(x_1534, 22);
lean_inc(x_1564);
x_1565 = lean_ctor_get(x_1534, 23);
lean_inc(x_1565);
x_1566 = lean_ctor_get(x_1534, 24);
lean_inc(x_1566);
x_1567 = lean_ctor_get(x_1534, 25);
lean_inc(x_1567);
lean_dec(x_1534);
x_1568 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_1568, 0, x_1536);
lean_ctor_set(x_1568, 1, x_1542);
lean_ctor_set(x_1568, 2, x_1543);
lean_ctor_set(x_1568, 3, x_1544);
lean_ctor_set(x_1568, 4, x_1545);
lean_ctor_set(x_1568, 5, x_1546);
lean_ctor_set(x_1568, 6, x_1547);
lean_ctor_set(x_1568, 7, x_1549);
lean_ctor_set(x_1568, 8, x_1550);
lean_ctor_set(x_1568, 9, x_1551);
lean_ctor_set(x_1568, 10, x_1552);
lean_ctor_set(x_1568, 11, x_1553);
lean_ctor_set(x_1568, 12, x_1554);
lean_ctor_set(x_1568, 13, x_1555);
lean_ctor_set(x_1568, 14, x_1556);
lean_ctor_set(x_1568, 15, x_1557);
lean_ctor_set(x_1568, 16, x_1558);
lean_ctor_set(x_1568, 17, x_1559);
lean_ctor_set(x_1568, 18, x_1560);
lean_ctor_set(x_1568, 19, x_1561);
lean_ctor_set(x_1568, 20, x_1562);
lean_ctor_set(x_1568, 21, x_1563);
lean_ctor_set(x_1568, 22, x_1564);
lean_ctor_set(x_1568, 23, x_1565);
lean_ctor_set(x_1568, 24, x_1566);
lean_ctor_set(x_1568, 25, x_1567);
lean_ctor_set_uint8(x_1568, sizeof(void*)*26, x_1548);
x_1569 = lean_st_ref_set(x_13, x_1568, x_1535);
lean_dec(x_13);
x_1570 = !lean_is_exclusive(x_1569);
if (x_1570 == 0)
{
lean_object* x_1571; 
x_1571 = lean_ctor_get(x_1569, 0);
lean_dec(x_1571);
lean_ctor_set(x_1569, 0, x_1532);
return x_1569;
}
else
{
lean_object* x_1572; lean_object* x_1573; 
x_1572 = lean_ctor_get(x_1569, 1);
lean_inc(x_1572);
lean_dec(x_1569);
x_1573 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1573, 0, x_1532);
lean_ctor_set(x_1573, 1, x_1572);
return x_1573;
}
}
else
{
lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; lean_object* x_1588; uint8_t x_1589; lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; uint8_t x_1611; 
lean_dec(x_10);
lean_dec(x_9);
x_1574 = lean_st_ref_take(x_13, x_1523);
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
x_1582 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1581, x_1518, x_1);
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
x_1589 = lean_ctor_get_uint8(x_1575, sizeof(void*)*26);
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
x_1598 = lean_ctor_get(x_1575, 15);
lean_inc(x_1598);
x_1599 = lean_ctor_get(x_1575, 16);
lean_inc(x_1599);
x_1600 = lean_ctor_get(x_1575, 17);
lean_inc(x_1600);
x_1601 = lean_ctor_get(x_1575, 18);
lean_inc(x_1601);
x_1602 = lean_ctor_get(x_1575, 19);
lean_inc(x_1602);
x_1603 = lean_ctor_get(x_1575, 20);
lean_inc(x_1603);
x_1604 = lean_ctor_get(x_1575, 21);
lean_inc(x_1604);
x_1605 = lean_ctor_get(x_1575, 22);
lean_inc(x_1605);
x_1606 = lean_ctor_get(x_1575, 23);
lean_inc(x_1606);
x_1607 = lean_ctor_get(x_1575, 24);
lean_inc(x_1607);
x_1608 = lean_ctor_get(x_1575, 25);
lean_inc(x_1608);
lean_dec(x_1575);
x_1609 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_1609, 0, x_1577);
lean_ctor_set(x_1609, 1, x_1583);
lean_ctor_set(x_1609, 2, x_1584);
lean_ctor_set(x_1609, 3, x_1585);
lean_ctor_set(x_1609, 4, x_1586);
lean_ctor_set(x_1609, 5, x_1587);
lean_ctor_set(x_1609, 6, x_1588);
lean_ctor_set(x_1609, 7, x_1590);
lean_ctor_set(x_1609, 8, x_1591);
lean_ctor_set(x_1609, 9, x_1592);
lean_ctor_set(x_1609, 10, x_1593);
lean_ctor_set(x_1609, 11, x_1594);
lean_ctor_set(x_1609, 12, x_1595);
lean_ctor_set(x_1609, 13, x_1596);
lean_ctor_set(x_1609, 14, x_1597);
lean_ctor_set(x_1609, 15, x_1598);
lean_ctor_set(x_1609, 16, x_1599);
lean_ctor_set(x_1609, 17, x_1600);
lean_ctor_set(x_1609, 18, x_1601);
lean_ctor_set(x_1609, 19, x_1602);
lean_ctor_set(x_1609, 20, x_1603);
lean_ctor_set(x_1609, 21, x_1604);
lean_ctor_set(x_1609, 22, x_1605);
lean_ctor_set(x_1609, 23, x_1606);
lean_ctor_set(x_1609, 24, x_1607);
lean_ctor_set(x_1609, 25, x_1608);
lean_ctor_set_uint8(x_1609, sizeof(void*)*26, x_1589);
x_1610 = lean_st_ref_set(x_13, x_1609, x_1576);
lean_dec(x_13);
x_1611 = !lean_is_exclusive(x_1610);
if (x_1611 == 0)
{
lean_object* x_1612; 
x_1612 = lean_ctor_get(x_1610, 0);
lean_dec(x_1612);
lean_ctor_set(x_1610, 0, x_1);
return x_1610;
}
else
{
lean_object* x_1613; lean_object* x_1614; 
x_1613 = lean_ctor_get(x_1610, 1);
lean_inc(x_1613);
lean_dec(x_1610);
x_1614 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1614, 0, x_1);
lean_ctor_set(x_1614, 1, x_1613);
return x_1614;
}
}
}
else
{
lean_object* x_1615; 
lean_dec(x_1518);
lean_dec(x_1516);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_1615 = lean_ctor_get(x_1526, 0);
lean_inc(x_1615);
lean_dec(x_1526);
lean_ctor_set(x_1520, 0, x_1615);
return x_1520;
}
}
else
{
lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; 
x_1616 = lean_ctor_get(x_1520, 0);
x_1617 = lean_ctor_get(x_1520, 1);
lean_inc(x_1617);
lean_inc(x_1616);
lean_dec(x_1520);
x_1618 = lean_ctor_get(x_1616, 1);
lean_inc(x_1618);
lean_dec(x_1616);
x_1619 = lean_ctor_get(x_1618, 2);
lean_inc(x_1619);
lean_dec(x_1618);
x_1620 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_1619, x_1518);
if (lean_obj_tag(x_1620) == 0)
{
size_t x_1621; size_t x_1622; uint8_t x_1623; 
x_1621 = lean_ptr_addr(x_1516);
lean_dec(x_1516);
x_1622 = lean_ptr_addr(x_1518);
x_1623 = lean_usize_dec_eq(x_1621, x_1622);
if (x_1623 == 0)
{
lean_object* x_1624; lean_object* x_1625; lean_object* x_1626; lean_object* x_1627; lean_object* x_1628; lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; uint8_t x_1642; lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; lean_object* x_1646; lean_object* x_1647; lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; lean_object* x_1656; lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; lean_object* x_1665; lean_object* x_1666; 
lean_dec(x_1);
x_1624 = lean_unsigned_to_nat(0u);
lean_inc(x_1518);
x_1625 = lean_array_set(x_10, x_1624, x_1518);
x_1626 = l_Lean_mkAppN(x_9, x_1625);
lean_dec(x_1625);
x_1627 = lean_st_ref_take(x_13, x_1617);
x_1628 = lean_ctor_get(x_1627, 0);
lean_inc(x_1628);
x_1629 = lean_ctor_get(x_1627, 1);
lean_inc(x_1629);
lean_dec(x_1627);
x_1630 = lean_ctor_get(x_1628, 0);
lean_inc(x_1630);
x_1631 = lean_ctor_get(x_1628, 1);
lean_inc(x_1631);
x_1632 = lean_ctor_get(x_1631, 0);
lean_inc(x_1632);
x_1633 = lean_ctor_get(x_1631, 1);
lean_inc(x_1633);
x_1634 = lean_ctor_get(x_1631, 2);
lean_inc(x_1634);
lean_dec(x_1631);
lean_inc(x_1626);
x_1635 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1634, x_1518, x_1626);
x_1636 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1636, 0, x_1632);
lean_ctor_set(x_1636, 1, x_1633);
lean_ctor_set(x_1636, 2, x_1635);
x_1637 = lean_ctor_get(x_1628, 2);
lean_inc(x_1637);
x_1638 = lean_ctor_get(x_1628, 3);
lean_inc(x_1638);
x_1639 = lean_ctor_get(x_1628, 4);
lean_inc(x_1639);
x_1640 = lean_ctor_get(x_1628, 5);
lean_inc(x_1640);
x_1641 = lean_ctor_get(x_1628, 6);
lean_inc(x_1641);
x_1642 = lean_ctor_get_uint8(x_1628, sizeof(void*)*26);
x_1643 = lean_ctor_get(x_1628, 7);
lean_inc(x_1643);
x_1644 = lean_ctor_get(x_1628, 8);
lean_inc(x_1644);
x_1645 = lean_ctor_get(x_1628, 9);
lean_inc(x_1645);
x_1646 = lean_ctor_get(x_1628, 10);
lean_inc(x_1646);
x_1647 = lean_ctor_get(x_1628, 11);
lean_inc(x_1647);
x_1648 = lean_ctor_get(x_1628, 12);
lean_inc(x_1648);
x_1649 = lean_ctor_get(x_1628, 13);
lean_inc(x_1649);
x_1650 = lean_ctor_get(x_1628, 14);
lean_inc(x_1650);
x_1651 = lean_ctor_get(x_1628, 15);
lean_inc(x_1651);
x_1652 = lean_ctor_get(x_1628, 16);
lean_inc(x_1652);
x_1653 = lean_ctor_get(x_1628, 17);
lean_inc(x_1653);
x_1654 = lean_ctor_get(x_1628, 18);
lean_inc(x_1654);
x_1655 = lean_ctor_get(x_1628, 19);
lean_inc(x_1655);
x_1656 = lean_ctor_get(x_1628, 20);
lean_inc(x_1656);
x_1657 = lean_ctor_get(x_1628, 21);
lean_inc(x_1657);
x_1658 = lean_ctor_get(x_1628, 22);
lean_inc(x_1658);
x_1659 = lean_ctor_get(x_1628, 23);
lean_inc(x_1659);
x_1660 = lean_ctor_get(x_1628, 24);
lean_inc(x_1660);
x_1661 = lean_ctor_get(x_1628, 25);
lean_inc(x_1661);
lean_dec(x_1628);
x_1662 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_1662, 0, x_1630);
lean_ctor_set(x_1662, 1, x_1636);
lean_ctor_set(x_1662, 2, x_1637);
lean_ctor_set(x_1662, 3, x_1638);
lean_ctor_set(x_1662, 4, x_1639);
lean_ctor_set(x_1662, 5, x_1640);
lean_ctor_set(x_1662, 6, x_1641);
lean_ctor_set(x_1662, 7, x_1643);
lean_ctor_set(x_1662, 8, x_1644);
lean_ctor_set(x_1662, 9, x_1645);
lean_ctor_set(x_1662, 10, x_1646);
lean_ctor_set(x_1662, 11, x_1647);
lean_ctor_set(x_1662, 12, x_1648);
lean_ctor_set(x_1662, 13, x_1649);
lean_ctor_set(x_1662, 14, x_1650);
lean_ctor_set(x_1662, 15, x_1651);
lean_ctor_set(x_1662, 16, x_1652);
lean_ctor_set(x_1662, 17, x_1653);
lean_ctor_set(x_1662, 18, x_1654);
lean_ctor_set(x_1662, 19, x_1655);
lean_ctor_set(x_1662, 20, x_1656);
lean_ctor_set(x_1662, 21, x_1657);
lean_ctor_set(x_1662, 22, x_1658);
lean_ctor_set(x_1662, 23, x_1659);
lean_ctor_set(x_1662, 24, x_1660);
lean_ctor_set(x_1662, 25, x_1661);
lean_ctor_set_uint8(x_1662, sizeof(void*)*26, x_1642);
x_1663 = lean_st_ref_set(x_13, x_1662, x_1629);
lean_dec(x_13);
x_1664 = lean_ctor_get(x_1663, 1);
lean_inc(x_1664);
if (lean_is_exclusive(x_1663)) {
 lean_ctor_release(x_1663, 0);
 lean_ctor_release(x_1663, 1);
 x_1665 = x_1663;
} else {
 lean_dec_ref(x_1663);
 x_1665 = lean_box(0);
}
if (lean_is_scalar(x_1665)) {
 x_1666 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1666 = x_1665;
}
lean_ctor_set(x_1666, 0, x_1626);
lean_ctor_set(x_1666, 1, x_1664);
return x_1666;
}
else
{
lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; lean_object* x_1677; lean_object* x_1678; lean_object* x_1679; lean_object* x_1680; lean_object* x_1681; uint8_t x_1682; lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; lean_object* x_1690; lean_object* x_1691; lean_object* x_1692; lean_object* x_1693; lean_object* x_1694; lean_object* x_1695; lean_object* x_1696; lean_object* x_1697; lean_object* x_1698; lean_object* x_1699; lean_object* x_1700; lean_object* x_1701; lean_object* x_1702; lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; lean_object* x_1706; 
lean_dec(x_10);
lean_dec(x_9);
x_1667 = lean_st_ref_take(x_13, x_1617);
x_1668 = lean_ctor_get(x_1667, 0);
lean_inc(x_1668);
x_1669 = lean_ctor_get(x_1667, 1);
lean_inc(x_1669);
lean_dec(x_1667);
x_1670 = lean_ctor_get(x_1668, 0);
lean_inc(x_1670);
x_1671 = lean_ctor_get(x_1668, 1);
lean_inc(x_1671);
x_1672 = lean_ctor_get(x_1671, 0);
lean_inc(x_1672);
x_1673 = lean_ctor_get(x_1671, 1);
lean_inc(x_1673);
x_1674 = lean_ctor_get(x_1671, 2);
lean_inc(x_1674);
lean_dec(x_1671);
lean_inc(x_1);
x_1675 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1674, x_1518, x_1);
x_1676 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1676, 0, x_1672);
lean_ctor_set(x_1676, 1, x_1673);
lean_ctor_set(x_1676, 2, x_1675);
x_1677 = lean_ctor_get(x_1668, 2);
lean_inc(x_1677);
x_1678 = lean_ctor_get(x_1668, 3);
lean_inc(x_1678);
x_1679 = lean_ctor_get(x_1668, 4);
lean_inc(x_1679);
x_1680 = lean_ctor_get(x_1668, 5);
lean_inc(x_1680);
x_1681 = lean_ctor_get(x_1668, 6);
lean_inc(x_1681);
x_1682 = lean_ctor_get_uint8(x_1668, sizeof(void*)*26);
x_1683 = lean_ctor_get(x_1668, 7);
lean_inc(x_1683);
x_1684 = lean_ctor_get(x_1668, 8);
lean_inc(x_1684);
x_1685 = lean_ctor_get(x_1668, 9);
lean_inc(x_1685);
x_1686 = lean_ctor_get(x_1668, 10);
lean_inc(x_1686);
x_1687 = lean_ctor_get(x_1668, 11);
lean_inc(x_1687);
x_1688 = lean_ctor_get(x_1668, 12);
lean_inc(x_1688);
x_1689 = lean_ctor_get(x_1668, 13);
lean_inc(x_1689);
x_1690 = lean_ctor_get(x_1668, 14);
lean_inc(x_1690);
x_1691 = lean_ctor_get(x_1668, 15);
lean_inc(x_1691);
x_1692 = lean_ctor_get(x_1668, 16);
lean_inc(x_1692);
x_1693 = lean_ctor_get(x_1668, 17);
lean_inc(x_1693);
x_1694 = lean_ctor_get(x_1668, 18);
lean_inc(x_1694);
x_1695 = lean_ctor_get(x_1668, 19);
lean_inc(x_1695);
x_1696 = lean_ctor_get(x_1668, 20);
lean_inc(x_1696);
x_1697 = lean_ctor_get(x_1668, 21);
lean_inc(x_1697);
x_1698 = lean_ctor_get(x_1668, 22);
lean_inc(x_1698);
x_1699 = lean_ctor_get(x_1668, 23);
lean_inc(x_1699);
x_1700 = lean_ctor_get(x_1668, 24);
lean_inc(x_1700);
x_1701 = lean_ctor_get(x_1668, 25);
lean_inc(x_1701);
lean_dec(x_1668);
x_1702 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_1702, 0, x_1670);
lean_ctor_set(x_1702, 1, x_1676);
lean_ctor_set(x_1702, 2, x_1677);
lean_ctor_set(x_1702, 3, x_1678);
lean_ctor_set(x_1702, 4, x_1679);
lean_ctor_set(x_1702, 5, x_1680);
lean_ctor_set(x_1702, 6, x_1681);
lean_ctor_set(x_1702, 7, x_1683);
lean_ctor_set(x_1702, 8, x_1684);
lean_ctor_set(x_1702, 9, x_1685);
lean_ctor_set(x_1702, 10, x_1686);
lean_ctor_set(x_1702, 11, x_1687);
lean_ctor_set(x_1702, 12, x_1688);
lean_ctor_set(x_1702, 13, x_1689);
lean_ctor_set(x_1702, 14, x_1690);
lean_ctor_set(x_1702, 15, x_1691);
lean_ctor_set(x_1702, 16, x_1692);
lean_ctor_set(x_1702, 17, x_1693);
lean_ctor_set(x_1702, 18, x_1694);
lean_ctor_set(x_1702, 19, x_1695);
lean_ctor_set(x_1702, 20, x_1696);
lean_ctor_set(x_1702, 21, x_1697);
lean_ctor_set(x_1702, 22, x_1698);
lean_ctor_set(x_1702, 23, x_1699);
lean_ctor_set(x_1702, 24, x_1700);
lean_ctor_set(x_1702, 25, x_1701);
lean_ctor_set_uint8(x_1702, sizeof(void*)*26, x_1682);
x_1703 = lean_st_ref_set(x_13, x_1702, x_1669);
lean_dec(x_13);
x_1704 = lean_ctor_get(x_1703, 1);
lean_inc(x_1704);
if (lean_is_exclusive(x_1703)) {
 lean_ctor_release(x_1703, 0);
 lean_ctor_release(x_1703, 1);
 x_1705 = x_1703;
} else {
 lean_dec_ref(x_1703);
 x_1705 = lean_box(0);
}
if (lean_is_scalar(x_1705)) {
 x_1706 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1706 = x_1705;
}
lean_ctor_set(x_1706, 0, x_1);
lean_ctor_set(x_1706, 1, x_1704);
return x_1706;
}
}
else
{
lean_object* x_1707; lean_object* x_1708; 
lean_dec(x_1518);
lean_dec(x_1516);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_1707 = lean_ctor_get(x_1620, 0);
lean_inc(x_1707);
lean_dec(x_1620);
x_1708 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1708, 0, x_1707);
lean_ctor_set(x_1708, 1, x_1617);
return x_1708;
}
}
}
else
{
uint8_t x_1709; 
lean_dec(x_1516);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_1709 = !lean_is_exclusive(x_1517);
if (x_1709 == 0)
{
return x_1517;
}
else
{
lean_object* x_1710; lean_object* x_1711; lean_object* x_1712; 
x_1710 = lean_ctor_get(x_1517, 0);
x_1711 = lean_ctor_get(x_1517, 1);
lean_inc(x_1711);
lean_inc(x_1710);
lean_dec(x_1517);
x_1712 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1712, 0, x_1710);
lean_ctor_set(x_1712, 1, x_1711);
return x_1712;
}
}
}
block_1751:
{
lean_object* x_1715; 
lean_dec(x_1714);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_9);
x_1715 = l_Lean_Meta_getFunInfo(x_9, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_1715) == 0)
{
lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; lean_object* x_1719; lean_object* x_1720; lean_object* x_1721; lean_object* x_1722; uint8_t x_1723; lean_object* x_1724; lean_object* x_1725; lean_object* x_1726; lean_object* x_1727; 
x_1716 = lean_ctor_get(x_1715, 0);
lean_inc(x_1716);
x_1717 = lean_ctor_get(x_1715, 1);
lean_inc(x_1717);
lean_dec(x_1715);
x_1718 = lean_ctor_get(x_1716, 0);
lean_inc(x_1718);
lean_dec(x_1716);
x_1719 = lean_array_get_size(x_10);
x_1720 = lean_unsigned_to_nat(0u);
x_1721 = lean_unsigned_to_nat(1u);
lean_inc(x_1719);
x_1722 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1722, 0, x_1720);
lean_ctor_set(x_1722, 1, x_1719);
lean_ctor_set(x_1722, 2, x_1721);
x_1723 = 0;
x_1724 = lean_box(x_1723);
lean_inc(x_10);
x_1725 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1725, 0, x_10);
lean_ctor_set(x_1725, 1, x_1724);
x_1726 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_1722);
lean_inc(x_9);
lean_inc(x_1);
x_1727 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1726, x_1718, x_1719, x_1722, x_1722, x_1725, x_1720, lean_box(0), lean_box(0), x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_1717);
if (lean_obj_tag(x_1727) == 0)
{
lean_object* x_1728; lean_object* x_1729; uint8_t x_1730; 
x_1728 = lean_ctor_get(x_1727, 0);
lean_inc(x_1728);
x_1729 = lean_ctor_get(x_1728, 1);
lean_inc(x_1729);
x_1730 = lean_unbox(x_1729);
lean_dec(x_1729);
if (x_1730 == 0)
{
uint8_t x_1731; 
lean_dec(x_1728);
lean_dec(x_9);
x_1731 = !lean_is_exclusive(x_1727);
if (x_1731 == 0)
{
lean_object* x_1732; 
x_1732 = lean_ctor_get(x_1727, 0);
lean_dec(x_1732);
lean_ctor_set(x_1727, 0, x_1);
return x_1727;
}
else
{
lean_object* x_1733; lean_object* x_1734; 
x_1733 = lean_ctor_get(x_1727, 1);
lean_inc(x_1733);
lean_dec(x_1727);
x_1734 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1734, 0, x_1);
lean_ctor_set(x_1734, 1, x_1733);
return x_1734;
}
}
else
{
uint8_t x_1735; 
lean_dec(x_1);
x_1735 = !lean_is_exclusive(x_1727);
if (x_1735 == 0)
{
lean_object* x_1736; lean_object* x_1737; lean_object* x_1738; 
x_1736 = lean_ctor_get(x_1727, 0);
lean_dec(x_1736);
x_1737 = lean_ctor_get(x_1728, 0);
lean_inc(x_1737);
lean_dec(x_1728);
x_1738 = l_Lean_mkAppN(x_9, x_1737);
lean_dec(x_1737);
lean_ctor_set(x_1727, 0, x_1738);
return x_1727;
}
else
{
lean_object* x_1739; lean_object* x_1740; lean_object* x_1741; lean_object* x_1742; 
x_1739 = lean_ctor_get(x_1727, 1);
lean_inc(x_1739);
lean_dec(x_1727);
x_1740 = lean_ctor_get(x_1728, 0);
lean_inc(x_1740);
lean_dec(x_1728);
x_1741 = l_Lean_mkAppN(x_9, x_1740);
lean_dec(x_1740);
x_1742 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1742, 0, x_1741);
lean_ctor_set(x_1742, 1, x_1739);
return x_1742;
}
}
}
else
{
uint8_t x_1743; 
lean_dec(x_9);
lean_dec(x_1);
x_1743 = !lean_is_exclusive(x_1727);
if (x_1743 == 0)
{
return x_1727;
}
else
{
lean_object* x_1744; lean_object* x_1745; lean_object* x_1746; 
x_1744 = lean_ctor_get(x_1727, 0);
x_1745 = lean_ctor_get(x_1727, 1);
lean_inc(x_1745);
lean_inc(x_1744);
lean_dec(x_1727);
x_1746 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1746, 0, x_1744);
lean_ctor_set(x_1746, 1, x_1745);
return x_1746;
}
}
}
else
{
uint8_t x_1747; 
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
x_1747 = !lean_is_exclusive(x_1715);
if (x_1747 == 0)
{
return x_1715;
}
else
{
lean_object* x_1748; lean_object* x_1749; lean_object* x_1750; 
x_1748 = lean_ctor_get(x_1715, 0);
x_1749 = lean_ctor_get(x_1715, 1);
lean_inc(x_1749);
lean_inc(x_1748);
lean_dec(x_1715);
x_1750 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1750, 0, x_1748);
lean_ctor_set(x_1750, 1, x_1749);
return x_1750;
}
}
}
}
case 8:
{
lean_object* x_1764; lean_object* x_1962; lean_object* x_2000; uint8_t x_2001; 
lean_dec(x_11);
x_2000 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_2001 = l_Lean_Expr_isConstOf(x_9, x_2000);
if (x_2001 == 0)
{
lean_object* x_2002; 
x_2002 = lean_box(0);
x_1962 = x_2002;
goto block_1999;
}
else
{
lean_object* x_2003; lean_object* x_2004; uint8_t x_2005; 
x_2003 = lean_array_get_size(x_10);
x_2004 = lean_unsigned_to_nat(2u);
x_2005 = lean_nat_dec_eq(x_2003, x_2004);
if (x_2005 == 0)
{
lean_object* x_2006; 
lean_dec(x_2003);
x_2006 = lean_box(0);
x_1962 = x_2006;
goto block_1999;
}
else
{
lean_object* x_2007; uint8_t x_2008; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2007 = lean_unsigned_to_nat(0u);
x_2008 = lean_nat_dec_lt(x_2007, x_2003);
lean_dec(x_2003);
if (x_2008 == 0)
{
lean_object* x_2009; lean_object* x_2010; 
x_2009 = l_Lean_instInhabitedExpr;
x_2010 = l_outOfBounds___rarg(x_2009);
x_1764 = x_2010;
goto block_1961;
}
else
{
lean_object* x_2011; 
x_2011 = lean_array_fget(x_10, x_2007);
x_1764 = x_2011;
goto block_1961;
}
}
}
block_1961:
{
lean_object* x_1765; 
lean_inc(x_13);
lean_inc(x_1764);
x_1765 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_1764, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_1765) == 0)
{
lean_object* x_1766; lean_object* x_1767; lean_object* x_1768; uint8_t x_1769; 
x_1766 = lean_ctor_get(x_1765, 0);
lean_inc(x_1766);
x_1767 = lean_ctor_get(x_1765, 1);
lean_inc(x_1767);
lean_dec(x_1765);
x_1768 = lean_st_ref_get(x_13, x_1767);
x_1769 = !lean_is_exclusive(x_1768);
if (x_1769 == 0)
{
lean_object* x_1770; lean_object* x_1771; lean_object* x_1772; lean_object* x_1773; lean_object* x_1774; 
x_1770 = lean_ctor_get(x_1768, 0);
x_1771 = lean_ctor_get(x_1768, 1);
x_1772 = lean_ctor_get(x_1770, 1);
lean_inc(x_1772);
lean_dec(x_1770);
x_1773 = lean_ctor_get(x_1772, 2);
lean_inc(x_1773);
lean_dec(x_1772);
x_1774 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_1773, x_1766);
if (lean_obj_tag(x_1774) == 0)
{
size_t x_1775; size_t x_1776; uint8_t x_1777; 
lean_free_object(x_1768);
x_1775 = lean_ptr_addr(x_1764);
lean_dec(x_1764);
x_1776 = lean_ptr_addr(x_1766);
x_1777 = lean_usize_dec_eq(x_1775, x_1776);
if (x_1777 == 0)
{
lean_object* x_1778; lean_object* x_1779; lean_object* x_1780; lean_object* x_1781; lean_object* x_1782; lean_object* x_1783; lean_object* x_1784; lean_object* x_1785; lean_object* x_1786; lean_object* x_1787; lean_object* x_1788; lean_object* x_1789; lean_object* x_1790; lean_object* x_1791; lean_object* x_1792; lean_object* x_1793; lean_object* x_1794; lean_object* x_1795; uint8_t x_1796; lean_object* x_1797; lean_object* x_1798; lean_object* x_1799; lean_object* x_1800; lean_object* x_1801; lean_object* x_1802; lean_object* x_1803; lean_object* x_1804; lean_object* x_1805; lean_object* x_1806; lean_object* x_1807; lean_object* x_1808; lean_object* x_1809; lean_object* x_1810; lean_object* x_1811; lean_object* x_1812; lean_object* x_1813; lean_object* x_1814; lean_object* x_1815; lean_object* x_1816; lean_object* x_1817; uint8_t x_1818; 
lean_dec(x_1);
x_1778 = lean_unsigned_to_nat(0u);
lean_inc(x_1766);
x_1779 = lean_array_set(x_10, x_1778, x_1766);
x_1780 = l_Lean_mkAppN(x_9, x_1779);
lean_dec(x_1779);
x_1781 = lean_st_ref_take(x_13, x_1771);
x_1782 = lean_ctor_get(x_1781, 0);
lean_inc(x_1782);
x_1783 = lean_ctor_get(x_1781, 1);
lean_inc(x_1783);
lean_dec(x_1781);
x_1784 = lean_ctor_get(x_1782, 0);
lean_inc(x_1784);
x_1785 = lean_ctor_get(x_1782, 1);
lean_inc(x_1785);
x_1786 = lean_ctor_get(x_1785, 0);
lean_inc(x_1786);
x_1787 = lean_ctor_get(x_1785, 1);
lean_inc(x_1787);
x_1788 = lean_ctor_get(x_1785, 2);
lean_inc(x_1788);
lean_dec(x_1785);
lean_inc(x_1780);
x_1789 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1788, x_1766, x_1780);
x_1790 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1790, 0, x_1786);
lean_ctor_set(x_1790, 1, x_1787);
lean_ctor_set(x_1790, 2, x_1789);
x_1791 = lean_ctor_get(x_1782, 2);
lean_inc(x_1791);
x_1792 = lean_ctor_get(x_1782, 3);
lean_inc(x_1792);
x_1793 = lean_ctor_get(x_1782, 4);
lean_inc(x_1793);
x_1794 = lean_ctor_get(x_1782, 5);
lean_inc(x_1794);
x_1795 = lean_ctor_get(x_1782, 6);
lean_inc(x_1795);
x_1796 = lean_ctor_get_uint8(x_1782, sizeof(void*)*26);
x_1797 = lean_ctor_get(x_1782, 7);
lean_inc(x_1797);
x_1798 = lean_ctor_get(x_1782, 8);
lean_inc(x_1798);
x_1799 = lean_ctor_get(x_1782, 9);
lean_inc(x_1799);
x_1800 = lean_ctor_get(x_1782, 10);
lean_inc(x_1800);
x_1801 = lean_ctor_get(x_1782, 11);
lean_inc(x_1801);
x_1802 = lean_ctor_get(x_1782, 12);
lean_inc(x_1802);
x_1803 = lean_ctor_get(x_1782, 13);
lean_inc(x_1803);
x_1804 = lean_ctor_get(x_1782, 14);
lean_inc(x_1804);
x_1805 = lean_ctor_get(x_1782, 15);
lean_inc(x_1805);
x_1806 = lean_ctor_get(x_1782, 16);
lean_inc(x_1806);
x_1807 = lean_ctor_get(x_1782, 17);
lean_inc(x_1807);
x_1808 = lean_ctor_get(x_1782, 18);
lean_inc(x_1808);
x_1809 = lean_ctor_get(x_1782, 19);
lean_inc(x_1809);
x_1810 = lean_ctor_get(x_1782, 20);
lean_inc(x_1810);
x_1811 = lean_ctor_get(x_1782, 21);
lean_inc(x_1811);
x_1812 = lean_ctor_get(x_1782, 22);
lean_inc(x_1812);
x_1813 = lean_ctor_get(x_1782, 23);
lean_inc(x_1813);
x_1814 = lean_ctor_get(x_1782, 24);
lean_inc(x_1814);
x_1815 = lean_ctor_get(x_1782, 25);
lean_inc(x_1815);
lean_dec(x_1782);
x_1816 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_1816, 0, x_1784);
lean_ctor_set(x_1816, 1, x_1790);
lean_ctor_set(x_1816, 2, x_1791);
lean_ctor_set(x_1816, 3, x_1792);
lean_ctor_set(x_1816, 4, x_1793);
lean_ctor_set(x_1816, 5, x_1794);
lean_ctor_set(x_1816, 6, x_1795);
lean_ctor_set(x_1816, 7, x_1797);
lean_ctor_set(x_1816, 8, x_1798);
lean_ctor_set(x_1816, 9, x_1799);
lean_ctor_set(x_1816, 10, x_1800);
lean_ctor_set(x_1816, 11, x_1801);
lean_ctor_set(x_1816, 12, x_1802);
lean_ctor_set(x_1816, 13, x_1803);
lean_ctor_set(x_1816, 14, x_1804);
lean_ctor_set(x_1816, 15, x_1805);
lean_ctor_set(x_1816, 16, x_1806);
lean_ctor_set(x_1816, 17, x_1807);
lean_ctor_set(x_1816, 18, x_1808);
lean_ctor_set(x_1816, 19, x_1809);
lean_ctor_set(x_1816, 20, x_1810);
lean_ctor_set(x_1816, 21, x_1811);
lean_ctor_set(x_1816, 22, x_1812);
lean_ctor_set(x_1816, 23, x_1813);
lean_ctor_set(x_1816, 24, x_1814);
lean_ctor_set(x_1816, 25, x_1815);
lean_ctor_set_uint8(x_1816, sizeof(void*)*26, x_1796);
x_1817 = lean_st_ref_set(x_13, x_1816, x_1783);
lean_dec(x_13);
x_1818 = !lean_is_exclusive(x_1817);
if (x_1818 == 0)
{
lean_object* x_1819; 
x_1819 = lean_ctor_get(x_1817, 0);
lean_dec(x_1819);
lean_ctor_set(x_1817, 0, x_1780);
return x_1817;
}
else
{
lean_object* x_1820; lean_object* x_1821; 
x_1820 = lean_ctor_get(x_1817, 1);
lean_inc(x_1820);
lean_dec(x_1817);
x_1821 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1821, 0, x_1780);
lean_ctor_set(x_1821, 1, x_1820);
return x_1821;
}
}
else
{
lean_object* x_1822; lean_object* x_1823; lean_object* x_1824; lean_object* x_1825; lean_object* x_1826; lean_object* x_1827; lean_object* x_1828; lean_object* x_1829; lean_object* x_1830; lean_object* x_1831; lean_object* x_1832; lean_object* x_1833; lean_object* x_1834; lean_object* x_1835; lean_object* x_1836; uint8_t x_1837; lean_object* x_1838; lean_object* x_1839; lean_object* x_1840; lean_object* x_1841; lean_object* x_1842; lean_object* x_1843; lean_object* x_1844; lean_object* x_1845; lean_object* x_1846; lean_object* x_1847; lean_object* x_1848; lean_object* x_1849; lean_object* x_1850; lean_object* x_1851; lean_object* x_1852; lean_object* x_1853; lean_object* x_1854; lean_object* x_1855; lean_object* x_1856; lean_object* x_1857; lean_object* x_1858; uint8_t x_1859; 
lean_dec(x_10);
lean_dec(x_9);
x_1822 = lean_st_ref_take(x_13, x_1771);
x_1823 = lean_ctor_get(x_1822, 0);
lean_inc(x_1823);
x_1824 = lean_ctor_get(x_1822, 1);
lean_inc(x_1824);
lean_dec(x_1822);
x_1825 = lean_ctor_get(x_1823, 0);
lean_inc(x_1825);
x_1826 = lean_ctor_get(x_1823, 1);
lean_inc(x_1826);
x_1827 = lean_ctor_get(x_1826, 0);
lean_inc(x_1827);
x_1828 = lean_ctor_get(x_1826, 1);
lean_inc(x_1828);
x_1829 = lean_ctor_get(x_1826, 2);
lean_inc(x_1829);
lean_dec(x_1826);
lean_inc(x_1);
x_1830 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1829, x_1766, x_1);
x_1831 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1831, 0, x_1827);
lean_ctor_set(x_1831, 1, x_1828);
lean_ctor_set(x_1831, 2, x_1830);
x_1832 = lean_ctor_get(x_1823, 2);
lean_inc(x_1832);
x_1833 = lean_ctor_get(x_1823, 3);
lean_inc(x_1833);
x_1834 = lean_ctor_get(x_1823, 4);
lean_inc(x_1834);
x_1835 = lean_ctor_get(x_1823, 5);
lean_inc(x_1835);
x_1836 = lean_ctor_get(x_1823, 6);
lean_inc(x_1836);
x_1837 = lean_ctor_get_uint8(x_1823, sizeof(void*)*26);
x_1838 = lean_ctor_get(x_1823, 7);
lean_inc(x_1838);
x_1839 = lean_ctor_get(x_1823, 8);
lean_inc(x_1839);
x_1840 = lean_ctor_get(x_1823, 9);
lean_inc(x_1840);
x_1841 = lean_ctor_get(x_1823, 10);
lean_inc(x_1841);
x_1842 = lean_ctor_get(x_1823, 11);
lean_inc(x_1842);
x_1843 = lean_ctor_get(x_1823, 12);
lean_inc(x_1843);
x_1844 = lean_ctor_get(x_1823, 13);
lean_inc(x_1844);
x_1845 = lean_ctor_get(x_1823, 14);
lean_inc(x_1845);
x_1846 = lean_ctor_get(x_1823, 15);
lean_inc(x_1846);
x_1847 = lean_ctor_get(x_1823, 16);
lean_inc(x_1847);
x_1848 = lean_ctor_get(x_1823, 17);
lean_inc(x_1848);
x_1849 = lean_ctor_get(x_1823, 18);
lean_inc(x_1849);
x_1850 = lean_ctor_get(x_1823, 19);
lean_inc(x_1850);
x_1851 = lean_ctor_get(x_1823, 20);
lean_inc(x_1851);
x_1852 = lean_ctor_get(x_1823, 21);
lean_inc(x_1852);
x_1853 = lean_ctor_get(x_1823, 22);
lean_inc(x_1853);
x_1854 = lean_ctor_get(x_1823, 23);
lean_inc(x_1854);
x_1855 = lean_ctor_get(x_1823, 24);
lean_inc(x_1855);
x_1856 = lean_ctor_get(x_1823, 25);
lean_inc(x_1856);
lean_dec(x_1823);
x_1857 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_1857, 0, x_1825);
lean_ctor_set(x_1857, 1, x_1831);
lean_ctor_set(x_1857, 2, x_1832);
lean_ctor_set(x_1857, 3, x_1833);
lean_ctor_set(x_1857, 4, x_1834);
lean_ctor_set(x_1857, 5, x_1835);
lean_ctor_set(x_1857, 6, x_1836);
lean_ctor_set(x_1857, 7, x_1838);
lean_ctor_set(x_1857, 8, x_1839);
lean_ctor_set(x_1857, 9, x_1840);
lean_ctor_set(x_1857, 10, x_1841);
lean_ctor_set(x_1857, 11, x_1842);
lean_ctor_set(x_1857, 12, x_1843);
lean_ctor_set(x_1857, 13, x_1844);
lean_ctor_set(x_1857, 14, x_1845);
lean_ctor_set(x_1857, 15, x_1846);
lean_ctor_set(x_1857, 16, x_1847);
lean_ctor_set(x_1857, 17, x_1848);
lean_ctor_set(x_1857, 18, x_1849);
lean_ctor_set(x_1857, 19, x_1850);
lean_ctor_set(x_1857, 20, x_1851);
lean_ctor_set(x_1857, 21, x_1852);
lean_ctor_set(x_1857, 22, x_1853);
lean_ctor_set(x_1857, 23, x_1854);
lean_ctor_set(x_1857, 24, x_1855);
lean_ctor_set(x_1857, 25, x_1856);
lean_ctor_set_uint8(x_1857, sizeof(void*)*26, x_1837);
x_1858 = lean_st_ref_set(x_13, x_1857, x_1824);
lean_dec(x_13);
x_1859 = !lean_is_exclusive(x_1858);
if (x_1859 == 0)
{
lean_object* x_1860; 
x_1860 = lean_ctor_get(x_1858, 0);
lean_dec(x_1860);
lean_ctor_set(x_1858, 0, x_1);
return x_1858;
}
else
{
lean_object* x_1861; lean_object* x_1862; 
x_1861 = lean_ctor_get(x_1858, 1);
lean_inc(x_1861);
lean_dec(x_1858);
x_1862 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1862, 0, x_1);
lean_ctor_set(x_1862, 1, x_1861);
return x_1862;
}
}
}
else
{
lean_object* x_1863; 
lean_dec(x_1766);
lean_dec(x_1764);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_1863 = lean_ctor_get(x_1774, 0);
lean_inc(x_1863);
lean_dec(x_1774);
lean_ctor_set(x_1768, 0, x_1863);
return x_1768;
}
}
else
{
lean_object* x_1864; lean_object* x_1865; lean_object* x_1866; lean_object* x_1867; lean_object* x_1868; 
x_1864 = lean_ctor_get(x_1768, 0);
x_1865 = lean_ctor_get(x_1768, 1);
lean_inc(x_1865);
lean_inc(x_1864);
lean_dec(x_1768);
x_1866 = lean_ctor_get(x_1864, 1);
lean_inc(x_1866);
lean_dec(x_1864);
x_1867 = lean_ctor_get(x_1866, 2);
lean_inc(x_1867);
lean_dec(x_1866);
x_1868 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_1867, x_1766);
if (lean_obj_tag(x_1868) == 0)
{
size_t x_1869; size_t x_1870; uint8_t x_1871; 
x_1869 = lean_ptr_addr(x_1764);
lean_dec(x_1764);
x_1870 = lean_ptr_addr(x_1766);
x_1871 = lean_usize_dec_eq(x_1869, x_1870);
if (x_1871 == 0)
{
lean_object* x_1872; lean_object* x_1873; lean_object* x_1874; lean_object* x_1875; lean_object* x_1876; lean_object* x_1877; lean_object* x_1878; lean_object* x_1879; lean_object* x_1880; lean_object* x_1881; lean_object* x_1882; lean_object* x_1883; lean_object* x_1884; lean_object* x_1885; lean_object* x_1886; lean_object* x_1887; lean_object* x_1888; lean_object* x_1889; uint8_t x_1890; lean_object* x_1891; lean_object* x_1892; lean_object* x_1893; lean_object* x_1894; lean_object* x_1895; lean_object* x_1896; lean_object* x_1897; lean_object* x_1898; lean_object* x_1899; lean_object* x_1900; lean_object* x_1901; lean_object* x_1902; lean_object* x_1903; lean_object* x_1904; lean_object* x_1905; lean_object* x_1906; lean_object* x_1907; lean_object* x_1908; lean_object* x_1909; lean_object* x_1910; lean_object* x_1911; lean_object* x_1912; lean_object* x_1913; lean_object* x_1914; 
lean_dec(x_1);
x_1872 = lean_unsigned_to_nat(0u);
lean_inc(x_1766);
x_1873 = lean_array_set(x_10, x_1872, x_1766);
x_1874 = l_Lean_mkAppN(x_9, x_1873);
lean_dec(x_1873);
x_1875 = lean_st_ref_take(x_13, x_1865);
x_1876 = lean_ctor_get(x_1875, 0);
lean_inc(x_1876);
x_1877 = lean_ctor_get(x_1875, 1);
lean_inc(x_1877);
lean_dec(x_1875);
x_1878 = lean_ctor_get(x_1876, 0);
lean_inc(x_1878);
x_1879 = lean_ctor_get(x_1876, 1);
lean_inc(x_1879);
x_1880 = lean_ctor_get(x_1879, 0);
lean_inc(x_1880);
x_1881 = lean_ctor_get(x_1879, 1);
lean_inc(x_1881);
x_1882 = lean_ctor_get(x_1879, 2);
lean_inc(x_1882);
lean_dec(x_1879);
lean_inc(x_1874);
x_1883 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1882, x_1766, x_1874);
x_1884 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1884, 0, x_1880);
lean_ctor_set(x_1884, 1, x_1881);
lean_ctor_set(x_1884, 2, x_1883);
x_1885 = lean_ctor_get(x_1876, 2);
lean_inc(x_1885);
x_1886 = lean_ctor_get(x_1876, 3);
lean_inc(x_1886);
x_1887 = lean_ctor_get(x_1876, 4);
lean_inc(x_1887);
x_1888 = lean_ctor_get(x_1876, 5);
lean_inc(x_1888);
x_1889 = lean_ctor_get(x_1876, 6);
lean_inc(x_1889);
x_1890 = lean_ctor_get_uint8(x_1876, sizeof(void*)*26);
x_1891 = lean_ctor_get(x_1876, 7);
lean_inc(x_1891);
x_1892 = lean_ctor_get(x_1876, 8);
lean_inc(x_1892);
x_1893 = lean_ctor_get(x_1876, 9);
lean_inc(x_1893);
x_1894 = lean_ctor_get(x_1876, 10);
lean_inc(x_1894);
x_1895 = lean_ctor_get(x_1876, 11);
lean_inc(x_1895);
x_1896 = lean_ctor_get(x_1876, 12);
lean_inc(x_1896);
x_1897 = lean_ctor_get(x_1876, 13);
lean_inc(x_1897);
x_1898 = lean_ctor_get(x_1876, 14);
lean_inc(x_1898);
x_1899 = lean_ctor_get(x_1876, 15);
lean_inc(x_1899);
x_1900 = lean_ctor_get(x_1876, 16);
lean_inc(x_1900);
x_1901 = lean_ctor_get(x_1876, 17);
lean_inc(x_1901);
x_1902 = lean_ctor_get(x_1876, 18);
lean_inc(x_1902);
x_1903 = lean_ctor_get(x_1876, 19);
lean_inc(x_1903);
x_1904 = lean_ctor_get(x_1876, 20);
lean_inc(x_1904);
x_1905 = lean_ctor_get(x_1876, 21);
lean_inc(x_1905);
x_1906 = lean_ctor_get(x_1876, 22);
lean_inc(x_1906);
x_1907 = lean_ctor_get(x_1876, 23);
lean_inc(x_1907);
x_1908 = lean_ctor_get(x_1876, 24);
lean_inc(x_1908);
x_1909 = lean_ctor_get(x_1876, 25);
lean_inc(x_1909);
lean_dec(x_1876);
x_1910 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_1910, 0, x_1878);
lean_ctor_set(x_1910, 1, x_1884);
lean_ctor_set(x_1910, 2, x_1885);
lean_ctor_set(x_1910, 3, x_1886);
lean_ctor_set(x_1910, 4, x_1887);
lean_ctor_set(x_1910, 5, x_1888);
lean_ctor_set(x_1910, 6, x_1889);
lean_ctor_set(x_1910, 7, x_1891);
lean_ctor_set(x_1910, 8, x_1892);
lean_ctor_set(x_1910, 9, x_1893);
lean_ctor_set(x_1910, 10, x_1894);
lean_ctor_set(x_1910, 11, x_1895);
lean_ctor_set(x_1910, 12, x_1896);
lean_ctor_set(x_1910, 13, x_1897);
lean_ctor_set(x_1910, 14, x_1898);
lean_ctor_set(x_1910, 15, x_1899);
lean_ctor_set(x_1910, 16, x_1900);
lean_ctor_set(x_1910, 17, x_1901);
lean_ctor_set(x_1910, 18, x_1902);
lean_ctor_set(x_1910, 19, x_1903);
lean_ctor_set(x_1910, 20, x_1904);
lean_ctor_set(x_1910, 21, x_1905);
lean_ctor_set(x_1910, 22, x_1906);
lean_ctor_set(x_1910, 23, x_1907);
lean_ctor_set(x_1910, 24, x_1908);
lean_ctor_set(x_1910, 25, x_1909);
lean_ctor_set_uint8(x_1910, sizeof(void*)*26, x_1890);
x_1911 = lean_st_ref_set(x_13, x_1910, x_1877);
lean_dec(x_13);
x_1912 = lean_ctor_get(x_1911, 1);
lean_inc(x_1912);
if (lean_is_exclusive(x_1911)) {
 lean_ctor_release(x_1911, 0);
 lean_ctor_release(x_1911, 1);
 x_1913 = x_1911;
} else {
 lean_dec_ref(x_1911);
 x_1913 = lean_box(0);
}
if (lean_is_scalar(x_1913)) {
 x_1914 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1914 = x_1913;
}
lean_ctor_set(x_1914, 0, x_1874);
lean_ctor_set(x_1914, 1, x_1912);
return x_1914;
}
else
{
lean_object* x_1915; lean_object* x_1916; lean_object* x_1917; lean_object* x_1918; lean_object* x_1919; lean_object* x_1920; lean_object* x_1921; lean_object* x_1922; lean_object* x_1923; lean_object* x_1924; lean_object* x_1925; lean_object* x_1926; lean_object* x_1927; lean_object* x_1928; lean_object* x_1929; uint8_t x_1930; lean_object* x_1931; lean_object* x_1932; lean_object* x_1933; lean_object* x_1934; lean_object* x_1935; lean_object* x_1936; lean_object* x_1937; lean_object* x_1938; lean_object* x_1939; lean_object* x_1940; lean_object* x_1941; lean_object* x_1942; lean_object* x_1943; lean_object* x_1944; lean_object* x_1945; lean_object* x_1946; lean_object* x_1947; lean_object* x_1948; lean_object* x_1949; lean_object* x_1950; lean_object* x_1951; lean_object* x_1952; lean_object* x_1953; lean_object* x_1954; 
lean_dec(x_10);
lean_dec(x_9);
x_1915 = lean_st_ref_take(x_13, x_1865);
x_1916 = lean_ctor_get(x_1915, 0);
lean_inc(x_1916);
x_1917 = lean_ctor_get(x_1915, 1);
lean_inc(x_1917);
lean_dec(x_1915);
x_1918 = lean_ctor_get(x_1916, 0);
lean_inc(x_1918);
x_1919 = lean_ctor_get(x_1916, 1);
lean_inc(x_1919);
x_1920 = lean_ctor_get(x_1919, 0);
lean_inc(x_1920);
x_1921 = lean_ctor_get(x_1919, 1);
lean_inc(x_1921);
x_1922 = lean_ctor_get(x_1919, 2);
lean_inc(x_1922);
lean_dec(x_1919);
lean_inc(x_1);
x_1923 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1922, x_1766, x_1);
x_1924 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1924, 0, x_1920);
lean_ctor_set(x_1924, 1, x_1921);
lean_ctor_set(x_1924, 2, x_1923);
x_1925 = lean_ctor_get(x_1916, 2);
lean_inc(x_1925);
x_1926 = lean_ctor_get(x_1916, 3);
lean_inc(x_1926);
x_1927 = lean_ctor_get(x_1916, 4);
lean_inc(x_1927);
x_1928 = lean_ctor_get(x_1916, 5);
lean_inc(x_1928);
x_1929 = lean_ctor_get(x_1916, 6);
lean_inc(x_1929);
x_1930 = lean_ctor_get_uint8(x_1916, sizeof(void*)*26);
x_1931 = lean_ctor_get(x_1916, 7);
lean_inc(x_1931);
x_1932 = lean_ctor_get(x_1916, 8);
lean_inc(x_1932);
x_1933 = lean_ctor_get(x_1916, 9);
lean_inc(x_1933);
x_1934 = lean_ctor_get(x_1916, 10);
lean_inc(x_1934);
x_1935 = lean_ctor_get(x_1916, 11);
lean_inc(x_1935);
x_1936 = lean_ctor_get(x_1916, 12);
lean_inc(x_1936);
x_1937 = lean_ctor_get(x_1916, 13);
lean_inc(x_1937);
x_1938 = lean_ctor_get(x_1916, 14);
lean_inc(x_1938);
x_1939 = lean_ctor_get(x_1916, 15);
lean_inc(x_1939);
x_1940 = lean_ctor_get(x_1916, 16);
lean_inc(x_1940);
x_1941 = lean_ctor_get(x_1916, 17);
lean_inc(x_1941);
x_1942 = lean_ctor_get(x_1916, 18);
lean_inc(x_1942);
x_1943 = lean_ctor_get(x_1916, 19);
lean_inc(x_1943);
x_1944 = lean_ctor_get(x_1916, 20);
lean_inc(x_1944);
x_1945 = lean_ctor_get(x_1916, 21);
lean_inc(x_1945);
x_1946 = lean_ctor_get(x_1916, 22);
lean_inc(x_1946);
x_1947 = lean_ctor_get(x_1916, 23);
lean_inc(x_1947);
x_1948 = lean_ctor_get(x_1916, 24);
lean_inc(x_1948);
x_1949 = lean_ctor_get(x_1916, 25);
lean_inc(x_1949);
lean_dec(x_1916);
x_1950 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_1950, 0, x_1918);
lean_ctor_set(x_1950, 1, x_1924);
lean_ctor_set(x_1950, 2, x_1925);
lean_ctor_set(x_1950, 3, x_1926);
lean_ctor_set(x_1950, 4, x_1927);
lean_ctor_set(x_1950, 5, x_1928);
lean_ctor_set(x_1950, 6, x_1929);
lean_ctor_set(x_1950, 7, x_1931);
lean_ctor_set(x_1950, 8, x_1932);
lean_ctor_set(x_1950, 9, x_1933);
lean_ctor_set(x_1950, 10, x_1934);
lean_ctor_set(x_1950, 11, x_1935);
lean_ctor_set(x_1950, 12, x_1936);
lean_ctor_set(x_1950, 13, x_1937);
lean_ctor_set(x_1950, 14, x_1938);
lean_ctor_set(x_1950, 15, x_1939);
lean_ctor_set(x_1950, 16, x_1940);
lean_ctor_set(x_1950, 17, x_1941);
lean_ctor_set(x_1950, 18, x_1942);
lean_ctor_set(x_1950, 19, x_1943);
lean_ctor_set(x_1950, 20, x_1944);
lean_ctor_set(x_1950, 21, x_1945);
lean_ctor_set(x_1950, 22, x_1946);
lean_ctor_set(x_1950, 23, x_1947);
lean_ctor_set(x_1950, 24, x_1948);
lean_ctor_set(x_1950, 25, x_1949);
lean_ctor_set_uint8(x_1950, sizeof(void*)*26, x_1930);
x_1951 = lean_st_ref_set(x_13, x_1950, x_1917);
lean_dec(x_13);
x_1952 = lean_ctor_get(x_1951, 1);
lean_inc(x_1952);
if (lean_is_exclusive(x_1951)) {
 lean_ctor_release(x_1951, 0);
 lean_ctor_release(x_1951, 1);
 x_1953 = x_1951;
} else {
 lean_dec_ref(x_1951);
 x_1953 = lean_box(0);
}
if (lean_is_scalar(x_1953)) {
 x_1954 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1954 = x_1953;
}
lean_ctor_set(x_1954, 0, x_1);
lean_ctor_set(x_1954, 1, x_1952);
return x_1954;
}
}
else
{
lean_object* x_1955; lean_object* x_1956; 
lean_dec(x_1766);
lean_dec(x_1764);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_1955 = lean_ctor_get(x_1868, 0);
lean_inc(x_1955);
lean_dec(x_1868);
x_1956 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1956, 0, x_1955);
lean_ctor_set(x_1956, 1, x_1865);
return x_1956;
}
}
}
else
{
uint8_t x_1957; 
lean_dec(x_1764);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_1957 = !lean_is_exclusive(x_1765);
if (x_1957 == 0)
{
return x_1765;
}
else
{
lean_object* x_1958; lean_object* x_1959; lean_object* x_1960; 
x_1958 = lean_ctor_get(x_1765, 0);
x_1959 = lean_ctor_get(x_1765, 1);
lean_inc(x_1959);
lean_inc(x_1958);
lean_dec(x_1765);
x_1960 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1960, 0, x_1958);
lean_ctor_set(x_1960, 1, x_1959);
return x_1960;
}
}
}
block_1999:
{
lean_object* x_1963; 
lean_dec(x_1962);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_9);
x_1963 = l_Lean_Meta_getFunInfo(x_9, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_1963) == 0)
{
lean_object* x_1964; lean_object* x_1965; lean_object* x_1966; lean_object* x_1967; lean_object* x_1968; lean_object* x_1969; lean_object* x_1970; uint8_t x_1971; lean_object* x_1972; lean_object* x_1973; lean_object* x_1974; lean_object* x_1975; 
x_1964 = lean_ctor_get(x_1963, 0);
lean_inc(x_1964);
x_1965 = lean_ctor_get(x_1963, 1);
lean_inc(x_1965);
lean_dec(x_1963);
x_1966 = lean_ctor_get(x_1964, 0);
lean_inc(x_1966);
lean_dec(x_1964);
x_1967 = lean_array_get_size(x_10);
x_1968 = lean_unsigned_to_nat(0u);
x_1969 = lean_unsigned_to_nat(1u);
lean_inc(x_1967);
x_1970 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1970, 0, x_1968);
lean_ctor_set(x_1970, 1, x_1967);
lean_ctor_set(x_1970, 2, x_1969);
x_1971 = 0;
x_1972 = lean_box(x_1971);
lean_inc(x_10);
x_1973 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1973, 0, x_10);
lean_ctor_set(x_1973, 1, x_1972);
x_1974 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_1970);
lean_inc(x_9);
lean_inc(x_1);
x_1975 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1974, x_1966, x_1967, x_1970, x_1970, x_1973, x_1968, lean_box(0), lean_box(0), x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_1965);
if (lean_obj_tag(x_1975) == 0)
{
lean_object* x_1976; lean_object* x_1977; uint8_t x_1978; 
x_1976 = lean_ctor_get(x_1975, 0);
lean_inc(x_1976);
x_1977 = lean_ctor_get(x_1976, 1);
lean_inc(x_1977);
x_1978 = lean_unbox(x_1977);
lean_dec(x_1977);
if (x_1978 == 0)
{
uint8_t x_1979; 
lean_dec(x_1976);
lean_dec(x_9);
x_1979 = !lean_is_exclusive(x_1975);
if (x_1979 == 0)
{
lean_object* x_1980; 
x_1980 = lean_ctor_get(x_1975, 0);
lean_dec(x_1980);
lean_ctor_set(x_1975, 0, x_1);
return x_1975;
}
else
{
lean_object* x_1981; lean_object* x_1982; 
x_1981 = lean_ctor_get(x_1975, 1);
lean_inc(x_1981);
lean_dec(x_1975);
x_1982 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1982, 0, x_1);
lean_ctor_set(x_1982, 1, x_1981);
return x_1982;
}
}
else
{
uint8_t x_1983; 
lean_dec(x_1);
x_1983 = !lean_is_exclusive(x_1975);
if (x_1983 == 0)
{
lean_object* x_1984; lean_object* x_1985; lean_object* x_1986; 
x_1984 = lean_ctor_get(x_1975, 0);
lean_dec(x_1984);
x_1985 = lean_ctor_get(x_1976, 0);
lean_inc(x_1985);
lean_dec(x_1976);
x_1986 = l_Lean_mkAppN(x_9, x_1985);
lean_dec(x_1985);
lean_ctor_set(x_1975, 0, x_1986);
return x_1975;
}
else
{
lean_object* x_1987; lean_object* x_1988; lean_object* x_1989; lean_object* x_1990; 
x_1987 = lean_ctor_get(x_1975, 1);
lean_inc(x_1987);
lean_dec(x_1975);
x_1988 = lean_ctor_get(x_1976, 0);
lean_inc(x_1988);
lean_dec(x_1976);
x_1989 = l_Lean_mkAppN(x_9, x_1988);
lean_dec(x_1988);
x_1990 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1990, 0, x_1989);
lean_ctor_set(x_1990, 1, x_1987);
return x_1990;
}
}
}
else
{
uint8_t x_1991; 
lean_dec(x_9);
lean_dec(x_1);
x_1991 = !lean_is_exclusive(x_1975);
if (x_1991 == 0)
{
return x_1975;
}
else
{
lean_object* x_1992; lean_object* x_1993; lean_object* x_1994; 
x_1992 = lean_ctor_get(x_1975, 0);
x_1993 = lean_ctor_get(x_1975, 1);
lean_inc(x_1993);
lean_inc(x_1992);
lean_dec(x_1975);
x_1994 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1994, 0, x_1992);
lean_ctor_set(x_1994, 1, x_1993);
return x_1994;
}
}
}
else
{
uint8_t x_1995; 
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
x_1995 = !lean_is_exclusive(x_1963);
if (x_1995 == 0)
{
return x_1963;
}
else
{
lean_object* x_1996; lean_object* x_1997; lean_object* x_1998; 
x_1996 = lean_ctor_get(x_1963, 0);
x_1997 = lean_ctor_get(x_1963, 1);
lean_inc(x_1997);
lean_inc(x_1996);
lean_dec(x_1963);
x_1998 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1998, 0, x_1996);
lean_ctor_set(x_1998, 1, x_1997);
return x_1998;
}
}
}
}
case 9:
{
lean_object* x_2012; lean_object* x_2210; lean_object* x_2248; uint8_t x_2249; 
lean_dec(x_11);
x_2248 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_2249 = l_Lean_Expr_isConstOf(x_9, x_2248);
if (x_2249 == 0)
{
lean_object* x_2250; 
x_2250 = lean_box(0);
x_2210 = x_2250;
goto block_2247;
}
else
{
lean_object* x_2251; lean_object* x_2252; uint8_t x_2253; 
x_2251 = lean_array_get_size(x_10);
x_2252 = lean_unsigned_to_nat(2u);
x_2253 = lean_nat_dec_eq(x_2251, x_2252);
if (x_2253 == 0)
{
lean_object* x_2254; 
lean_dec(x_2251);
x_2254 = lean_box(0);
x_2210 = x_2254;
goto block_2247;
}
else
{
lean_object* x_2255; uint8_t x_2256; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2255 = lean_unsigned_to_nat(0u);
x_2256 = lean_nat_dec_lt(x_2255, x_2251);
lean_dec(x_2251);
if (x_2256 == 0)
{
lean_object* x_2257; lean_object* x_2258; 
x_2257 = l_Lean_instInhabitedExpr;
x_2258 = l_outOfBounds___rarg(x_2257);
x_2012 = x_2258;
goto block_2209;
}
else
{
lean_object* x_2259; 
x_2259 = lean_array_fget(x_10, x_2255);
x_2012 = x_2259;
goto block_2209;
}
}
}
block_2209:
{
lean_object* x_2013; 
lean_inc(x_13);
lean_inc(x_2012);
x_2013 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_2012, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_2013) == 0)
{
lean_object* x_2014; lean_object* x_2015; lean_object* x_2016; uint8_t x_2017; 
x_2014 = lean_ctor_get(x_2013, 0);
lean_inc(x_2014);
x_2015 = lean_ctor_get(x_2013, 1);
lean_inc(x_2015);
lean_dec(x_2013);
x_2016 = lean_st_ref_get(x_13, x_2015);
x_2017 = !lean_is_exclusive(x_2016);
if (x_2017 == 0)
{
lean_object* x_2018; lean_object* x_2019; lean_object* x_2020; lean_object* x_2021; lean_object* x_2022; 
x_2018 = lean_ctor_get(x_2016, 0);
x_2019 = lean_ctor_get(x_2016, 1);
x_2020 = lean_ctor_get(x_2018, 1);
lean_inc(x_2020);
lean_dec(x_2018);
x_2021 = lean_ctor_get(x_2020, 2);
lean_inc(x_2021);
lean_dec(x_2020);
x_2022 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_2021, x_2014);
if (lean_obj_tag(x_2022) == 0)
{
size_t x_2023; size_t x_2024; uint8_t x_2025; 
lean_free_object(x_2016);
x_2023 = lean_ptr_addr(x_2012);
lean_dec(x_2012);
x_2024 = lean_ptr_addr(x_2014);
x_2025 = lean_usize_dec_eq(x_2023, x_2024);
if (x_2025 == 0)
{
lean_object* x_2026; lean_object* x_2027; lean_object* x_2028; lean_object* x_2029; lean_object* x_2030; lean_object* x_2031; lean_object* x_2032; lean_object* x_2033; lean_object* x_2034; lean_object* x_2035; lean_object* x_2036; lean_object* x_2037; lean_object* x_2038; lean_object* x_2039; lean_object* x_2040; lean_object* x_2041; lean_object* x_2042; lean_object* x_2043; uint8_t x_2044; lean_object* x_2045; lean_object* x_2046; lean_object* x_2047; lean_object* x_2048; lean_object* x_2049; lean_object* x_2050; lean_object* x_2051; lean_object* x_2052; lean_object* x_2053; lean_object* x_2054; lean_object* x_2055; lean_object* x_2056; lean_object* x_2057; lean_object* x_2058; lean_object* x_2059; lean_object* x_2060; lean_object* x_2061; lean_object* x_2062; lean_object* x_2063; lean_object* x_2064; lean_object* x_2065; uint8_t x_2066; 
lean_dec(x_1);
x_2026 = lean_unsigned_to_nat(0u);
lean_inc(x_2014);
x_2027 = lean_array_set(x_10, x_2026, x_2014);
x_2028 = l_Lean_mkAppN(x_9, x_2027);
lean_dec(x_2027);
x_2029 = lean_st_ref_take(x_13, x_2019);
x_2030 = lean_ctor_get(x_2029, 0);
lean_inc(x_2030);
x_2031 = lean_ctor_get(x_2029, 1);
lean_inc(x_2031);
lean_dec(x_2029);
x_2032 = lean_ctor_get(x_2030, 0);
lean_inc(x_2032);
x_2033 = lean_ctor_get(x_2030, 1);
lean_inc(x_2033);
x_2034 = lean_ctor_get(x_2033, 0);
lean_inc(x_2034);
x_2035 = lean_ctor_get(x_2033, 1);
lean_inc(x_2035);
x_2036 = lean_ctor_get(x_2033, 2);
lean_inc(x_2036);
lean_dec(x_2033);
lean_inc(x_2028);
x_2037 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_2036, x_2014, x_2028);
x_2038 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2038, 0, x_2034);
lean_ctor_set(x_2038, 1, x_2035);
lean_ctor_set(x_2038, 2, x_2037);
x_2039 = lean_ctor_get(x_2030, 2);
lean_inc(x_2039);
x_2040 = lean_ctor_get(x_2030, 3);
lean_inc(x_2040);
x_2041 = lean_ctor_get(x_2030, 4);
lean_inc(x_2041);
x_2042 = lean_ctor_get(x_2030, 5);
lean_inc(x_2042);
x_2043 = lean_ctor_get(x_2030, 6);
lean_inc(x_2043);
x_2044 = lean_ctor_get_uint8(x_2030, sizeof(void*)*26);
x_2045 = lean_ctor_get(x_2030, 7);
lean_inc(x_2045);
x_2046 = lean_ctor_get(x_2030, 8);
lean_inc(x_2046);
x_2047 = lean_ctor_get(x_2030, 9);
lean_inc(x_2047);
x_2048 = lean_ctor_get(x_2030, 10);
lean_inc(x_2048);
x_2049 = lean_ctor_get(x_2030, 11);
lean_inc(x_2049);
x_2050 = lean_ctor_get(x_2030, 12);
lean_inc(x_2050);
x_2051 = lean_ctor_get(x_2030, 13);
lean_inc(x_2051);
x_2052 = lean_ctor_get(x_2030, 14);
lean_inc(x_2052);
x_2053 = lean_ctor_get(x_2030, 15);
lean_inc(x_2053);
x_2054 = lean_ctor_get(x_2030, 16);
lean_inc(x_2054);
x_2055 = lean_ctor_get(x_2030, 17);
lean_inc(x_2055);
x_2056 = lean_ctor_get(x_2030, 18);
lean_inc(x_2056);
x_2057 = lean_ctor_get(x_2030, 19);
lean_inc(x_2057);
x_2058 = lean_ctor_get(x_2030, 20);
lean_inc(x_2058);
x_2059 = lean_ctor_get(x_2030, 21);
lean_inc(x_2059);
x_2060 = lean_ctor_get(x_2030, 22);
lean_inc(x_2060);
x_2061 = lean_ctor_get(x_2030, 23);
lean_inc(x_2061);
x_2062 = lean_ctor_get(x_2030, 24);
lean_inc(x_2062);
x_2063 = lean_ctor_get(x_2030, 25);
lean_inc(x_2063);
lean_dec(x_2030);
x_2064 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_2064, 0, x_2032);
lean_ctor_set(x_2064, 1, x_2038);
lean_ctor_set(x_2064, 2, x_2039);
lean_ctor_set(x_2064, 3, x_2040);
lean_ctor_set(x_2064, 4, x_2041);
lean_ctor_set(x_2064, 5, x_2042);
lean_ctor_set(x_2064, 6, x_2043);
lean_ctor_set(x_2064, 7, x_2045);
lean_ctor_set(x_2064, 8, x_2046);
lean_ctor_set(x_2064, 9, x_2047);
lean_ctor_set(x_2064, 10, x_2048);
lean_ctor_set(x_2064, 11, x_2049);
lean_ctor_set(x_2064, 12, x_2050);
lean_ctor_set(x_2064, 13, x_2051);
lean_ctor_set(x_2064, 14, x_2052);
lean_ctor_set(x_2064, 15, x_2053);
lean_ctor_set(x_2064, 16, x_2054);
lean_ctor_set(x_2064, 17, x_2055);
lean_ctor_set(x_2064, 18, x_2056);
lean_ctor_set(x_2064, 19, x_2057);
lean_ctor_set(x_2064, 20, x_2058);
lean_ctor_set(x_2064, 21, x_2059);
lean_ctor_set(x_2064, 22, x_2060);
lean_ctor_set(x_2064, 23, x_2061);
lean_ctor_set(x_2064, 24, x_2062);
lean_ctor_set(x_2064, 25, x_2063);
lean_ctor_set_uint8(x_2064, sizeof(void*)*26, x_2044);
x_2065 = lean_st_ref_set(x_13, x_2064, x_2031);
lean_dec(x_13);
x_2066 = !lean_is_exclusive(x_2065);
if (x_2066 == 0)
{
lean_object* x_2067; 
x_2067 = lean_ctor_get(x_2065, 0);
lean_dec(x_2067);
lean_ctor_set(x_2065, 0, x_2028);
return x_2065;
}
else
{
lean_object* x_2068; lean_object* x_2069; 
x_2068 = lean_ctor_get(x_2065, 1);
lean_inc(x_2068);
lean_dec(x_2065);
x_2069 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2069, 0, x_2028);
lean_ctor_set(x_2069, 1, x_2068);
return x_2069;
}
}
else
{
lean_object* x_2070; lean_object* x_2071; lean_object* x_2072; lean_object* x_2073; lean_object* x_2074; lean_object* x_2075; lean_object* x_2076; lean_object* x_2077; lean_object* x_2078; lean_object* x_2079; lean_object* x_2080; lean_object* x_2081; lean_object* x_2082; lean_object* x_2083; lean_object* x_2084; uint8_t x_2085; lean_object* x_2086; lean_object* x_2087; lean_object* x_2088; lean_object* x_2089; lean_object* x_2090; lean_object* x_2091; lean_object* x_2092; lean_object* x_2093; lean_object* x_2094; lean_object* x_2095; lean_object* x_2096; lean_object* x_2097; lean_object* x_2098; lean_object* x_2099; lean_object* x_2100; lean_object* x_2101; lean_object* x_2102; lean_object* x_2103; lean_object* x_2104; lean_object* x_2105; lean_object* x_2106; uint8_t x_2107; 
lean_dec(x_10);
lean_dec(x_9);
x_2070 = lean_st_ref_take(x_13, x_2019);
x_2071 = lean_ctor_get(x_2070, 0);
lean_inc(x_2071);
x_2072 = lean_ctor_get(x_2070, 1);
lean_inc(x_2072);
lean_dec(x_2070);
x_2073 = lean_ctor_get(x_2071, 0);
lean_inc(x_2073);
x_2074 = lean_ctor_get(x_2071, 1);
lean_inc(x_2074);
x_2075 = lean_ctor_get(x_2074, 0);
lean_inc(x_2075);
x_2076 = lean_ctor_get(x_2074, 1);
lean_inc(x_2076);
x_2077 = lean_ctor_get(x_2074, 2);
lean_inc(x_2077);
lean_dec(x_2074);
lean_inc(x_1);
x_2078 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_2077, x_2014, x_1);
x_2079 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2079, 0, x_2075);
lean_ctor_set(x_2079, 1, x_2076);
lean_ctor_set(x_2079, 2, x_2078);
x_2080 = lean_ctor_get(x_2071, 2);
lean_inc(x_2080);
x_2081 = lean_ctor_get(x_2071, 3);
lean_inc(x_2081);
x_2082 = lean_ctor_get(x_2071, 4);
lean_inc(x_2082);
x_2083 = lean_ctor_get(x_2071, 5);
lean_inc(x_2083);
x_2084 = lean_ctor_get(x_2071, 6);
lean_inc(x_2084);
x_2085 = lean_ctor_get_uint8(x_2071, sizeof(void*)*26);
x_2086 = lean_ctor_get(x_2071, 7);
lean_inc(x_2086);
x_2087 = lean_ctor_get(x_2071, 8);
lean_inc(x_2087);
x_2088 = lean_ctor_get(x_2071, 9);
lean_inc(x_2088);
x_2089 = lean_ctor_get(x_2071, 10);
lean_inc(x_2089);
x_2090 = lean_ctor_get(x_2071, 11);
lean_inc(x_2090);
x_2091 = lean_ctor_get(x_2071, 12);
lean_inc(x_2091);
x_2092 = lean_ctor_get(x_2071, 13);
lean_inc(x_2092);
x_2093 = lean_ctor_get(x_2071, 14);
lean_inc(x_2093);
x_2094 = lean_ctor_get(x_2071, 15);
lean_inc(x_2094);
x_2095 = lean_ctor_get(x_2071, 16);
lean_inc(x_2095);
x_2096 = lean_ctor_get(x_2071, 17);
lean_inc(x_2096);
x_2097 = lean_ctor_get(x_2071, 18);
lean_inc(x_2097);
x_2098 = lean_ctor_get(x_2071, 19);
lean_inc(x_2098);
x_2099 = lean_ctor_get(x_2071, 20);
lean_inc(x_2099);
x_2100 = lean_ctor_get(x_2071, 21);
lean_inc(x_2100);
x_2101 = lean_ctor_get(x_2071, 22);
lean_inc(x_2101);
x_2102 = lean_ctor_get(x_2071, 23);
lean_inc(x_2102);
x_2103 = lean_ctor_get(x_2071, 24);
lean_inc(x_2103);
x_2104 = lean_ctor_get(x_2071, 25);
lean_inc(x_2104);
lean_dec(x_2071);
x_2105 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_2105, 0, x_2073);
lean_ctor_set(x_2105, 1, x_2079);
lean_ctor_set(x_2105, 2, x_2080);
lean_ctor_set(x_2105, 3, x_2081);
lean_ctor_set(x_2105, 4, x_2082);
lean_ctor_set(x_2105, 5, x_2083);
lean_ctor_set(x_2105, 6, x_2084);
lean_ctor_set(x_2105, 7, x_2086);
lean_ctor_set(x_2105, 8, x_2087);
lean_ctor_set(x_2105, 9, x_2088);
lean_ctor_set(x_2105, 10, x_2089);
lean_ctor_set(x_2105, 11, x_2090);
lean_ctor_set(x_2105, 12, x_2091);
lean_ctor_set(x_2105, 13, x_2092);
lean_ctor_set(x_2105, 14, x_2093);
lean_ctor_set(x_2105, 15, x_2094);
lean_ctor_set(x_2105, 16, x_2095);
lean_ctor_set(x_2105, 17, x_2096);
lean_ctor_set(x_2105, 18, x_2097);
lean_ctor_set(x_2105, 19, x_2098);
lean_ctor_set(x_2105, 20, x_2099);
lean_ctor_set(x_2105, 21, x_2100);
lean_ctor_set(x_2105, 22, x_2101);
lean_ctor_set(x_2105, 23, x_2102);
lean_ctor_set(x_2105, 24, x_2103);
lean_ctor_set(x_2105, 25, x_2104);
lean_ctor_set_uint8(x_2105, sizeof(void*)*26, x_2085);
x_2106 = lean_st_ref_set(x_13, x_2105, x_2072);
lean_dec(x_13);
x_2107 = !lean_is_exclusive(x_2106);
if (x_2107 == 0)
{
lean_object* x_2108; 
x_2108 = lean_ctor_get(x_2106, 0);
lean_dec(x_2108);
lean_ctor_set(x_2106, 0, x_1);
return x_2106;
}
else
{
lean_object* x_2109; lean_object* x_2110; 
x_2109 = lean_ctor_get(x_2106, 1);
lean_inc(x_2109);
lean_dec(x_2106);
x_2110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2110, 0, x_1);
lean_ctor_set(x_2110, 1, x_2109);
return x_2110;
}
}
}
else
{
lean_object* x_2111; 
lean_dec(x_2014);
lean_dec(x_2012);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_2111 = lean_ctor_get(x_2022, 0);
lean_inc(x_2111);
lean_dec(x_2022);
lean_ctor_set(x_2016, 0, x_2111);
return x_2016;
}
}
else
{
lean_object* x_2112; lean_object* x_2113; lean_object* x_2114; lean_object* x_2115; lean_object* x_2116; 
x_2112 = lean_ctor_get(x_2016, 0);
x_2113 = lean_ctor_get(x_2016, 1);
lean_inc(x_2113);
lean_inc(x_2112);
lean_dec(x_2016);
x_2114 = lean_ctor_get(x_2112, 1);
lean_inc(x_2114);
lean_dec(x_2112);
x_2115 = lean_ctor_get(x_2114, 2);
lean_inc(x_2115);
lean_dec(x_2114);
x_2116 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_2115, x_2014);
if (lean_obj_tag(x_2116) == 0)
{
size_t x_2117; size_t x_2118; uint8_t x_2119; 
x_2117 = lean_ptr_addr(x_2012);
lean_dec(x_2012);
x_2118 = lean_ptr_addr(x_2014);
x_2119 = lean_usize_dec_eq(x_2117, x_2118);
if (x_2119 == 0)
{
lean_object* x_2120; lean_object* x_2121; lean_object* x_2122; lean_object* x_2123; lean_object* x_2124; lean_object* x_2125; lean_object* x_2126; lean_object* x_2127; lean_object* x_2128; lean_object* x_2129; lean_object* x_2130; lean_object* x_2131; lean_object* x_2132; lean_object* x_2133; lean_object* x_2134; lean_object* x_2135; lean_object* x_2136; lean_object* x_2137; uint8_t x_2138; lean_object* x_2139; lean_object* x_2140; lean_object* x_2141; lean_object* x_2142; lean_object* x_2143; lean_object* x_2144; lean_object* x_2145; lean_object* x_2146; lean_object* x_2147; lean_object* x_2148; lean_object* x_2149; lean_object* x_2150; lean_object* x_2151; lean_object* x_2152; lean_object* x_2153; lean_object* x_2154; lean_object* x_2155; lean_object* x_2156; lean_object* x_2157; lean_object* x_2158; lean_object* x_2159; lean_object* x_2160; lean_object* x_2161; lean_object* x_2162; 
lean_dec(x_1);
x_2120 = lean_unsigned_to_nat(0u);
lean_inc(x_2014);
x_2121 = lean_array_set(x_10, x_2120, x_2014);
x_2122 = l_Lean_mkAppN(x_9, x_2121);
lean_dec(x_2121);
x_2123 = lean_st_ref_take(x_13, x_2113);
x_2124 = lean_ctor_get(x_2123, 0);
lean_inc(x_2124);
x_2125 = lean_ctor_get(x_2123, 1);
lean_inc(x_2125);
lean_dec(x_2123);
x_2126 = lean_ctor_get(x_2124, 0);
lean_inc(x_2126);
x_2127 = lean_ctor_get(x_2124, 1);
lean_inc(x_2127);
x_2128 = lean_ctor_get(x_2127, 0);
lean_inc(x_2128);
x_2129 = lean_ctor_get(x_2127, 1);
lean_inc(x_2129);
x_2130 = lean_ctor_get(x_2127, 2);
lean_inc(x_2130);
lean_dec(x_2127);
lean_inc(x_2122);
x_2131 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_2130, x_2014, x_2122);
x_2132 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2132, 0, x_2128);
lean_ctor_set(x_2132, 1, x_2129);
lean_ctor_set(x_2132, 2, x_2131);
x_2133 = lean_ctor_get(x_2124, 2);
lean_inc(x_2133);
x_2134 = lean_ctor_get(x_2124, 3);
lean_inc(x_2134);
x_2135 = lean_ctor_get(x_2124, 4);
lean_inc(x_2135);
x_2136 = lean_ctor_get(x_2124, 5);
lean_inc(x_2136);
x_2137 = lean_ctor_get(x_2124, 6);
lean_inc(x_2137);
x_2138 = lean_ctor_get_uint8(x_2124, sizeof(void*)*26);
x_2139 = lean_ctor_get(x_2124, 7);
lean_inc(x_2139);
x_2140 = lean_ctor_get(x_2124, 8);
lean_inc(x_2140);
x_2141 = lean_ctor_get(x_2124, 9);
lean_inc(x_2141);
x_2142 = lean_ctor_get(x_2124, 10);
lean_inc(x_2142);
x_2143 = lean_ctor_get(x_2124, 11);
lean_inc(x_2143);
x_2144 = lean_ctor_get(x_2124, 12);
lean_inc(x_2144);
x_2145 = lean_ctor_get(x_2124, 13);
lean_inc(x_2145);
x_2146 = lean_ctor_get(x_2124, 14);
lean_inc(x_2146);
x_2147 = lean_ctor_get(x_2124, 15);
lean_inc(x_2147);
x_2148 = lean_ctor_get(x_2124, 16);
lean_inc(x_2148);
x_2149 = lean_ctor_get(x_2124, 17);
lean_inc(x_2149);
x_2150 = lean_ctor_get(x_2124, 18);
lean_inc(x_2150);
x_2151 = lean_ctor_get(x_2124, 19);
lean_inc(x_2151);
x_2152 = lean_ctor_get(x_2124, 20);
lean_inc(x_2152);
x_2153 = lean_ctor_get(x_2124, 21);
lean_inc(x_2153);
x_2154 = lean_ctor_get(x_2124, 22);
lean_inc(x_2154);
x_2155 = lean_ctor_get(x_2124, 23);
lean_inc(x_2155);
x_2156 = lean_ctor_get(x_2124, 24);
lean_inc(x_2156);
x_2157 = lean_ctor_get(x_2124, 25);
lean_inc(x_2157);
lean_dec(x_2124);
x_2158 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_2158, 0, x_2126);
lean_ctor_set(x_2158, 1, x_2132);
lean_ctor_set(x_2158, 2, x_2133);
lean_ctor_set(x_2158, 3, x_2134);
lean_ctor_set(x_2158, 4, x_2135);
lean_ctor_set(x_2158, 5, x_2136);
lean_ctor_set(x_2158, 6, x_2137);
lean_ctor_set(x_2158, 7, x_2139);
lean_ctor_set(x_2158, 8, x_2140);
lean_ctor_set(x_2158, 9, x_2141);
lean_ctor_set(x_2158, 10, x_2142);
lean_ctor_set(x_2158, 11, x_2143);
lean_ctor_set(x_2158, 12, x_2144);
lean_ctor_set(x_2158, 13, x_2145);
lean_ctor_set(x_2158, 14, x_2146);
lean_ctor_set(x_2158, 15, x_2147);
lean_ctor_set(x_2158, 16, x_2148);
lean_ctor_set(x_2158, 17, x_2149);
lean_ctor_set(x_2158, 18, x_2150);
lean_ctor_set(x_2158, 19, x_2151);
lean_ctor_set(x_2158, 20, x_2152);
lean_ctor_set(x_2158, 21, x_2153);
lean_ctor_set(x_2158, 22, x_2154);
lean_ctor_set(x_2158, 23, x_2155);
lean_ctor_set(x_2158, 24, x_2156);
lean_ctor_set(x_2158, 25, x_2157);
lean_ctor_set_uint8(x_2158, sizeof(void*)*26, x_2138);
x_2159 = lean_st_ref_set(x_13, x_2158, x_2125);
lean_dec(x_13);
x_2160 = lean_ctor_get(x_2159, 1);
lean_inc(x_2160);
if (lean_is_exclusive(x_2159)) {
 lean_ctor_release(x_2159, 0);
 lean_ctor_release(x_2159, 1);
 x_2161 = x_2159;
} else {
 lean_dec_ref(x_2159);
 x_2161 = lean_box(0);
}
if (lean_is_scalar(x_2161)) {
 x_2162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2162 = x_2161;
}
lean_ctor_set(x_2162, 0, x_2122);
lean_ctor_set(x_2162, 1, x_2160);
return x_2162;
}
else
{
lean_object* x_2163; lean_object* x_2164; lean_object* x_2165; lean_object* x_2166; lean_object* x_2167; lean_object* x_2168; lean_object* x_2169; lean_object* x_2170; lean_object* x_2171; lean_object* x_2172; lean_object* x_2173; lean_object* x_2174; lean_object* x_2175; lean_object* x_2176; lean_object* x_2177; uint8_t x_2178; lean_object* x_2179; lean_object* x_2180; lean_object* x_2181; lean_object* x_2182; lean_object* x_2183; lean_object* x_2184; lean_object* x_2185; lean_object* x_2186; lean_object* x_2187; lean_object* x_2188; lean_object* x_2189; lean_object* x_2190; lean_object* x_2191; lean_object* x_2192; lean_object* x_2193; lean_object* x_2194; lean_object* x_2195; lean_object* x_2196; lean_object* x_2197; lean_object* x_2198; lean_object* x_2199; lean_object* x_2200; lean_object* x_2201; lean_object* x_2202; 
lean_dec(x_10);
lean_dec(x_9);
x_2163 = lean_st_ref_take(x_13, x_2113);
x_2164 = lean_ctor_get(x_2163, 0);
lean_inc(x_2164);
x_2165 = lean_ctor_get(x_2163, 1);
lean_inc(x_2165);
lean_dec(x_2163);
x_2166 = lean_ctor_get(x_2164, 0);
lean_inc(x_2166);
x_2167 = lean_ctor_get(x_2164, 1);
lean_inc(x_2167);
x_2168 = lean_ctor_get(x_2167, 0);
lean_inc(x_2168);
x_2169 = lean_ctor_get(x_2167, 1);
lean_inc(x_2169);
x_2170 = lean_ctor_get(x_2167, 2);
lean_inc(x_2170);
lean_dec(x_2167);
lean_inc(x_1);
x_2171 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_2170, x_2014, x_1);
x_2172 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2172, 0, x_2168);
lean_ctor_set(x_2172, 1, x_2169);
lean_ctor_set(x_2172, 2, x_2171);
x_2173 = lean_ctor_get(x_2164, 2);
lean_inc(x_2173);
x_2174 = lean_ctor_get(x_2164, 3);
lean_inc(x_2174);
x_2175 = lean_ctor_get(x_2164, 4);
lean_inc(x_2175);
x_2176 = lean_ctor_get(x_2164, 5);
lean_inc(x_2176);
x_2177 = lean_ctor_get(x_2164, 6);
lean_inc(x_2177);
x_2178 = lean_ctor_get_uint8(x_2164, sizeof(void*)*26);
x_2179 = lean_ctor_get(x_2164, 7);
lean_inc(x_2179);
x_2180 = lean_ctor_get(x_2164, 8);
lean_inc(x_2180);
x_2181 = lean_ctor_get(x_2164, 9);
lean_inc(x_2181);
x_2182 = lean_ctor_get(x_2164, 10);
lean_inc(x_2182);
x_2183 = lean_ctor_get(x_2164, 11);
lean_inc(x_2183);
x_2184 = lean_ctor_get(x_2164, 12);
lean_inc(x_2184);
x_2185 = lean_ctor_get(x_2164, 13);
lean_inc(x_2185);
x_2186 = lean_ctor_get(x_2164, 14);
lean_inc(x_2186);
x_2187 = lean_ctor_get(x_2164, 15);
lean_inc(x_2187);
x_2188 = lean_ctor_get(x_2164, 16);
lean_inc(x_2188);
x_2189 = lean_ctor_get(x_2164, 17);
lean_inc(x_2189);
x_2190 = lean_ctor_get(x_2164, 18);
lean_inc(x_2190);
x_2191 = lean_ctor_get(x_2164, 19);
lean_inc(x_2191);
x_2192 = lean_ctor_get(x_2164, 20);
lean_inc(x_2192);
x_2193 = lean_ctor_get(x_2164, 21);
lean_inc(x_2193);
x_2194 = lean_ctor_get(x_2164, 22);
lean_inc(x_2194);
x_2195 = lean_ctor_get(x_2164, 23);
lean_inc(x_2195);
x_2196 = lean_ctor_get(x_2164, 24);
lean_inc(x_2196);
x_2197 = lean_ctor_get(x_2164, 25);
lean_inc(x_2197);
lean_dec(x_2164);
x_2198 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_2198, 0, x_2166);
lean_ctor_set(x_2198, 1, x_2172);
lean_ctor_set(x_2198, 2, x_2173);
lean_ctor_set(x_2198, 3, x_2174);
lean_ctor_set(x_2198, 4, x_2175);
lean_ctor_set(x_2198, 5, x_2176);
lean_ctor_set(x_2198, 6, x_2177);
lean_ctor_set(x_2198, 7, x_2179);
lean_ctor_set(x_2198, 8, x_2180);
lean_ctor_set(x_2198, 9, x_2181);
lean_ctor_set(x_2198, 10, x_2182);
lean_ctor_set(x_2198, 11, x_2183);
lean_ctor_set(x_2198, 12, x_2184);
lean_ctor_set(x_2198, 13, x_2185);
lean_ctor_set(x_2198, 14, x_2186);
lean_ctor_set(x_2198, 15, x_2187);
lean_ctor_set(x_2198, 16, x_2188);
lean_ctor_set(x_2198, 17, x_2189);
lean_ctor_set(x_2198, 18, x_2190);
lean_ctor_set(x_2198, 19, x_2191);
lean_ctor_set(x_2198, 20, x_2192);
lean_ctor_set(x_2198, 21, x_2193);
lean_ctor_set(x_2198, 22, x_2194);
lean_ctor_set(x_2198, 23, x_2195);
lean_ctor_set(x_2198, 24, x_2196);
lean_ctor_set(x_2198, 25, x_2197);
lean_ctor_set_uint8(x_2198, sizeof(void*)*26, x_2178);
x_2199 = lean_st_ref_set(x_13, x_2198, x_2165);
lean_dec(x_13);
x_2200 = lean_ctor_get(x_2199, 1);
lean_inc(x_2200);
if (lean_is_exclusive(x_2199)) {
 lean_ctor_release(x_2199, 0);
 lean_ctor_release(x_2199, 1);
 x_2201 = x_2199;
} else {
 lean_dec_ref(x_2199);
 x_2201 = lean_box(0);
}
if (lean_is_scalar(x_2201)) {
 x_2202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2202 = x_2201;
}
lean_ctor_set(x_2202, 0, x_1);
lean_ctor_set(x_2202, 1, x_2200);
return x_2202;
}
}
else
{
lean_object* x_2203; lean_object* x_2204; 
lean_dec(x_2014);
lean_dec(x_2012);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_2203 = lean_ctor_get(x_2116, 0);
lean_inc(x_2203);
lean_dec(x_2116);
x_2204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2204, 0, x_2203);
lean_ctor_set(x_2204, 1, x_2113);
return x_2204;
}
}
}
else
{
uint8_t x_2205; 
lean_dec(x_2012);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_2205 = !lean_is_exclusive(x_2013);
if (x_2205 == 0)
{
return x_2013;
}
else
{
lean_object* x_2206; lean_object* x_2207; lean_object* x_2208; 
x_2206 = lean_ctor_get(x_2013, 0);
x_2207 = lean_ctor_get(x_2013, 1);
lean_inc(x_2207);
lean_inc(x_2206);
lean_dec(x_2013);
x_2208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2208, 0, x_2206);
lean_ctor_set(x_2208, 1, x_2207);
return x_2208;
}
}
}
block_2247:
{
lean_object* x_2211; 
lean_dec(x_2210);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_9);
x_2211 = l_Lean_Meta_getFunInfo(x_9, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_2211) == 0)
{
lean_object* x_2212; lean_object* x_2213; lean_object* x_2214; lean_object* x_2215; lean_object* x_2216; lean_object* x_2217; lean_object* x_2218; uint8_t x_2219; lean_object* x_2220; lean_object* x_2221; lean_object* x_2222; lean_object* x_2223; 
x_2212 = lean_ctor_get(x_2211, 0);
lean_inc(x_2212);
x_2213 = lean_ctor_get(x_2211, 1);
lean_inc(x_2213);
lean_dec(x_2211);
x_2214 = lean_ctor_get(x_2212, 0);
lean_inc(x_2214);
lean_dec(x_2212);
x_2215 = lean_array_get_size(x_10);
x_2216 = lean_unsigned_to_nat(0u);
x_2217 = lean_unsigned_to_nat(1u);
lean_inc(x_2215);
x_2218 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2218, 0, x_2216);
lean_ctor_set(x_2218, 1, x_2215);
lean_ctor_set(x_2218, 2, x_2217);
x_2219 = 0;
x_2220 = lean_box(x_2219);
lean_inc(x_10);
x_2221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2221, 0, x_10);
lean_ctor_set(x_2221, 1, x_2220);
x_2222 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_2218);
lean_inc(x_9);
lean_inc(x_1);
x_2223 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_2222, x_2214, x_2215, x_2218, x_2218, x_2221, x_2216, lean_box(0), lean_box(0), x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_2213);
if (lean_obj_tag(x_2223) == 0)
{
lean_object* x_2224; lean_object* x_2225; uint8_t x_2226; 
x_2224 = lean_ctor_get(x_2223, 0);
lean_inc(x_2224);
x_2225 = lean_ctor_get(x_2224, 1);
lean_inc(x_2225);
x_2226 = lean_unbox(x_2225);
lean_dec(x_2225);
if (x_2226 == 0)
{
uint8_t x_2227; 
lean_dec(x_2224);
lean_dec(x_9);
x_2227 = !lean_is_exclusive(x_2223);
if (x_2227 == 0)
{
lean_object* x_2228; 
x_2228 = lean_ctor_get(x_2223, 0);
lean_dec(x_2228);
lean_ctor_set(x_2223, 0, x_1);
return x_2223;
}
else
{
lean_object* x_2229; lean_object* x_2230; 
x_2229 = lean_ctor_get(x_2223, 1);
lean_inc(x_2229);
lean_dec(x_2223);
x_2230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2230, 0, x_1);
lean_ctor_set(x_2230, 1, x_2229);
return x_2230;
}
}
else
{
uint8_t x_2231; 
lean_dec(x_1);
x_2231 = !lean_is_exclusive(x_2223);
if (x_2231 == 0)
{
lean_object* x_2232; lean_object* x_2233; lean_object* x_2234; 
x_2232 = lean_ctor_get(x_2223, 0);
lean_dec(x_2232);
x_2233 = lean_ctor_get(x_2224, 0);
lean_inc(x_2233);
lean_dec(x_2224);
x_2234 = l_Lean_mkAppN(x_9, x_2233);
lean_dec(x_2233);
lean_ctor_set(x_2223, 0, x_2234);
return x_2223;
}
else
{
lean_object* x_2235; lean_object* x_2236; lean_object* x_2237; lean_object* x_2238; 
x_2235 = lean_ctor_get(x_2223, 1);
lean_inc(x_2235);
lean_dec(x_2223);
x_2236 = lean_ctor_get(x_2224, 0);
lean_inc(x_2236);
lean_dec(x_2224);
x_2237 = l_Lean_mkAppN(x_9, x_2236);
lean_dec(x_2236);
x_2238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2238, 0, x_2237);
lean_ctor_set(x_2238, 1, x_2235);
return x_2238;
}
}
}
else
{
uint8_t x_2239; 
lean_dec(x_9);
lean_dec(x_1);
x_2239 = !lean_is_exclusive(x_2223);
if (x_2239 == 0)
{
return x_2223;
}
else
{
lean_object* x_2240; lean_object* x_2241; lean_object* x_2242; 
x_2240 = lean_ctor_get(x_2223, 0);
x_2241 = lean_ctor_get(x_2223, 1);
lean_inc(x_2241);
lean_inc(x_2240);
lean_dec(x_2223);
x_2242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2242, 0, x_2240);
lean_ctor_set(x_2242, 1, x_2241);
return x_2242;
}
}
}
else
{
uint8_t x_2243; 
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
x_2243 = !lean_is_exclusive(x_2211);
if (x_2243 == 0)
{
return x_2211;
}
else
{
lean_object* x_2244; lean_object* x_2245; lean_object* x_2246; 
x_2244 = lean_ctor_get(x_2211, 0);
x_2245 = lean_ctor_get(x_2211, 1);
lean_inc(x_2245);
lean_inc(x_2244);
lean_dec(x_2211);
x_2246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2246, 0, x_2244);
lean_ctor_set(x_2246, 1, x_2245);
return x_2246;
}
}
}
}
case 10:
{
lean_object* x_2260; lean_object* x_2458; lean_object* x_2496; uint8_t x_2497; 
lean_dec(x_11);
x_2496 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_2497 = l_Lean_Expr_isConstOf(x_9, x_2496);
if (x_2497 == 0)
{
lean_object* x_2498; 
x_2498 = lean_box(0);
x_2458 = x_2498;
goto block_2495;
}
else
{
lean_object* x_2499; lean_object* x_2500; uint8_t x_2501; 
x_2499 = lean_array_get_size(x_10);
x_2500 = lean_unsigned_to_nat(2u);
x_2501 = lean_nat_dec_eq(x_2499, x_2500);
if (x_2501 == 0)
{
lean_object* x_2502; 
lean_dec(x_2499);
x_2502 = lean_box(0);
x_2458 = x_2502;
goto block_2495;
}
else
{
lean_object* x_2503; uint8_t x_2504; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2503 = lean_unsigned_to_nat(0u);
x_2504 = lean_nat_dec_lt(x_2503, x_2499);
lean_dec(x_2499);
if (x_2504 == 0)
{
lean_object* x_2505; lean_object* x_2506; 
x_2505 = l_Lean_instInhabitedExpr;
x_2506 = l_outOfBounds___rarg(x_2505);
x_2260 = x_2506;
goto block_2457;
}
else
{
lean_object* x_2507; 
x_2507 = lean_array_fget(x_10, x_2503);
x_2260 = x_2507;
goto block_2457;
}
}
}
block_2457:
{
lean_object* x_2261; 
lean_inc(x_13);
lean_inc(x_2260);
x_2261 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_2260, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_2261) == 0)
{
lean_object* x_2262; lean_object* x_2263; lean_object* x_2264; uint8_t x_2265; 
x_2262 = lean_ctor_get(x_2261, 0);
lean_inc(x_2262);
x_2263 = lean_ctor_get(x_2261, 1);
lean_inc(x_2263);
lean_dec(x_2261);
x_2264 = lean_st_ref_get(x_13, x_2263);
x_2265 = !lean_is_exclusive(x_2264);
if (x_2265 == 0)
{
lean_object* x_2266; lean_object* x_2267; lean_object* x_2268; lean_object* x_2269; lean_object* x_2270; 
x_2266 = lean_ctor_get(x_2264, 0);
x_2267 = lean_ctor_get(x_2264, 1);
x_2268 = lean_ctor_get(x_2266, 1);
lean_inc(x_2268);
lean_dec(x_2266);
x_2269 = lean_ctor_get(x_2268, 2);
lean_inc(x_2269);
lean_dec(x_2268);
x_2270 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_2269, x_2262);
if (lean_obj_tag(x_2270) == 0)
{
size_t x_2271; size_t x_2272; uint8_t x_2273; 
lean_free_object(x_2264);
x_2271 = lean_ptr_addr(x_2260);
lean_dec(x_2260);
x_2272 = lean_ptr_addr(x_2262);
x_2273 = lean_usize_dec_eq(x_2271, x_2272);
if (x_2273 == 0)
{
lean_object* x_2274; lean_object* x_2275; lean_object* x_2276; lean_object* x_2277; lean_object* x_2278; lean_object* x_2279; lean_object* x_2280; lean_object* x_2281; lean_object* x_2282; lean_object* x_2283; lean_object* x_2284; lean_object* x_2285; lean_object* x_2286; lean_object* x_2287; lean_object* x_2288; lean_object* x_2289; lean_object* x_2290; lean_object* x_2291; uint8_t x_2292; lean_object* x_2293; lean_object* x_2294; lean_object* x_2295; lean_object* x_2296; lean_object* x_2297; lean_object* x_2298; lean_object* x_2299; lean_object* x_2300; lean_object* x_2301; lean_object* x_2302; lean_object* x_2303; lean_object* x_2304; lean_object* x_2305; lean_object* x_2306; lean_object* x_2307; lean_object* x_2308; lean_object* x_2309; lean_object* x_2310; lean_object* x_2311; lean_object* x_2312; lean_object* x_2313; uint8_t x_2314; 
lean_dec(x_1);
x_2274 = lean_unsigned_to_nat(0u);
lean_inc(x_2262);
x_2275 = lean_array_set(x_10, x_2274, x_2262);
x_2276 = l_Lean_mkAppN(x_9, x_2275);
lean_dec(x_2275);
x_2277 = lean_st_ref_take(x_13, x_2267);
x_2278 = lean_ctor_get(x_2277, 0);
lean_inc(x_2278);
x_2279 = lean_ctor_get(x_2277, 1);
lean_inc(x_2279);
lean_dec(x_2277);
x_2280 = lean_ctor_get(x_2278, 0);
lean_inc(x_2280);
x_2281 = lean_ctor_get(x_2278, 1);
lean_inc(x_2281);
x_2282 = lean_ctor_get(x_2281, 0);
lean_inc(x_2282);
x_2283 = lean_ctor_get(x_2281, 1);
lean_inc(x_2283);
x_2284 = lean_ctor_get(x_2281, 2);
lean_inc(x_2284);
lean_dec(x_2281);
lean_inc(x_2276);
x_2285 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_2284, x_2262, x_2276);
x_2286 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2286, 0, x_2282);
lean_ctor_set(x_2286, 1, x_2283);
lean_ctor_set(x_2286, 2, x_2285);
x_2287 = lean_ctor_get(x_2278, 2);
lean_inc(x_2287);
x_2288 = lean_ctor_get(x_2278, 3);
lean_inc(x_2288);
x_2289 = lean_ctor_get(x_2278, 4);
lean_inc(x_2289);
x_2290 = lean_ctor_get(x_2278, 5);
lean_inc(x_2290);
x_2291 = lean_ctor_get(x_2278, 6);
lean_inc(x_2291);
x_2292 = lean_ctor_get_uint8(x_2278, sizeof(void*)*26);
x_2293 = lean_ctor_get(x_2278, 7);
lean_inc(x_2293);
x_2294 = lean_ctor_get(x_2278, 8);
lean_inc(x_2294);
x_2295 = lean_ctor_get(x_2278, 9);
lean_inc(x_2295);
x_2296 = lean_ctor_get(x_2278, 10);
lean_inc(x_2296);
x_2297 = lean_ctor_get(x_2278, 11);
lean_inc(x_2297);
x_2298 = lean_ctor_get(x_2278, 12);
lean_inc(x_2298);
x_2299 = lean_ctor_get(x_2278, 13);
lean_inc(x_2299);
x_2300 = lean_ctor_get(x_2278, 14);
lean_inc(x_2300);
x_2301 = lean_ctor_get(x_2278, 15);
lean_inc(x_2301);
x_2302 = lean_ctor_get(x_2278, 16);
lean_inc(x_2302);
x_2303 = lean_ctor_get(x_2278, 17);
lean_inc(x_2303);
x_2304 = lean_ctor_get(x_2278, 18);
lean_inc(x_2304);
x_2305 = lean_ctor_get(x_2278, 19);
lean_inc(x_2305);
x_2306 = lean_ctor_get(x_2278, 20);
lean_inc(x_2306);
x_2307 = lean_ctor_get(x_2278, 21);
lean_inc(x_2307);
x_2308 = lean_ctor_get(x_2278, 22);
lean_inc(x_2308);
x_2309 = lean_ctor_get(x_2278, 23);
lean_inc(x_2309);
x_2310 = lean_ctor_get(x_2278, 24);
lean_inc(x_2310);
x_2311 = lean_ctor_get(x_2278, 25);
lean_inc(x_2311);
lean_dec(x_2278);
x_2312 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_2312, 0, x_2280);
lean_ctor_set(x_2312, 1, x_2286);
lean_ctor_set(x_2312, 2, x_2287);
lean_ctor_set(x_2312, 3, x_2288);
lean_ctor_set(x_2312, 4, x_2289);
lean_ctor_set(x_2312, 5, x_2290);
lean_ctor_set(x_2312, 6, x_2291);
lean_ctor_set(x_2312, 7, x_2293);
lean_ctor_set(x_2312, 8, x_2294);
lean_ctor_set(x_2312, 9, x_2295);
lean_ctor_set(x_2312, 10, x_2296);
lean_ctor_set(x_2312, 11, x_2297);
lean_ctor_set(x_2312, 12, x_2298);
lean_ctor_set(x_2312, 13, x_2299);
lean_ctor_set(x_2312, 14, x_2300);
lean_ctor_set(x_2312, 15, x_2301);
lean_ctor_set(x_2312, 16, x_2302);
lean_ctor_set(x_2312, 17, x_2303);
lean_ctor_set(x_2312, 18, x_2304);
lean_ctor_set(x_2312, 19, x_2305);
lean_ctor_set(x_2312, 20, x_2306);
lean_ctor_set(x_2312, 21, x_2307);
lean_ctor_set(x_2312, 22, x_2308);
lean_ctor_set(x_2312, 23, x_2309);
lean_ctor_set(x_2312, 24, x_2310);
lean_ctor_set(x_2312, 25, x_2311);
lean_ctor_set_uint8(x_2312, sizeof(void*)*26, x_2292);
x_2313 = lean_st_ref_set(x_13, x_2312, x_2279);
lean_dec(x_13);
x_2314 = !lean_is_exclusive(x_2313);
if (x_2314 == 0)
{
lean_object* x_2315; 
x_2315 = lean_ctor_get(x_2313, 0);
lean_dec(x_2315);
lean_ctor_set(x_2313, 0, x_2276);
return x_2313;
}
else
{
lean_object* x_2316; lean_object* x_2317; 
x_2316 = lean_ctor_get(x_2313, 1);
lean_inc(x_2316);
lean_dec(x_2313);
x_2317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2317, 0, x_2276);
lean_ctor_set(x_2317, 1, x_2316);
return x_2317;
}
}
else
{
lean_object* x_2318; lean_object* x_2319; lean_object* x_2320; lean_object* x_2321; lean_object* x_2322; lean_object* x_2323; lean_object* x_2324; lean_object* x_2325; lean_object* x_2326; lean_object* x_2327; lean_object* x_2328; lean_object* x_2329; lean_object* x_2330; lean_object* x_2331; lean_object* x_2332; uint8_t x_2333; lean_object* x_2334; lean_object* x_2335; lean_object* x_2336; lean_object* x_2337; lean_object* x_2338; lean_object* x_2339; lean_object* x_2340; lean_object* x_2341; lean_object* x_2342; lean_object* x_2343; lean_object* x_2344; lean_object* x_2345; lean_object* x_2346; lean_object* x_2347; lean_object* x_2348; lean_object* x_2349; lean_object* x_2350; lean_object* x_2351; lean_object* x_2352; lean_object* x_2353; lean_object* x_2354; uint8_t x_2355; 
lean_dec(x_10);
lean_dec(x_9);
x_2318 = lean_st_ref_take(x_13, x_2267);
x_2319 = lean_ctor_get(x_2318, 0);
lean_inc(x_2319);
x_2320 = lean_ctor_get(x_2318, 1);
lean_inc(x_2320);
lean_dec(x_2318);
x_2321 = lean_ctor_get(x_2319, 0);
lean_inc(x_2321);
x_2322 = lean_ctor_get(x_2319, 1);
lean_inc(x_2322);
x_2323 = lean_ctor_get(x_2322, 0);
lean_inc(x_2323);
x_2324 = lean_ctor_get(x_2322, 1);
lean_inc(x_2324);
x_2325 = lean_ctor_get(x_2322, 2);
lean_inc(x_2325);
lean_dec(x_2322);
lean_inc(x_1);
x_2326 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_2325, x_2262, x_1);
x_2327 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2327, 0, x_2323);
lean_ctor_set(x_2327, 1, x_2324);
lean_ctor_set(x_2327, 2, x_2326);
x_2328 = lean_ctor_get(x_2319, 2);
lean_inc(x_2328);
x_2329 = lean_ctor_get(x_2319, 3);
lean_inc(x_2329);
x_2330 = lean_ctor_get(x_2319, 4);
lean_inc(x_2330);
x_2331 = lean_ctor_get(x_2319, 5);
lean_inc(x_2331);
x_2332 = lean_ctor_get(x_2319, 6);
lean_inc(x_2332);
x_2333 = lean_ctor_get_uint8(x_2319, sizeof(void*)*26);
x_2334 = lean_ctor_get(x_2319, 7);
lean_inc(x_2334);
x_2335 = lean_ctor_get(x_2319, 8);
lean_inc(x_2335);
x_2336 = lean_ctor_get(x_2319, 9);
lean_inc(x_2336);
x_2337 = lean_ctor_get(x_2319, 10);
lean_inc(x_2337);
x_2338 = lean_ctor_get(x_2319, 11);
lean_inc(x_2338);
x_2339 = lean_ctor_get(x_2319, 12);
lean_inc(x_2339);
x_2340 = lean_ctor_get(x_2319, 13);
lean_inc(x_2340);
x_2341 = lean_ctor_get(x_2319, 14);
lean_inc(x_2341);
x_2342 = lean_ctor_get(x_2319, 15);
lean_inc(x_2342);
x_2343 = lean_ctor_get(x_2319, 16);
lean_inc(x_2343);
x_2344 = lean_ctor_get(x_2319, 17);
lean_inc(x_2344);
x_2345 = lean_ctor_get(x_2319, 18);
lean_inc(x_2345);
x_2346 = lean_ctor_get(x_2319, 19);
lean_inc(x_2346);
x_2347 = lean_ctor_get(x_2319, 20);
lean_inc(x_2347);
x_2348 = lean_ctor_get(x_2319, 21);
lean_inc(x_2348);
x_2349 = lean_ctor_get(x_2319, 22);
lean_inc(x_2349);
x_2350 = lean_ctor_get(x_2319, 23);
lean_inc(x_2350);
x_2351 = lean_ctor_get(x_2319, 24);
lean_inc(x_2351);
x_2352 = lean_ctor_get(x_2319, 25);
lean_inc(x_2352);
lean_dec(x_2319);
x_2353 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_2353, 0, x_2321);
lean_ctor_set(x_2353, 1, x_2327);
lean_ctor_set(x_2353, 2, x_2328);
lean_ctor_set(x_2353, 3, x_2329);
lean_ctor_set(x_2353, 4, x_2330);
lean_ctor_set(x_2353, 5, x_2331);
lean_ctor_set(x_2353, 6, x_2332);
lean_ctor_set(x_2353, 7, x_2334);
lean_ctor_set(x_2353, 8, x_2335);
lean_ctor_set(x_2353, 9, x_2336);
lean_ctor_set(x_2353, 10, x_2337);
lean_ctor_set(x_2353, 11, x_2338);
lean_ctor_set(x_2353, 12, x_2339);
lean_ctor_set(x_2353, 13, x_2340);
lean_ctor_set(x_2353, 14, x_2341);
lean_ctor_set(x_2353, 15, x_2342);
lean_ctor_set(x_2353, 16, x_2343);
lean_ctor_set(x_2353, 17, x_2344);
lean_ctor_set(x_2353, 18, x_2345);
lean_ctor_set(x_2353, 19, x_2346);
lean_ctor_set(x_2353, 20, x_2347);
lean_ctor_set(x_2353, 21, x_2348);
lean_ctor_set(x_2353, 22, x_2349);
lean_ctor_set(x_2353, 23, x_2350);
lean_ctor_set(x_2353, 24, x_2351);
lean_ctor_set(x_2353, 25, x_2352);
lean_ctor_set_uint8(x_2353, sizeof(void*)*26, x_2333);
x_2354 = lean_st_ref_set(x_13, x_2353, x_2320);
lean_dec(x_13);
x_2355 = !lean_is_exclusive(x_2354);
if (x_2355 == 0)
{
lean_object* x_2356; 
x_2356 = lean_ctor_get(x_2354, 0);
lean_dec(x_2356);
lean_ctor_set(x_2354, 0, x_1);
return x_2354;
}
else
{
lean_object* x_2357; lean_object* x_2358; 
x_2357 = lean_ctor_get(x_2354, 1);
lean_inc(x_2357);
lean_dec(x_2354);
x_2358 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2358, 0, x_1);
lean_ctor_set(x_2358, 1, x_2357);
return x_2358;
}
}
}
else
{
lean_object* x_2359; 
lean_dec(x_2262);
lean_dec(x_2260);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_2359 = lean_ctor_get(x_2270, 0);
lean_inc(x_2359);
lean_dec(x_2270);
lean_ctor_set(x_2264, 0, x_2359);
return x_2264;
}
}
else
{
lean_object* x_2360; lean_object* x_2361; lean_object* x_2362; lean_object* x_2363; lean_object* x_2364; 
x_2360 = lean_ctor_get(x_2264, 0);
x_2361 = lean_ctor_get(x_2264, 1);
lean_inc(x_2361);
lean_inc(x_2360);
lean_dec(x_2264);
x_2362 = lean_ctor_get(x_2360, 1);
lean_inc(x_2362);
lean_dec(x_2360);
x_2363 = lean_ctor_get(x_2362, 2);
lean_inc(x_2363);
lean_dec(x_2362);
x_2364 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_2363, x_2262);
if (lean_obj_tag(x_2364) == 0)
{
size_t x_2365; size_t x_2366; uint8_t x_2367; 
x_2365 = lean_ptr_addr(x_2260);
lean_dec(x_2260);
x_2366 = lean_ptr_addr(x_2262);
x_2367 = lean_usize_dec_eq(x_2365, x_2366);
if (x_2367 == 0)
{
lean_object* x_2368; lean_object* x_2369; lean_object* x_2370; lean_object* x_2371; lean_object* x_2372; lean_object* x_2373; lean_object* x_2374; lean_object* x_2375; lean_object* x_2376; lean_object* x_2377; lean_object* x_2378; lean_object* x_2379; lean_object* x_2380; lean_object* x_2381; lean_object* x_2382; lean_object* x_2383; lean_object* x_2384; lean_object* x_2385; uint8_t x_2386; lean_object* x_2387; lean_object* x_2388; lean_object* x_2389; lean_object* x_2390; lean_object* x_2391; lean_object* x_2392; lean_object* x_2393; lean_object* x_2394; lean_object* x_2395; lean_object* x_2396; lean_object* x_2397; lean_object* x_2398; lean_object* x_2399; lean_object* x_2400; lean_object* x_2401; lean_object* x_2402; lean_object* x_2403; lean_object* x_2404; lean_object* x_2405; lean_object* x_2406; lean_object* x_2407; lean_object* x_2408; lean_object* x_2409; lean_object* x_2410; 
lean_dec(x_1);
x_2368 = lean_unsigned_to_nat(0u);
lean_inc(x_2262);
x_2369 = lean_array_set(x_10, x_2368, x_2262);
x_2370 = l_Lean_mkAppN(x_9, x_2369);
lean_dec(x_2369);
x_2371 = lean_st_ref_take(x_13, x_2361);
x_2372 = lean_ctor_get(x_2371, 0);
lean_inc(x_2372);
x_2373 = lean_ctor_get(x_2371, 1);
lean_inc(x_2373);
lean_dec(x_2371);
x_2374 = lean_ctor_get(x_2372, 0);
lean_inc(x_2374);
x_2375 = lean_ctor_get(x_2372, 1);
lean_inc(x_2375);
x_2376 = lean_ctor_get(x_2375, 0);
lean_inc(x_2376);
x_2377 = lean_ctor_get(x_2375, 1);
lean_inc(x_2377);
x_2378 = lean_ctor_get(x_2375, 2);
lean_inc(x_2378);
lean_dec(x_2375);
lean_inc(x_2370);
x_2379 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_2378, x_2262, x_2370);
x_2380 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2380, 0, x_2376);
lean_ctor_set(x_2380, 1, x_2377);
lean_ctor_set(x_2380, 2, x_2379);
x_2381 = lean_ctor_get(x_2372, 2);
lean_inc(x_2381);
x_2382 = lean_ctor_get(x_2372, 3);
lean_inc(x_2382);
x_2383 = lean_ctor_get(x_2372, 4);
lean_inc(x_2383);
x_2384 = lean_ctor_get(x_2372, 5);
lean_inc(x_2384);
x_2385 = lean_ctor_get(x_2372, 6);
lean_inc(x_2385);
x_2386 = lean_ctor_get_uint8(x_2372, sizeof(void*)*26);
x_2387 = lean_ctor_get(x_2372, 7);
lean_inc(x_2387);
x_2388 = lean_ctor_get(x_2372, 8);
lean_inc(x_2388);
x_2389 = lean_ctor_get(x_2372, 9);
lean_inc(x_2389);
x_2390 = lean_ctor_get(x_2372, 10);
lean_inc(x_2390);
x_2391 = lean_ctor_get(x_2372, 11);
lean_inc(x_2391);
x_2392 = lean_ctor_get(x_2372, 12);
lean_inc(x_2392);
x_2393 = lean_ctor_get(x_2372, 13);
lean_inc(x_2393);
x_2394 = lean_ctor_get(x_2372, 14);
lean_inc(x_2394);
x_2395 = lean_ctor_get(x_2372, 15);
lean_inc(x_2395);
x_2396 = lean_ctor_get(x_2372, 16);
lean_inc(x_2396);
x_2397 = lean_ctor_get(x_2372, 17);
lean_inc(x_2397);
x_2398 = lean_ctor_get(x_2372, 18);
lean_inc(x_2398);
x_2399 = lean_ctor_get(x_2372, 19);
lean_inc(x_2399);
x_2400 = lean_ctor_get(x_2372, 20);
lean_inc(x_2400);
x_2401 = lean_ctor_get(x_2372, 21);
lean_inc(x_2401);
x_2402 = lean_ctor_get(x_2372, 22);
lean_inc(x_2402);
x_2403 = lean_ctor_get(x_2372, 23);
lean_inc(x_2403);
x_2404 = lean_ctor_get(x_2372, 24);
lean_inc(x_2404);
x_2405 = lean_ctor_get(x_2372, 25);
lean_inc(x_2405);
lean_dec(x_2372);
x_2406 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_2406, 0, x_2374);
lean_ctor_set(x_2406, 1, x_2380);
lean_ctor_set(x_2406, 2, x_2381);
lean_ctor_set(x_2406, 3, x_2382);
lean_ctor_set(x_2406, 4, x_2383);
lean_ctor_set(x_2406, 5, x_2384);
lean_ctor_set(x_2406, 6, x_2385);
lean_ctor_set(x_2406, 7, x_2387);
lean_ctor_set(x_2406, 8, x_2388);
lean_ctor_set(x_2406, 9, x_2389);
lean_ctor_set(x_2406, 10, x_2390);
lean_ctor_set(x_2406, 11, x_2391);
lean_ctor_set(x_2406, 12, x_2392);
lean_ctor_set(x_2406, 13, x_2393);
lean_ctor_set(x_2406, 14, x_2394);
lean_ctor_set(x_2406, 15, x_2395);
lean_ctor_set(x_2406, 16, x_2396);
lean_ctor_set(x_2406, 17, x_2397);
lean_ctor_set(x_2406, 18, x_2398);
lean_ctor_set(x_2406, 19, x_2399);
lean_ctor_set(x_2406, 20, x_2400);
lean_ctor_set(x_2406, 21, x_2401);
lean_ctor_set(x_2406, 22, x_2402);
lean_ctor_set(x_2406, 23, x_2403);
lean_ctor_set(x_2406, 24, x_2404);
lean_ctor_set(x_2406, 25, x_2405);
lean_ctor_set_uint8(x_2406, sizeof(void*)*26, x_2386);
x_2407 = lean_st_ref_set(x_13, x_2406, x_2373);
lean_dec(x_13);
x_2408 = lean_ctor_get(x_2407, 1);
lean_inc(x_2408);
if (lean_is_exclusive(x_2407)) {
 lean_ctor_release(x_2407, 0);
 lean_ctor_release(x_2407, 1);
 x_2409 = x_2407;
} else {
 lean_dec_ref(x_2407);
 x_2409 = lean_box(0);
}
if (lean_is_scalar(x_2409)) {
 x_2410 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2410 = x_2409;
}
lean_ctor_set(x_2410, 0, x_2370);
lean_ctor_set(x_2410, 1, x_2408);
return x_2410;
}
else
{
lean_object* x_2411; lean_object* x_2412; lean_object* x_2413; lean_object* x_2414; lean_object* x_2415; lean_object* x_2416; lean_object* x_2417; lean_object* x_2418; lean_object* x_2419; lean_object* x_2420; lean_object* x_2421; lean_object* x_2422; lean_object* x_2423; lean_object* x_2424; lean_object* x_2425; uint8_t x_2426; lean_object* x_2427; lean_object* x_2428; lean_object* x_2429; lean_object* x_2430; lean_object* x_2431; lean_object* x_2432; lean_object* x_2433; lean_object* x_2434; lean_object* x_2435; lean_object* x_2436; lean_object* x_2437; lean_object* x_2438; lean_object* x_2439; lean_object* x_2440; lean_object* x_2441; lean_object* x_2442; lean_object* x_2443; lean_object* x_2444; lean_object* x_2445; lean_object* x_2446; lean_object* x_2447; lean_object* x_2448; lean_object* x_2449; lean_object* x_2450; 
lean_dec(x_10);
lean_dec(x_9);
x_2411 = lean_st_ref_take(x_13, x_2361);
x_2412 = lean_ctor_get(x_2411, 0);
lean_inc(x_2412);
x_2413 = lean_ctor_get(x_2411, 1);
lean_inc(x_2413);
lean_dec(x_2411);
x_2414 = lean_ctor_get(x_2412, 0);
lean_inc(x_2414);
x_2415 = lean_ctor_get(x_2412, 1);
lean_inc(x_2415);
x_2416 = lean_ctor_get(x_2415, 0);
lean_inc(x_2416);
x_2417 = lean_ctor_get(x_2415, 1);
lean_inc(x_2417);
x_2418 = lean_ctor_get(x_2415, 2);
lean_inc(x_2418);
lean_dec(x_2415);
lean_inc(x_1);
x_2419 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_2418, x_2262, x_1);
x_2420 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2420, 0, x_2416);
lean_ctor_set(x_2420, 1, x_2417);
lean_ctor_set(x_2420, 2, x_2419);
x_2421 = lean_ctor_get(x_2412, 2);
lean_inc(x_2421);
x_2422 = lean_ctor_get(x_2412, 3);
lean_inc(x_2422);
x_2423 = lean_ctor_get(x_2412, 4);
lean_inc(x_2423);
x_2424 = lean_ctor_get(x_2412, 5);
lean_inc(x_2424);
x_2425 = lean_ctor_get(x_2412, 6);
lean_inc(x_2425);
x_2426 = lean_ctor_get_uint8(x_2412, sizeof(void*)*26);
x_2427 = lean_ctor_get(x_2412, 7);
lean_inc(x_2427);
x_2428 = lean_ctor_get(x_2412, 8);
lean_inc(x_2428);
x_2429 = lean_ctor_get(x_2412, 9);
lean_inc(x_2429);
x_2430 = lean_ctor_get(x_2412, 10);
lean_inc(x_2430);
x_2431 = lean_ctor_get(x_2412, 11);
lean_inc(x_2431);
x_2432 = lean_ctor_get(x_2412, 12);
lean_inc(x_2432);
x_2433 = lean_ctor_get(x_2412, 13);
lean_inc(x_2433);
x_2434 = lean_ctor_get(x_2412, 14);
lean_inc(x_2434);
x_2435 = lean_ctor_get(x_2412, 15);
lean_inc(x_2435);
x_2436 = lean_ctor_get(x_2412, 16);
lean_inc(x_2436);
x_2437 = lean_ctor_get(x_2412, 17);
lean_inc(x_2437);
x_2438 = lean_ctor_get(x_2412, 18);
lean_inc(x_2438);
x_2439 = lean_ctor_get(x_2412, 19);
lean_inc(x_2439);
x_2440 = lean_ctor_get(x_2412, 20);
lean_inc(x_2440);
x_2441 = lean_ctor_get(x_2412, 21);
lean_inc(x_2441);
x_2442 = lean_ctor_get(x_2412, 22);
lean_inc(x_2442);
x_2443 = lean_ctor_get(x_2412, 23);
lean_inc(x_2443);
x_2444 = lean_ctor_get(x_2412, 24);
lean_inc(x_2444);
x_2445 = lean_ctor_get(x_2412, 25);
lean_inc(x_2445);
lean_dec(x_2412);
x_2446 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_2446, 0, x_2414);
lean_ctor_set(x_2446, 1, x_2420);
lean_ctor_set(x_2446, 2, x_2421);
lean_ctor_set(x_2446, 3, x_2422);
lean_ctor_set(x_2446, 4, x_2423);
lean_ctor_set(x_2446, 5, x_2424);
lean_ctor_set(x_2446, 6, x_2425);
lean_ctor_set(x_2446, 7, x_2427);
lean_ctor_set(x_2446, 8, x_2428);
lean_ctor_set(x_2446, 9, x_2429);
lean_ctor_set(x_2446, 10, x_2430);
lean_ctor_set(x_2446, 11, x_2431);
lean_ctor_set(x_2446, 12, x_2432);
lean_ctor_set(x_2446, 13, x_2433);
lean_ctor_set(x_2446, 14, x_2434);
lean_ctor_set(x_2446, 15, x_2435);
lean_ctor_set(x_2446, 16, x_2436);
lean_ctor_set(x_2446, 17, x_2437);
lean_ctor_set(x_2446, 18, x_2438);
lean_ctor_set(x_2446, 19, x_2439);
lean_ctor_set(x_2446, 20, x_2440);
lean_ctor_set(x_2446, 21, x_2441);
lean_ctor_set(x_2446, 22, x_2442);
lean_ctor_set(x_2446, 23, x_2443);
lean_ctor_set(x_2446, 24, x_2444);
lean_ctor_set(x_2446, 25, x_2445);
lean_ctor_set_uint8(x_2446, sizeof(void*)*26, x_2426);
x_2447 = lean_st_ref_set(x_13, x_2446, x_2413);
lean_dec(x_13);
x_2448 = lean_ctor_get(x_2447, 1);
lean_inc(x_2448);
if (lean_is_exclusive(x_2447)) {
 lean_ctor_release(x_2447, 0);
 lean_ctor_release(x_2447, 1);
 x_2449 = x_2447;
} else {
 lean_dec_ref(x_2447);
 x_2449 = lean_box(0);
}
if (lean_is_scalar(x_2449)) {
 x_2450 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2450 = x_2449;
}
lean_ctor_set(x_2450, 0, x_1);
lean_ctor_set(x_2450, 1, x_2448);
return x_2450;
}
}
else
{
lean_object* x_2451; lean_object* x_2452; 
lean_dec(x_2262);
lean_dec(x_2260);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_2451 = lean_ctor_get(x_2364, 0);
lean_inc(x_2451);
lean_dec(x_2364);
x_2452 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2452, 0, x_2451);
lean_ctor_set(x_2452, 1, x_2361);
return x_2452;
}
}
}
else
{
uint8_t x_2453; 
lean_dec(x_2260);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_2453 = !lean_is_exclusive(x_2261);
if (x_2453 == 0)
{
return x_2261;
}
else
{
lean_object* x_2454; lean_object* x_2455; lean_object* x_2456; 
x_2454 = lean_ctor_get(x_2261, 0);
x_2455 = lean_ctor_get(x_2261, 1);
lean_inc(x_2455);
lean_inc(x_2454);
lean_dec(x_2261);
x_2456 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2456, 0, x_2454);
lean_ctor_set(x_2456, 1, x_2455);
return x_2456;
}
}
}
block_2495:
{
lean_object* x_2459; 
lean_dec(x_2458);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_9);
x_2459 = l_Lean_Meta_getFunInfo(x_9, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_2459) == 0)
{
lean_object* x_2460; lean_object* x_2461; lean_object* x_2462; lean_object* x_2463; lean_object* x_2464; lean_object* x_2465; lean_object* x_2466; uint8_t x_2467; lean_object* x_2468; lean_object* x_2469; lean_object* x_2470; lean_object* x_2471; 
x_2460 = lean_ctor_get(x_2459, 0);
lean_inc(x_2460);
x_2461 = lean_ctor_get(x_2459, 1);
lean_inc(x_2461);
lean_dec(x_2459);
x_2462 = lean_ctor_get(x_2460, 0);
lean_inc(x_2462);
lean_dec(x_2460);
x_2463 = lean_array_get_size(x_10);
x_2464 = lean_unsigned_to_nat(0u);
x_2465 = lean_unsigned_to_nat(1u);
lean_inc(x_2463);
x_2466 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2466, 0, x_2464);
lean_ctor_set(x_2466, 1, x_2463);
lean_ctor_set(x_2466, 2, x_2465);
x_2467 = 0;
x_2468 = lean_box(x_2467);
lean_inc(x_10);
x_2469 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2469, 0, x_10);
lean_ctor_set(x_2469, 1, x_2468);
x_2470 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_2466);
lean_inc(x_9);
lean_inc(x_1);
x_2471 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_2470, x_2462, x_2463, x_2466, x_2466, x_2469, x_2464, lean_box(0), lean_box(0), x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_2461);
if (lean_obj_tag(x_2471) == 0)
{
lean_object* x_2472; lean_object* x_2473; uint8_t x_2474; 
x_2472 = lean_ctor_get(x_2471, 0);
lean_inc(x_2472);
x_2473 = lean_ctor_get(x_2472, 1);
lean_inc(x_2473);
x_2474 = lean_unbox(x_2473);
lean_dec(x_2473);
if (x_2474 == 0)
{
uint8_t x_2475; 
lean_dec(x_2472);
lean_dec(x_9);
x_2475 = !lean_is_exclusive(x_2471);
if (x_2475 == 0)
{
lean_object* x_2476; 
x_2476 = lean_ctor_get(x_2471, 0);
lean_dec(x_2476);
lean_ctor_set(x_2471, 0, x_1);
return x_2471;
}
else
{
lean_object* x_2477; lean_object* x_2478; 
x_2477 = lean_ctor_get(x_2471, 1);
lean_inc(x_2477);
lean_dec(x_2471);
x_2478 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2478, 0, x_1);
lean_ctor_set(x_2478, 1, x_2477);
return x_2478;
}
}
else
{
uint8_t x_2479; 
lean_dec(x_1);
x_2479 = !lean_is_exclusive(x_2471);
if (x_2479 == 0)
{
lean_object* x_2480; lean_object* x_2481; lean_object* x_2482; 
x_2480 = lean_ctor_get(x_2471, 0);
lean_dec(x_2480);
x_2481 = lean_ctor_get(x_2472, 0);
lean_inc(x_2481);
lean_dec(x_2472);
x_2482 = l_Lean_mkAppN(x_9, x_2481);
lean_dec(x_2481);
lean_ctor_set(x_2471, 0, x_2482);
return x_2471;
}
else
{
lean_object* x_2483; lean_object* x_2484; lean_object* x_2485; lean_object* x_2486; 
x_2483 = lean_ctor_get(x_2471, 1);
lean_inc(x_2483);
lean_dec(x_2471);
x_2484 = lean_ctor_get(x_2472, 0);
lean_inc(x_2484);
lean_dec(x_2472);
x_2485 = l_Lean_mkAppN(x_9, x_2484);
lean_dec(x_2484);
x_2486 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2486, 0, x_2485);
lean_ctor_set(x_2486, 1, x_2483);
return x_2486;
}
}
}
else
{
uint8_t x_2487; 
lean_dec(x_9);
lean_dec(x_1);
x_2487 = !lean_is_exclusive(x_2471);
if (x_2487 == 0)
{
return x_2471;
}
else
{
lean_object* x_2488; lean_object* x_2489; lean_object* x_2490; 
x_2488 = lean_ctor_get(x_2471, 0);
x_2489 = lean_ctor_get(x_2471, 1);
lean_inc(x_2489);
lean_inc(x_2488);
lean_dec(x_2471);
x_2490 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2490, 0, x_2488);
lean_ctor_set(x_2490, 1, x_2489);
return x_2490;
}
}
}
else
{
uint8_t x_2491; 
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
x_2491 = !lean_is_exclusive(x_2459);
if (x_2491 == 0)
{
return x_2459;
}
else
{
lean_object* x_2492; lean_object* x_2493; lean_object* x_2494; 
x_2492 = lean_ctor_get(x_2459, 0);
x_2493 = lean_ctor_get(x_2459, 1);
lean_inc(x_2493);
lean_inc(x_2492);
lean_dec(x_2459);
x_2494 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2494, 0, x_2492);
lean_ctor_set(x_2494, 1, x_2493);
return x_2494;
}
}
}
}
default: 
{
lean_object* x_2508; lean_object* x_2706; lean_object* x_2744; uint8_t x_2745; 
lean_dec(x_11);
x_2744 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_2745 = l_Lean_Expr_isConstOf(x_9, x_2744);
if (x_2745 == 0)
{
lean_object* x_2746; 
x_2746 = lean_box(0);
x_2706 = x_2746;
goto block_2743;
}
else
{
lean_object* x_2747; lean_object* x_2748; uint8_t x_2749; 
x_2747 = lean_array_get_size(x_10);
x_2748 = lean_unsigned_to_nat(2u);
x_2749 = lean_nat_dec_eq(x_2747, x_2748);
if (x_2749 == 0)
{
lean_object* x_2750; 
lean_dec(x_2747);
x_2750 = lean_box(0);
x_2706 = x_2750;
goto block_2743;
}
else
{
lean_object* x_2751; uint8_t x_2752; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2751 = lean_unsigned_to_nat(0u);
x_2752 = lean_nat_dec_lt(x_2751, x_2747);
lean_dec(x_2747);
if (x_2752 == 0)
{
lean_object* x_2753; lean_object* x_2754; 
x_2753 = l_Lean_instInhabitedExpr;
x_2754 = l_outOfBounds___rarg(x_2753);
x_2508 = x_2754;
goto block_2705;
}
else
{
lean_object* x_2755; 
x_2755 = lean_array_fget(x_10, x_2751);
x_2508 = x_2755;
goto block_2705;
}
}
}
block_2705:
{
lean_object* x_2509; 
lean_inc(x_13);
lean_inc(x_2508);
x_2509 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_2508, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_2509) == 0)
{
lean_object* x_2510; lean_object* x_2511; lean_object* x_2512; uint8_t x_2513; 
x_2510 = lean_ctor_get(x_2509, 0);
lean_inc(x_2510);
x_2511 = lean_ctor_get(x_2509, 1);
lean_inc(x_2511);
lean_dec(x_2509);
x_2512 = lean_st_ref_get(x_13, x_2511);
x_2513 = !lean_is_exclusive(x_2512);
if (x_2513 == 0)
{
lean_object* x_2514; lean_object* x_2515; lean_object* x_2516; lean_object* x_2517; lean_object* x_2518; 
x_2514 = lean_ctor_get(x_2512, 0);
x_2515 = lean_ctor_get(x_2512, 1);
x_2516 = lean_ctor_get(x_2514, 1);
lean_inc(x_2516);
lean_dec(x_2514);
x_2517 = lean_ctor_get(x_2516, 2);
lean_inc(x_2517);
lean_dec(x_2516);
x_2518 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_2517, x_2510);
if (lean_obj_tag(x_2518) == 0)
{
size_t x_2519; size_t x_2520; uint8_t x_2521; 
lean_free_object(x_2512);
x_2519 = lean_ptr_addr(x_2508);
lean_dec(x_2508);
x_2520 = lean_ptr_addr(x_2510);
x_2521 = lean_usize_dec_eq(x_2519, x_2520);
if (x_2521 == 0)
{
lean_object* x_2522; lean_object* x_2523; lean_object* x_2524; lean_object* x_2525; lean_object* x_2526; lean_object* x_2527; lean_object* x_2528; lean_object* x_2529; lean_object* x_2530; lean_object* x_2531; lean_object* x_2532; lean_object* x_2533; lean_object* x_2534; lean_object* x_2535; lean_object* x_2536; lean_object* x_2537; lean_object* x_2538; lean_object* x_2539; uint8_t x_2540; lean_object* x_2541; lean_object* x_2542; lean_object* x_2543; lean_object* x_2544; lean_object* x_2545; lean_object* x_2546; lean_object* x_2547; lean_object* x_2548; lean_object* x_2549; lean_object* x_2550; lean_object* x_2551; lean_object* x_2552; lean_object* x_2553; lean_object* x_2554; lean_object* x_2555; lean_object* x_2556; lean_object* x_2557; lean_object* x_2558; lean_object* x_2559; lean_object* x_2560; lean_object* x_2561; uint8_t x_2562; 
lean_dec(x_1);
x_2522 = lean_unsigned_to_nat(0u);
lean_inc(x_2510);
x_2523 = lean_array_set(x_10, x_2522, x_2510);
x_2524 = l_Lean_mkAppN(x_9, x_2523);
lean_dec(x_2523);
x_2525 = lean_st_ref_take(x_13, x_2515);
x_2526 = lean_ctor_get(x_2525, 0);
lean_inc(x_2526);
x_2527 = lean_ctor_get(x_2525, 1);
lean_inc(x_2527);
lean_dec(x_2525);
x_2528 = lean_ctor_get(x_2526, 0);
lean_inc(x_2528);
x_2529 = lean_ctor_get(x_2526, 1);
lean_inc(x_2529);
x_2530 = lean_ctor_get(x_2529, 0);
lean_inc(x_2530);
x_2531 = lean_ctor_get(x_2529, 1);
lean_inc(x_2531);
x_2532 = lean_ctor_get(x_2529, 2);
lean_inc(x_2532);
lean_dec(x_2529);
lean_inc(x_2524);
x_2533 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_2532, x_2510, x_2524);
x_2534 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2534, 0, x_2530);
lean_ctor_set(x_2534, 1, x_2531);
lean_ctor_set(x_2534, 2, x_2533);
x_2535 = lean_ctor_get(x_2526, 2);
lean_inc(x_2535);
x_2536 = lean_ctor_get(x_2526, 3);
lean_inc(x_2536);
x_2537 = lean_ctor_get(x_2526, 4);
lean_inc(x_2537);
x_2538 = lean_ctor_get(x_2526, 5);
lean_inc(x_2538);
x_2539 = lean_ctor_get(x_2526, 6);
lean_inc(x_2539);
x_2540 = lean_ctor_get_uint8(x_2526, sizeof(void*)*26);
x_2541 = lean_ctor_get(x_2526, 7);
lean_inc(x_2541);
x_2542 = lean_ctor_get(x_2526, 8);
lean_inc(x_2542);
x_2543 = lean_ctor_get(x_2526, 9);
lean_inc(x_2543);
x_2544 = lean_ctor_get(x_2526, 10);
lean_inc(x_2544);
x_2545 = lean_ctor_get(x_2526, 11);
lean_inc(x_2545);
x_2546 = lean_ctor_get(x_2526, 12);
lean_inc(x_2546);
x_2547 = lean_ctor_get(x_2526, 13);
lean_inc(x_2547);
x_2548 = lean_ctor_get(x_2526, 14);
lean_inc(x_2548);
x_2549 = lean_ctor_get(x_2526, 15);
lean_inc(x_2549);
x_2550 = lean_ctor_get(x_2526, 16);
lean_inc(x_2550);
x_2551 = lean_ctor_get(x_2526, 17);
lean_inc(x_2551);
x_2552 = lean_ctor_get(x_2526, 18);
lean_inc(x_2552);
x_2553 = lean_ctor_get(x_2526, 19);
lean_inc(x_2553);
x_2554 = lean_ctor_get(x_2526, 20);
lean_inc(x_2554);
x_2555 = lean_ctor_get(x_2526, 21);
lean_inc(x_2555);
x_2556 = lean_ctor_get(x_2526, 22);
lean_inc(x_2556);
x_2557 = lean_ctor_get(x_2526, 23);
lean_inc(x_2557);
x_2558 = lean_ctor_get(x_2526, 24);
lean_inc(x_2558);
x_2559 = lean_ctor_get(x_2526, 25);
lean_inc(x_2559);
lean_dec(x_2526);
x_2560 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_2560, 0, x_2528);
lean_ctor_set(x_2560, 1, x_2534);
lean_ctor_set(x_2560, 2, x_2535);
lean_ctor_set(x_2560, 3, x_2536);
lean_ctor_set(x_2560, 4, x_2537);
lean_ctor_set(x_2560, 5, x_2538);
lean_ctor_set(x_2560, 6, x_2539);
lean_ctor_set(x_2560, 7, x_2541);
lean_ctor_set(x_2560, 8, x_2542);
lean_ctor_set(x_2560, 9, x_2543);
lean_ctor_set(x_2560, 10, x_2544);
lean_ctor_set(x_2560, 11, x_2545);
lean_ctor_set(x_2560, 12, x_2546);
lean_ctor_set(x_2560, 13, x_2547);
lean_ctor_set(x_2560, 14, x_2548);
lean_ctor_set(x_2560, 15, x_2549);
lean_ctor_set(x_2560, 16, x_2550);
lean_ctor_set(x_2560, 17, x_2551);
lean_ctor_set(x_2560, 18, x_2552);
lean_ctor_set(x_2560, 19, x_2553);
lean_ctor_set(x_2560, 20, x_2554);
lean_ctor_set(x_2560, 21, x_2555);
lean_ctor_set(x_2560, 22, x_2556);
lean_ctor_set(x_2560, 23, x_2557);
lean_ctor_set(x_2560, 24, x_2558);
lean_ctor_set(x_2560, 25, x_2559);
lean_ctor_set_uint8(x_2560, sizeof(void*)*26, x_2540);
x_2561 = lean_st_ref_set(x_13, x_2560, x_2527);
lean_dec(x_13);
x_2562 = !lean_is_exclusive(x_2561);
if (x_2562 == 0)
{
lean_object* x_2563; 
x_2563 = lean_ctor_get(x_2561, 0);
lean_dec(x_2563);
lean_ctor_set(x_2561, 0, x_2524);
return x_2561;
}
else
{
lean_object* x_2564; lean_object* x_2565; 
x_2564 = lean_ctor_get(x_2561, 1);
lean_inc(x_2564);
lean_dec(x_2561);
x_2565 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2565, 0, x_2524);
lean_ctor_set(x_2565, 1, x_2564);
return x_2565;
}
}
else
{
lean_object* x_2566; lean_object* x_2567; lean_object* x_2568; lean_object* x_2569; lean_object* x_2570; lean_object* x_2571; lean_object* x_2572; lean_object* x_2573; lean_object* x_2574; lean_object* x_2575; lean_object* x_2576; lean_object* x_2577; lean_object* x_2578; lean_object* x_2579; lean_object* x_2580; uint8_t x_2581; lean_object* x_2582; lean_object* x_2583; lean_object* x_2584; lean_object* x_2585; lean_object* x_2586; lean_object* x_2587; lean_object* x_2588; lean_object* x_2589; lean_object* x_2590; lean_object* x_2591; lean_object* x_2592; lean_object* x_2593; lean_object* x_2594; lean_object* x_2595; lean_object* x_2596; lean_object* x_2597; lean_object* x_2598; lean_object* x_2599; lean_object* x_2600; lean_object* x_2601; lean_object* x_2602; uint8_t x_2603; 
lean_dec(x_10);
lean_dec(x_9);
x_2566 = lean_st_ref_take(x_13, x_2515);
x_2567 = lean_ctor_get(x_2566, 0);
lean_inc(x_2567);
x_2568 = lean_ctor_get(x_2566, 1);
lean_inc(x_2568);
lean_dec(x_2566);
x_2569 = lean_ctor_get(x_2567, 0);
lean_inc(x_2569);
x_2570 = lean_ctor_get(x_2567, 1);
lean_inc(x_2570);
x_2571 = lean_ctor_get(x_2570, 0);
lean_inc(x_2571);
x_2572 = lean_ctor_get(x_2570, 1);
lean_inc(x_2572);
x_2573 = lean_ctor_get(x_2570, 2);
lean_inc(x_2573);
lean_dec(x_2570);
lean_inc(x_1);
x_2574 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_2573, x_2510, x_1);
x_2575 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2575, 0, x_2571);
lean_ctor_set(x_2575, 1, x_2572);
lean_ctor_set(x_2575, 2, x_2574);
x_2576 = lean_ctor_get(x_2567, 2);
lean_inc(x_2576);
x_2577 = lean_ctor_get(x_2567, 3);
lean_inc(x_2577);
x_2578 = lean_ctor_get(x_2567, 4);
lean_inc(x_2578);
x_2579 = lean_ctor_get(x_2567, 5);
lean_inc(x_2579);
x_2580 = lean_ctor_get(x_2567, 6);
lean_inc(x_2580);
x_2581 = lean_ctor_get_uint8(x_2567, sizeof(void*)*26);
x_2582 = lean_ctor_get(x_2567, 7);
lean_inc(x_2582);
x_2583 = lean_ctor_get(x_2567, 8);
lean_inc(x_2583);
x_2584 = lean_ctor_get(x_2567, 9);
lean_inc(x_2584);
x_2585 = lean_ctor_get(x_2567, 10);
lean_inc(x_2585);
x_2586 = lean_ctor_get(x_2567, 11);
lean_inc(x_2586);
x_2587 = lean_ctor_get(x_2567, 12);
lean_inc(x_2587);
x_2588 = lean_ctor_get(x_2567, 13);
lean_inc(x_2588);
x_2589 = lean_ctor_get(x_2567, 14);
lean_inc(x_2589);
x_2590 = lean_ctor_get(x_2567, 15);
lean_inc(x_2590);
x_2591 = lean_ctor_get(x_2567, 16);
lean_inc(x_2591);
x_2592 = lean_ctor_get(x_2567, 17);
lean_inc(x_2592);
x_2593 = lean_ctor_get(x_2567, 18);
lean_inc(x_2593);
x_2594 = lean_ctor_get(x_2567, 19);
lean_inc(x_2594);
x_2595 = lean_ctor_get(x_2567, 20);
lean_inc(x_2595);
x_2596 = lean_ctor_get(x_2567, 21);
lean_inc(x_2596);
x_2597 = lean_ctor_get(x_2567, 22);
lean_inc(x_2597);
x_2598 = lean_ctor_get(x_2567, 23);
lean_inc(x_2598);
x_2599 = lean_ctor_get(x_2567, 24);
lean_inc(x_2599);
x_2600 = lean_ctor_get(x_2567, 25);
lean_inc(x_2600);
lean_dec(x_2567);
x_2601 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_2601, 0, x_2569);
lean_ctor_set(x_2601, 1, x_2575);
lean_ctor_set(x_2601, 2, x_2576);
lean_ctor_set(x_2601, 3, x_2577);
lean_ctor_set(x_2601, 4, x_2578);
lean_ctor_set(x_2601, 5, x_2579);
lean_ctor_set(x_2601, 6, x_2580);
lean_ctor_set(x_2601, 7, x_2582);
lean_ctor_set(x_2601, 8, x_2583);
lean_ctor_set(x_2601, 9, x_2584);
lean_ctor_set(x_2601, 10, x_2585);
lean_ctor_set(x_2601, 11, x_2586);
lean_ctor_set(x_2601, 12, x_2587);
lean_ctor_set(x_2601, 13, x_2588);
lean_ctor_set(x_2601, 14, x_2589);
lean_ctor_set(x_2601, 15, x_2590);
lean_ctor_set(x_2601, 16, x_2591);
lean_ctor_set(x_2601, 17, x_2592);
lean_ctor_set(x_2601, 18, x_2593);
lean_ctor_set(x_2601, 19, x_2594);
lean_ctor_set(x_2601, 20, x_2595);
lean_ctor_set(x_2601, 21, x_2596);
lean_ctor_set(x_2601, 22, x_2597);
lean_ctor_set(x_2601, 23, x_2598);
lean_ctor_set(x_2601, 24, x_2599);
lean_ctor_set(x_2601, 25, x_2600);
lean_ctor_set_uint8(x_2601, sizeof(void*)*26, x_2581);
x_2602 = lean_st_ref_set(x_13, x_2601, x_2568);
lean_dec(x_13);
x_2603 = !lean_is_exclusive(x_2602);
if (x_2603 == 0)
{
lean_object* x_2604; 
x_2604 = lean_ctor_get(x_2602, 0);
lean_dec(x_2604);
lean_ctor_set(x_2602, 0, x_1);
return x_2602;
}
else
{
lean_object* x_2605; lean_object* x_2606; 
x_2605 = lean_ctor_get(x_2602, 1);
lean_inc(x_2605);
lean_dec(x_2602);
x_2606 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2606, 0, x_1);
lean_ctor_set(x_2606, 1, x_2605);
return x_2606;
}
}
}
else
{
lean_object* x_2607; 
lean_dec(x_2510);
lean_dec(x_2508);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_2607 = lean_ctor_get(x_2518, 0);
lean_inc(x_2607);
lean_dec(x_2518);
lean_ctor_set(x_2512, 0, x_2607);
return x_2512;
}
}
else
{
lean_object* x_2608; lean_object* x_2609; lean_object* x_2610; lean_object* x_2611; lean_object* x_2612; 
x_2608 = lean_ctor_get(x_2512, 0);
x_2609 = lean_ctor_get(x_2512, 1);
lean_inc(x_2609);
lean_inc(x_2608);
lean_dec(x_2512);
x_2610 = lean_ctor_get(x_2608, 1);
lean_inc(x_2610);
lean_dec(x_2608);
x_2611 = lean_ctor_get(x_2610, 2);
lean_inc(x_2611);
lean_dec(x_2610);
x_2612 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_2611, x_2510);
if (lean_obj_tag(x_2612) == 0)
{
size_t x_2613; size_t x_2614; uint8_t x_2615; 
x_2613 = lean_ptr_addr(x_2508);
lean_dec(x_2508);
x_2614 = lean_ptr_addr(x_2510);
x_2615 = lean_usize_dec_eq(x_2613, x_2614);
if (x_2615 == 0)
{
lean_object* x_2616; lean_object* x_2617; lean_object* x_2618; lean_object* x_2619; lean_object* x_2620; lean_object* x_2621; lean_object* x_2622; lean_object* x_2623; lean_object* x_2624; lean_object* x_2625; lean_object* x_2626; lean_object* x_2627; lean_object* x_2628; lean_object* x_2629; lean_object* x_2630; lean_object* x_2631; lean_object* x_2632; lean_object* x_2633; uint8_t x_2634; lean_object* x_2635; lean_object* x_2636; lean_object* x_2637; lean_object* x_2638; lean_object* x_2639; lean_object* x_2640; lean_object* x_2641; lean_object* x_2642; lean_object* x_2643; lean_object* x_2644; lean_object* x_2645; lean_object* x_2646; lean_object* x_2647; lean_object* x_2648; lean_object* x_2649; lean_object* x_2650; lean_object* x_2651; lean_object* x_2652; lean_object* x_2653; lean_object* x_2654; lean_object* x_2655; lean_object* x_2656; lean_object* x_2657; lean_object* x_2658; 
lean_dec(x_1);
x_2616 = lean_unsigned_to_nat(0u);
lean_inc(x_2510);
x_2617 = lean_array_set(x_10, x_2616, x_2510);
x_2618 = l_Lean_mkAppN(x_9, x_2617);
lean_dec(x_2617);
x_2619 = lean_st_ref_take(x_13, x_2609);
x_2620 = lean_ctor_get(x_2619, 0);
lean_inc(x_2620);
x_2621 = lean_ctor_get(x_2619, 1);
lean_inc(x_2621);
lean_dec(x_2619);
x_2622 = lean_ctor_get(x_2620, 0);
lean_inc(x_2622);
x_2623 = lean_ctor_get(x_2620, 1);
lean_inc(x_2623);
x_2624 = lean_ctor_get(x_2623, 0);
lean_inc(x_2624);
x_2625 = lean_ctor_get(x_2623, 1);
lean_inc(x_2625);
x_2626 = lean_ctor_get(x_2623, 2);
lean_inc(x_2626);
lean_dec(x_2623);
lean_inc(x_2618);
x_2627 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_2626, x_2510, x_2618);
x_2628 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2628, 0, x_2624);
lean_ctor_set(x_2628, 1, x_2625);
lean_ctor_set(x_2628, 2, x_2627);
x_2629 = lean_ctor_get(x_2620, 2);
lean_inc(x_2629);
x_2630 = lean_ctor_get(x_2620, 3);
lean_inc(x_2630);
x_2631 = lean_ctor_get(x_2620, 4);
lean_inc(x_2631);
x_2632 = lean_ctor_get(x_2620, 5);
lean_inc(x_2632);
x_2633 = lean_ctor_get(x_2620, 6);
lean_inc(x_2633);
x_2634 = lean_ctor_get_uint8(x_2620, sizeof(void*)*26);
x_2635 = lean_ctor_get(x_2620, 7);
lean_inc(x_2635);
x_2636 = lean_ctor_get(x_2620, 8);
lean_inc(x_2636);
x_2637 = lean_ctor_get(x_2620, 9);
lean_inc(x_2637);
x_2638 = lean_ctor_get(x_2620, 10);
lean_inc(x_2638);
x_2639 = lean_ctor_get(x_2620, 11);
lean_inc(x_2639);
x_2640 = lean_ctor_get(x_2620, 12);
lean_inc(x_2640);
x_2641 = lean_ctor_get(x_2620, 13);
lean_inc(x_2641);
x_2642 = lean_ctor_get(x_2620, 14);
lean_inc(x_2642);
x_2643 = lean_ctor_get(x_2620, 15);
lean_inc(x_2643);
x_2644 = lean_ctor_get(x_2620, 16);
lean_inc(x_2644);
x_2645 = lean_ctor_get(x_2620, 17);
lean_inc(x_2645);
x_2646 = lean_ctor_get(x_2620, 18);
lean_inc(x_2646);
x_2647 = lean_ctor_get(x_2620, 19);
lean_inc(x_2647);
x_2648 = lean_ctor_get(x_2620, 20);
lean_inc(x_2648);
x_2649 = lean_ctor_get(x_2620, 21);
lean_inc(x_2649);
x_2650 = lean_ctor_get(x_2620, 22);
lean_inc(x_2650);
x_2651 = lean_ctor_get(x_2620, 23);
lean_inc(x_2651);
x_2652 = lean_ctor_get(x_2620, 24);
lean_inc(x_2652);
x_2653 = lean_ctor_get(x_2620, 25);
lean_inc(x_2653);
lean_dec(x_2620);
x_2654 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_2654, 0, x_2622);
lean_ctor_set(x_2654, 1, x_2628);
lean_ctor_set(x_2654, 2, x_2629);
lean_ctor_set(x_2654, 3, x_2630);
lean_ctor_set(x_2654, 4, x_2631);
lean_ctor_set(x_2654, 5, x_2632);
lean_ctor_set(x_2654, 6, x_2633);
lean_ctor_set(x_2654, 7, x_2635);
lean_ctor_set(x_2654, 8, x_2636);
lean_ctor_set(x_2654, 9, x_2637);
lean_ctor_set(x_2654, 10, x_2638);
lean_ctor_set(x_2654, 11, x_2639);
lean_ctor_set(x_2654, 12, x_2640);
lean_ctor_set(x_2654, 13, x_2641);
lean_ctor_set(x_2654, 14, x_2642);
lean_ctor_set(x_2654, 15, x_2643);
lean_ctor_set(x_2654, 16, x_2644);
lean_ctor_set(x_2654, 17, x_2645);
lean_ctor_set(x_2654, 18, x_2646);
lean_ctor_set(x_2654, 19, x_2647);
lean_ctor_set(x_2654, 20, x_2648);
lean_ctor_set(x_2654, 21, x_2649);
lean_ctor_set(x_2654, 22, x_2650);
lean_ctor_set(x_2654, 23, x_2651);
lean_ctor_set(x_2654, 24, x_2652);
lean_ctor_set(x_2654, 25, x_2653);
lean_ctor_set_uint8(x_2654, sizeof(void*)*26, x_2634);
x_2655 = lean_st_ref_set(x_13, x_2654, x_2621);
lean_dec(x_13);
x_2656 = lean_ctor_get(x_2655, 1);
lean_inc(x_2656);
if (lean_is_exclusive(x_2655)) {
 lean_ctor_release(x_2655, 0);
 lean_ctor_release(x_2655, 1);
 x_2657 = x_2655;
} else {
 lean_dec_ref(x_2655);
 x_2657 = lean_box(0);
}
if (lean_is_scalar(x_2657)) {
 x_2658 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2658 = x_2657;
}
lean_ctor_set(x_2658, 0, x_2618);
lean_ctor_set(x_2658, 1, x_2656);
return x_2658;
}
else
{
lean_object* x_2659; lean_object* x_2660; lean_object* x_2661; lean_object* x_2662; lean_object* x_2663; lean_object* x_2664; lean_object* x_2665; lean_object* x_2666; lean_object* x_2667; lean_object* x_2668; lean_object* x_2669; lean_object* x_2670; lean_object* x_2671; lean_object* x_2672; lean_object* x_2673; uint8_t x_2674; lean_object* x_2675; lean_object* x_2676; lean_object* x_2677; lean_object* x_2678; lean_object* x_2679; lean_object* x_2680; lean_object* x_2681; lean_object* x_2682; lean_object* x_2683; lean_object* x_2684; lean_object* x_2685; lean_object* x_2686; lean_object* x_2687; lean_object* x_2688; lean_object* x_2689; lean_object* x_2690; lean_object* x_2691; lean_object* x_2692; lean_object* x_2693; lean_object* x_2694; lean_object* x_2695; lean_object* x_2696; lean_object* x_2697; lean_object* x_2698; 
lean_dec(x_10);
lean_dec(x_9);
x_2659 = lean_st_ref_take(x_13, x_2609);
x_2660 = lean_ctor_get(x_2659, 0);
lean_inc(x_2660);
x_2661 = lean_ctor_get(x_2659, 1);
lean_inc(x_2661);
lean_dec(x_2659);
x_2662 = lean_ctor_get(x_2660, 0);
lean_inc(x_2662);
x_2663 = lean_ctor_get(x_2660, 1);
lean_inc(x_2663);
x_2664 = lean_ctor_get(x_2663, 0);
lean_inc(x_2664);
x_2665 = lean_ctor_get(x_2663, 1);
lean_inc(x_2665);
x_2666 = lean_ctor_get(x_2663, 2);
lean_inc(x_2666);
lean_dec(x_2663);
lean_inc(x_1);
x_2667 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_2666, x_2510, x_1);
x_2668 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2668, 0, x_2664);
lean_ctor_set(x_2668, 1, x_2665);
lean_ctor_set(x_2668, 2, x_2667);
x_2669 = lean_ctor_get(x_2660, 2);
lean_inc(x_2669);
x_2670 = lean_ctor_get(x_2660, 3);
lean_inc(x_2670);
x_2671 = lean_ctor_get(x_2660, 4);
lean_inc(x_2671);
x_2672 = lean_ctor_get(x_2660, 5);
lean_inc(x_2672);
x_2673 = lean_ctor_get(x_2660, 6);
lean_inc(x_2673);
x_2674 = lean_ctor_get_uint8(x_2660, sizeof(void*)*26);
x_2675 = lean_ctor_get(x_2660, 7);
lean_inc(x_2675);
x_2676 = lean_ctor_get(x_2660, 8);
lean_inc(x_2676);
x_2677 = lean_ctor_get(x_2660, 9);
lean_inc(x_2677);
x_2678 = lean_ctor_get(x_2660, 10);
lean_inc(x_2678);
x_2679 = lean_ctor_get(x_2660, 11);
lean_inc(x_2679);
x_2680 = lean_ctor_get(x_2660, 12);
lean_inc(x_2680);
x_2681 = lean_ctor_get(x_2660, 13);
lean_inc(x_2681);
x_2682 = lean_ctor_get(x_2660, 14);
lean_inc(x_2682);
x_2683 = lean_ctor_get(x_2660, 15);
lean_inc(x_2683);
x_2684 = lean_ctor_get(x_2660, 16);
lean_inc(x_2684);
x_2685 = lean_ctor_get(x_2660, 17);
lean_inc(x_2685);
x_2686 = lean_ctor_get(x_2660, 18);
lean_inc(x_2686);
x_2687 = lean_ctor_get(x_2660, 19);
lean_inc(x_2687);
x_2688 = lean_ctor_get(x_2660, 20);
lean_inc(x_2688);
x_2689 = lean_ctor_get(x_2660, 21);
lean_inc(x_2689);
x_2690 = lean_ctor_get(x_2660, 22);
lean_inc(x_2690);
x_2691 = lean_ctor_get(x_2660, 23);
lean_inc(x_2691);
x_2692 = lean_ctor_get(x_2660, 24);
lean_inc(x_2692);
x_2693 = lean_ctor_get(x_2660, 25);
lean_inc(x_2693);
lean_dec(x_2660);
x_2694 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_2694, 0, x_2662);
lean_ctor_set(x_2694, 1, x_2668);
lean_ctor_set(x_2694, 2, x_2669);
lean_ctor_set(x_2694, 3, x_2670);
lean_ctor_set(x_2694, 4, x_2671);
lean_ctor_set(x_2694, 5, x_2672);
lean_ctor_set(x_2694, 6, x_2673);
lean_ctor_set(x_2694, 7, x_2675);
lean_ctor_set(x_2694, 8, x_2676);
lean_ctor_set(x_2694, 9, x_2677);
lean_ctor_set(x_2694, 10, x_2678);
lean_ctor_set(x_2694, 11, x_2679);
lean_ctor_set(x_2694, 12, x_2680);
lean_ctor_set(x_2694, 13, x_2681);
lean_ctor_set(x_2694, 14, x_2682);
lean_ctor_set(x_2694, 15, x_2683);
lean_ctor_set(x_2694, 16, x_2684);
lean_ctor_set(x_2694, 17, x_2685);
lean_ctor_set(x_2694, 18, x_2686);
lean_ctor_set(x_2694, 19, x_2687);
lean_ctor_set(x_2694, 20, x_2688);
lean_ctor_set(x_2694, 21, x_2689);
lean_ctor_set(x_2694, 22, x_2690);
lean_ctor_set(x_2694, 23, x_2691);
lean_ctor_set(x_2694, 24, x_2692);
lean_ctor_set(x_2694, 25, x_2693);
lean_ctor_set_uint8(x_2694, sizeof(void*)*26, x_2674);
x_2695 = lean_st_ref_set(x_13, x_2694, x_2661);
lean_dec(x_13);
x_2696 = lean_ctor_get(x_2695, 1);
lean_inc(x_2696);
if (lean_is_exclusive(x_2695)) {
 lean_ctor_release(x_2695, 0);
 lean_ctor_release(x_2695, 1);
 x_2697 = x_2695;
} else {
 lean_dec_ref(x_2695);
 x_2697 = lean_box(0);
}
if (lean_is_scalar(x_2697)) {
 x_2698 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2698 = x_2697;
}
lean_ctor_set(x_2698, 0, x_1);
lean_ctor_set(x_2698, 1, x_2696);
return x_2698;
}
}
else
{
lean_object* x_2699; lean_object* x_2700; 
lean_dec(x_2510);
lean_dec(x_2508);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_2699 = lean_ctor_get(x_2612, 0);
lean_inc(x_2699);
lean_dec(x_2612);
x_2700 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2700, 0, x_2699);
lean_ctor_set(x_2700, 1, x_2609);
return x_2700;
}
}
}
else
{
uint8_t x_2701; 
lean_dec(x_2508);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_2701 = !lean_is_exclusive(x_2509);
if (x_2701 == 0)
{
return x_2509;
}
else
{
lean_object* x_2702; lean_object* x_2703; lean_object* x_2704; 
x_2702 = lean_ctor_get(x_2509, 0);
x_2703 = lean_ctor_get(x_2509, 1);
lean_inc(x_2703);
lean_inc(x_2702);
lean_dec(x_2509);
x_2704 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2704, 0, x_2702);
lean_ctor_set(x_2704, 1, x_2703);
return x_2704;
}
}
}
block_2743:
{
lean_object* x_2707; 
lean_dec(x_2706);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_9);
x_2707 = l_Lean_Meta_getFunInfo(x_9, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_2707) == 0)
{
lean_object* x_2708; lean_object* x_2709; lean_object* x_2710; lean_object* x_2711; lean_object* x_2712; lean_object* x_2713; lean_object* x_2714; uint8_t x_2715; lean_object* x_2716; lean_object* x_2717; lean_object* x_2718; lean_object* x_2719; 
x_2708 = lean_ctor_get(x_2707, 0);
lean_inc(x_2708);
x_2709 = lean_ctor_get(x_2707, 1);
lean_inc(x_2709);
lean_dec(x_2707);
x_2710 = lean_ctor_get(x_2708, 0);
lean_inc(x_2710);
lean_dec(x_2708);
x_2711 = lean_array_get_size(x_10);
x_2712 = lean_unsigned_to_nat(0u);
x_2713 = lean_unsigned_to_nat(1u);
lean_inc(x_2711);
x_2714 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2714, 0, x_2712);
lean_ctor_set(x_2714, 1, x_2711);
lean_ctor_set(x_2714, 2, x_2713);
x_2715 = 0;
x_2716 = lean_box(x_2715);
lean_inc(x_10);
x_2717 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2717, 0, x_10);
lean_ctor_set(x_2717, 1, x_2716);
x_2718 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_2714);
lean_inc(x_9);
lean_inc(x_1);
x_2719 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_2718, x_2710, x_2711, x_2714, x_2714, x_2717, x_2712, lean_box(0), lean_box(0), x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_2709);
if (lean_obj_tag(x_2719) == 0)
{
lean_object* x_2720; lean_object* x_2721; uint8_t x_2722; 
x_2720 = lean_ctor_get(x_2719, 0);
lean_inc(x_2720);
x_2721 = lean_ctor_get(x_2720, 1);
lean_inc(x_2721);
x_2722 = lean_unbox(x_2721);
lean_dec(x_2721);
if (x_2722 == 0)
{
uint8_t x_2723; 
lean_dec(x_2720);
lean_dec(x_9);
x_2723 = !lean_is_exclusive(x_2719);
if (x_2723 == 0)
{
lean_object* x_2724; 
x_2724 = lean_ctor_get(x_2719, 0);
lean_dec(x_2724);
lean_ctor_set(x_2719, 0, x_1);
return x_2719;
}
else
{
lean_object* x_2725; lean_object* x_2726; 
x_2725 = lean_ctor_get(x_2719, 1);
lean_inc(x_2725);
lean_dec(x_2719);
x_2726 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2726, 0, x_1);
lean_ctor_set(x_2726, 1, x_2725);
return x_2726;
}
}
else
{
uint8_t x_2727; 
lean_dec(x_1);
x_2727 = !lean_is_exclusive(x_2719);
if (x_2727 == 0)
{
lean_object* x_2728; lean_object* x_2729; lean_object* x_2730; 
x_2728 = lean_ctor_get(x_2719, 0);
lean_dec(x_2728);
x_2729 = lean_ctor_get(x_2720, 0);
lean_inc(x_2729);
lean_dec(x_2720);
x_2730 = l_Lean_mkAppN(x_9, x_2729);
lean_dec(x_2729);
lean_ctor_set(x_2719, 0, x_2730);
return x_2719;
}
else
{
lean_object* x_2731; lean_object* x_2732; lean_object* x_2733; lean_object* x_2734; 
x_2731 = lean_ctor_get(x_2719, 1);
lean_inc(x_2731);
lean_dec(x_2719);
x_2732 = lean_ctor_get(x_2720, 0);
lean_inc(x_2732);
lean_dec(x_2720);
x_2733 = l_Lean_mkAppN(x_9, x_2732);
lean_dec(x_2732);
x_2734 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2734, 0, x_2733);
lean_ctor_set(x_2734, 1, x_2731);
return x_2734;
}
}
}
else
{
uint8_t x_2735; 
lean_dec(x_9);
lean_dec(x_1);
x_2735 = !lean_is_exclusive(x_2719);
if (x_2735 == 0)
{
return x_2719;
}
else
{
lean_object* x_2736; lean_object* x_2737; lean_object* x_2738; 
x_2736 = lean_ctor_get(x_2719, 0);
x_2737 = lean_ctor_get(x_2719, 1);
lean_inc(x_2737);
lean_inc(x_2736);
lean_dec(x_2719);
x_2738 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2738, 0, x_2736);
lean_ctor_set(x_2738, 1, x_2737);
return x_2738;
}
}
}
else
{
uint8_t x_2739; 
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
x_2739 = !lean_is_exclusive(x_2707);
if (x_2739 == 0)
{
return x_2707;
}
else
{
lean_object* x_2740; lean_object* x_2741; lean_object* x_2742; 
x_2740 = lean_ctor_get(x_2707, 0);
x_2741 = lean_ctor_get(x_2707, 1);
lean_inc(x_2741);
lean_inc(x_2740);
lean_dec(x_2707);
x_2742 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2742, 0, x_2740);
lean_ctor_set(x_2742, 1, x_2741);
return x_2742;
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
