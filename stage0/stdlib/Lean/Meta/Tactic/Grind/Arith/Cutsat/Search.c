// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Search
// Imports: Lean.Meta.Tactic.Grind.Arith.Cutsat.Var Lean.Meta.Tactic.Grind.Arith.Cutsat.Util Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_isDone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_gcd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_isDone___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_eval_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_isDone___lambda__2___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_isDone___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__3;
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_satisfiedLe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_gcdExt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__6;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_decideVar___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__5;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkLeCnstr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedPUnit;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_decideVar___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_decideVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__7;
lean_object* l_Lean_throwError___at_Int_Linear_Poly_updateOccs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__4;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_outOfBounds___rarg(lean_object*);
lean_object* l_Lean_quoteIfNotAtom(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__3;
lean_object* l_Int_Linear_Poly_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__7;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__8;
static lean_object* l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__5;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__1;
uint8_t l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(uint8_t, uint8_t);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_cdiv(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadMetaM;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__11;
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_isDone___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__4;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1___closed__1;
lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___spec__1___closed__1;
static lean_object* l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_decideVar___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___spec__1___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_decideVar___closed__1;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__8;
lean_object* l_Lean_PersistentArray_get_x21___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__3___boxed(lean_object**);
size_t lean_usize_add(size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__10;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_isDone___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__6;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__2;
lean_object* l_Int_Linear_Poly_combine_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkDvdCnstr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__2;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_decideVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__4;
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_isDone___closed__1;
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_7, x_6);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_4);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_array_uget(x_5, x_7);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_8, 1);
x_23 = lean_ctor_get(x_8, 0);
lean_dec(x_23);
lean_inc(x_22);
x_24 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2(x_1, x_20, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_8, 0, x_28);
lean_ctor_set(x_24, 0, x_8);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_8, 0, x_30);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
lean_dec(x_22);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
lean_inc(x_4);
lean_ctor_set(x_8, 1, x_33);
lean_ctor_set(x_8, 0, x_4);
x_34 = 1;
x_35 = lean_usize_add(x_7, x_34);
x_7 = x_35;
x_17 = x_32;
goto _start;
}
}
else
{
uint8_t x_37; 
lean_free_object(x_8);
lean_dec(x_22);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_24);
if (x_37 == 0)
{
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_24);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
lean_dec(x_8);
lean_inc(x_41);
x_42 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2(x_1, x_20, x_41, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_20);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_4);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; 
lean_dec(x_41);
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
lean_dec(x_42);
x_50 = lean_ctor_get(x_43, 0);
lean_inc(x_50);
lean_dec(x_43);
lean_inc(x_4);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_4);
lean_ctor_set(x_51, 1, x_50);
x_52 = 1;
x_53 = lean_usize_add(x_7, x_52);
x_7 = x_53;
x_8 = x_51;
x_17 = x_49;
goto _start;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_41);
lean_dec(x_4);
x_55 = lean_ctor_get(x_42, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_42, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_57 = x_42;
} else {
 lean_dec_ref(x_42);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_6, x_5);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_30; 
x_19 = lean_array_uget(x_4, x_6);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_21 = x_7;
} else {
 lean_dec_ref(x_7);
 x_21 = lean_box(0);
}
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_3);
x_31 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___rarg(x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 2);
lean_inc(x_37);
lean_dec(x_30);
x_38 = l_Int_Linear_Poly_eval_x3f(x_37, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_3);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___rarg(x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_40);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_38);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_38, 1);
x_48 = lean_ctor_get(x_38, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_39);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_39, 0);
x_51 = lean_int_neg(x_36);
lean_dec(x_36);
x_52 = l_Int_Linear_cdiv(x_50, x_51);
lean_dec(x_51);
lean_dec(x_50);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_53; 
lean_ctor_set(x_38, 1, x_19);
lean_ctor_set(x_38, 0, x_52);
lean_ctor_set(x_39, 0, x_38);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_39);
x_22 = x_53;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_54; uint8_t x_55; 
lean_free_object(x_39);
lean_free_object(x_38);
x_54 = lean_ctor_get(x_20, 0);
lean_inc(x_54);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
lean_dec(x_57);
x_58 = lean_int_dec_lt(x_56, x_52);
lean_dec(x_56);
if (x_58 == 0)
{
lean_object* x_59; 
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_19);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_20);
x_22 = x_59;
x_23 = x_47;
goto block_29;
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_20);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_20, 0);
lean_dec(x_61);
lean_ctor_set(x_54, 1, x_19);
lean_ctor_set(x_54, 0, x_52);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_20);
x_22 = x_62;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_20);
lean_ctor_set(x_54, 1, x_19);
lean_ctor_set(x_54, 0, x_52);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_54);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_22 = x_64;
x_23 = x_47;
goto block_29;
}
}
}
else
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_54, 0);
lean_inc(x_65);
lean_dec(x_54);
x_66 = lean_int_dec_lt(x_65, x_52);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_52);
lean_dec(x_19);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_20);
x_22 = x_67;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_68 = x_20;
} else {
 lean_dec_ref(x_20);
 x_68 = lean_box(0);
}
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_52);
lean_ctor_set(x_69, 1, x_19);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(1, 1, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_22 = x_71;
x_23 = x_47;
goto block_29;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_39, 0);
lean_inc(x_72);
lean_dec(x_39);
x_73 = lean_int_neg(x_36);
lean_dec(x_36);
x_74 = l_Int_Linear_cdiv(x_72, x_73);
lean_dec(x_73);
lean_dec(x_72);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_ctor_set(x_38, 1, x_19);
lean_ctor_set(x_38, 0, x_74);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_38);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_22 = x_76;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_free_object(x_38);
x_77 = lean_ctor_get(x_20, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
x_80 = lean_int_dec_lt(x_78, x_74);
lean_dec(x_78);
if (x_80 == 0)
{
lean_object* x_81; 
lean_dec(x_79);
lean_dec(x_74);
lean_dec(x_19);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_20);
x_22 = x_81;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_82 = x_20;
} else {
 lean_dec_ref(x_20);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_79;
}
lean_ctor_set(x_83, 0, x_74);
lean_ctor_set(x_83, 1, x_19);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(1, 1, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_22 = x_85;
x_23 = x_47;
goto block_29;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_38, 1);
lean_inc(x_86);
lean_dec(x_38);
x_87 = lean_ctor_get(x_39, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_88 = x_39;
} else {
 lean_dec_ref(x_39);
 x_88 = lean_box(0);
}
x_89 = lean_int_neg(x_36);
lean_dec(x_36);
x_90 = l_Int_Linear_cdiv(x_87, x_89);
lean_dec(x_89);
lean_dec(x_87);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_19);
if (lean_is_scalar(x_88)) {
 x_92 = lean_alloc_ctor(1, 1, 0);
} else {
 x_92 = x_88;
}
lean_ctor_set(x_92, 0, x_91);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_22 = x_93;
x_23 = x_86;
goto block_29;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_88);
x_94 = lean_ctor_get(x_20, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_96 = x_94;
} else {
 lean_dec_ref(x_94);
 x_96 = lean_box(0);
}
x_97 = lean_int_dec_lt(x_95, x_90);
lean_dec(x_95);
if (x_97 == 0)
{
lean_object* x_98; 
lean_dec(x_96);
lean_dec(x_90);
lean_dec(x_19);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_20);
x_22 = x_98;
x_23 = x_86;
goto block_29;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_99 = x_20;
} else {
 lean_dec_ref(x_20);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_96;
}
lean_ctor_set(x_100, 0, x_90);
lean_ctor_set(x_100, 1, x_19);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(1, 1, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_22 = x_102;
x_23 = x_86;
goto block_29;
}
}
}
}
}
block_29:
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_3);
if (lean_is_scalar(x_21)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_21;
}
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
x_26 = 1;
x_27 = lean_usize_add(x_6, x_26);
x_6 = x_27;
x_7 = x_25;
x_16 = x_23;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_box(0);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
x_17 = lean_array_size(x_13);
x_18 = 0;
x_19 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__3(x_1, x_13, x_14, x_15, x_13, x_17, x_18, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2___lambda__1(x_23, x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_20);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_19, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_28);
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
lean_dec(x_21);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_19);
if (x_32 == 0)
{
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_19, 0);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_2, 0);
x_37 = lean_box(0);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_3);
x_40 = lean_array_size(x_36);
x_41 = 0;
x_42 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__4(x_36, x_37, x_38, x_36, x_40, x_41, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_box(0);
x_48 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2___lambda__1(x_46, x_47, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_45);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_43);
x_49 = !lean_is_exclusive(x_42);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_42, 0);
lean_dec(x_50);
x_51 = lean_ctor_get(x_44, 0);
lean_inc(x_51);
lean_dec(x_44);
lean_ctor_set(x_42, 0, x_51);
return x_42;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_42, 1);
lean_inc(x_52);
lean_dec(x_42);
x_53 = lean_ctor_get(x_44, 0);
lean_inc(x_53);
lean_dec(x_44);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_42);
if (x_55 == 0)
{
return x_42;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_42, 0);
x_57 = lean_ctor_get(x_42, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_42);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_6, x_5);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_30; 
x_19 = lean_array_uget(x_4, x_6);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_21 = x_7;
} else {
 lean_dec_ref(x_7);
 x_21 = lean_box(0);
}
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_3);
x_31 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___rarg(x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 2);
lean_inc(x_37);
lean_dec(x_30);
x_38 = l_Int_Linear_Poly_eval_x3f(x_37, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_3);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___rarg(x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_40);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_38);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_38, 1);
x_48 = lean_ctor_get(x_38, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_39);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_39, 0);
x_51 = lean_int_neg(x_36);
lean_dec(x_36);
x_52 = l_Int_Linear_cdiv(x_50, x_51);
lean_dec(x_51);
lean_dec(x_50);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_53; 
lean_ctor_set(x_38, 1, x_19);
lean_ctor_set(x_38, 0, x_52);
lean_ctor_set(x_39, 0, x_38);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_39);
x_22 = x_53;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_54; uint8_t x_55; 
lean_free_object(x_39);
lean_free_object(x_38);
x_54 = lean_ctor_get(x_20, 0);
lean_inc(x_54);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
lean_dec(x_57);
x_58 = lean_int_dec_lt(x_56, x_52);
lean_dec(x_56);
if (x_58 == 0)
{
lean_object* x_59; 
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_19);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_20);
x_22 = x_59;
x_23 = x_47;
goto block_29;
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_20);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_20, 0);
lean_dec(x_61);
lean_ctor_set(x_54, 1, x_19);
lean_ctor_set(x_54, 0, x_52);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_20);
x_22 = x_62;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_20);
lean_ctor_set(x_54, 1, x_19);
lean_ctor_set(x_54, 0, x_52);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_54);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_22 = x_64;
x_23 = x_47;
goto block_29;
}
}
}
else
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_54, 0);
lean_inc(x_65);
lean_dec(x_54);
x_66 = lean_int_dec_lt(x_65, x_52);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_52);
lean_dec(x_19);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_20);
x_22 = x_67;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_68 = x_20;
} else {
 lean_dec_ref(x_20);
 x_68 = lean_box(0);
}
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_52);
lean_ctor_set(x_69, 1, x_19);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(1, 1, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_22 = x_71;
x_23 = x_47;
goto block_29;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_39, 0);
lean_inc(x_72);
lean_dec(x_39);
x_73 = lean_int_neg(x_36);
lean_dec(x_36);
x_74 = l_Int_Linear_cdiv(x_72, x_73);
lean_dec(x_73);
lean_dec(x_72);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_ctor_set(x_38, 1, x_19);
lean_ctor_set(x_38, 0, x_74);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_38);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_22 = x_76;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_free_object(x_38);
x_77 = lean_ctor_get(x_20, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
x_80 = lean_int_dec_lt(x_78, x_74);
lean_dec(x_78);
if (x_80 == 0)
{
lean_object* x_81; 
lean_dec(x_79);
lean_dec(x_74);
lean_dec(x_19);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_20);
x_22 = x_81;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_82 = x_20;
} else {
 lean_dec_ref(x_20);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_79;
}
lean_ctor_set(x_83, 0, x_74);
lean_ctor_set(x_83, 1, x_19);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(1, 1, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_22 = x_85;
x_23 = x_47;
goto block_29;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_38, 1);
lean_inc(x_86);
lean_dec(x_38);
x_87 = lean_ctor_get(x_39, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_88 = x_39;
} else {
 lean_dec_ref(x_39);
 x_88 = lean_box(0);
}
x_89 = lean_int_neg(x_36);
lean_dec(x_36);
x_90 = l_Int_Linear_cdiv(x_87, x_89);
lean_dec(x_89);
lean_dec(x_87);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_19);
if (lean_is_scalar(x_88)) {
 x_92 = lean_alloc_ctor(1, 1, 0);
} else {
 x_92 = x_88;
}
lean_ctor_set(x_92, 0, x_91);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_22 = x_93;
x_23 = x_86;
goto block_29;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_88);
x_94 = lean_ctor_get(x_20, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_96 = x_94;
} else {
 lean_dec_ref(x_94);
 x_96 = lean_box(0);
}
x_97 = lean_int_dec_lt(x_95, x_90);
lean_dec(x_95);
if (x_97 == 0)
{
lean_object* x_98; 
lean_dec(x_96);
lean_dec(x_90);
lean_dec(x_19);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_20);
x_22 = x_98;
x_23 = x_86;
goto block_29;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_99 = x_20;
} else {
 lean_dec_ref(x_20);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_96;
}
lean_ctor_set(x_100, 0, x_90);
lean_ctor_set(x_100, 1, x_19);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(1, 1, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_22 = x_102;
x_23 = x_86;
goto block_29;
}
}
}
}
}
block_29:
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_3);
if (lean_is_scalar(x_21)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_21;
}
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
x_26 = 1;
x_27 = lean_usize_add(x_6, x_26);
x_6 = x_27;
x_7 = x_25;
x_16 = x_23;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_13 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2(x_2, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_box(0);
x_24 = lean_ctor_get(x_1, 1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
x_27 = lean_array_size(x_24);
x_28 = 0;
x_29 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__5(x_23, x_24, x_25, x_24, x_27, x_28, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_30);
x_38 = !lean_is_exclusive(x_29);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_29, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_40);
return x_29;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_dec(x_29);
x_42 = lean_ctor_get(x_31, 0);
lean_inc(x_42);
lean_dec(x_31);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_29);
if (x_44 == 0)
{
return x_29;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_29, 0);
x_46 = lean_ctor_get(x_29, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_29);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_13);
if (x_48 == 0)
{
return x_13;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_13, 0);
x_50 = lean_ctor_get(x_13, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_13);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedPersistentArray(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_ctor_get(x_12, 3);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
x_17 = lean_nat_dec_lt(x_1, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
x_18 = l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___closed__1;
x_19 = l_outOfBounds___rarg(x_18);
x_20 = l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__1(x_19, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___closed__1;
x_30 = l_Lean_PersistentArray_get_x21___rarg(x_29, x_15, x_1);
x_31 = l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__1(x_30, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__3___boxed(lean_object** _args) {
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
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_20 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__3(x_1, x_2, x_3, x_4, x_5, x_18, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__4(x_1, x_2, x_3, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__5(x_1, x_2, x_3, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_7, x_6);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_4);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_array_uget(x_5, x_7);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_8, 1);
x_23 = lean_ctor_get(x_8, 0);
lean_dec(x_23);
lean_inc(x_22);
x_24 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__2(x_1, x_20, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_8, 0, x_28);
lean_ctor_set(x_24, 0, x_8);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_8, 0, x_30);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
lean_dec(x_22);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
lean_inc(x_4);
lean_ctor_set(x_8, 1, x_33);
lean_ctor_set(x_8, 0, x_4);
x_34 = 1;
x_35 = lean_usize_add(x_7, x_34);
x_7 = x_35;
x_17 = x_32;
goto _start;
}
}
else
{
uint8_t x_37; 
lean_free_object(x_8);
lean_dec(x_22);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_24);
if (x_37 == 0)
{
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_24);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
lean_dec(x_8);
lean_inc(x_41);
x_42 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__2(x_1, x_20, x_41, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_20);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_4);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; 
lean_dec(x_41);
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
lean_dec(x_42);
x_50 = lean_ctor_get(x_43, 0);
lean_inc(x_50);
lean_dec(x_43);
lean_inc(x_4);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_4);
lean_ctor_set(x_51, 1, x_50);
x_52 = 1;
x_53 = lean_usize_add(x_7, x_52);
x_7 = x_53;
x_8 = x_51;
x_17 = x_49;
goto _start;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_41);
lean_dec(x_4);
x_55 = lean_ctor_get(x_42, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_42, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_57 = x_42;
} else {
 lean_dec_ref(x_42);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_6, x_5);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_30; 
x_19 = lean_array_uget(x_4, x_6);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_21 = x_7;
} else {
 lean_dec_ref(x_7);
 x_21 = lean_box(0);
}
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_3);
x_31 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___rarg(x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 2);
lean_inc(x_37);
lean_dec(x_30);
x_38 = l_Int_Linear_Poly_eval_x3f(x_37, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_3);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___rarg(x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_40);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_38);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_38, 1);
x_48 = lean_ctor_get(x_38, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_39);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_39, 0);
x_51 = lean_int_neg(x_50);
lean_dec(x_50);
x_52 = lean_int_ediv(x_51, x_36);
lean_dec(x_36);
lean_dec(x_51);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_53; 
lean_ctor_set(x_38, 1, x_19);
lean_ctor_set(x_38, 0, x_52);
lean_ctor_set(x_39, 0, x_38);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_39);
x_22 = x_53;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_54; uint8_t x_55; 
lean_free_object(x_39);
lean_free_object(x_38);
x_54 = lean_ctor_get(x_20, 0);
lean_inc(x_54);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
lean_dec(x_57);
x_58 = lean_int_dec_lt(x_52, x_56);
lean_dec(x_56);
if (x_58 == 0)
{
lean_object* x_59; 
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_19);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_20);
x_22 = x_59;
x_23 = x_47;
goto block_29;
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_20);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_20, 0);
lean_dec(x_61);
lean_ctor_set(x_54, 1, x_19);
lean_ctor_set(x_54, 0, x_52);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_20);
x_22 = x_62;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_20);
lean_ctor_set(x_54, 1, x_19);
lean_ctor_set(x_54, 0, x_52);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_54);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_22 = x_64;
x_23 = x_47;
goto block_29;
}
}
}
else
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_54, 0);
lean_inc(x_65);
lean_dec(x_54);
x_66 = lean_int_dec_lt(x_52, x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_52);
lean_dec(x_19);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_20);
x_22 = x_67;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_68 = x_20;
} else {
 lean_dec_ref(x_20);
 x_68 = lean_box(0);
}
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_52);
lean_ctor_set(x_69, 1, x_19);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(1, 1, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_22 = x_71;
x_23 = x_47;
goto block_29;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_39, 0);
lean_inc(x_72);
lean_dec(x_39);
x_73 = lean_int_neg(x_72);
lean_dec(x_72);
x_74 = lean_int_ediv(x_73, x_36);
lean_dec(x_36);
lean_dec(x_73);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_ctor_set(x_38, 1, x_19);
lean_ctor_set(x_38, 0, x_74);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_38);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_22 = x_76;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_free_object(x_38);
x_77 = lean_ctor_get(x_20, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
x_80 = lean_int_dec_lt(x_74, x_78);
lean_dec(x_78);
if (x_80 == 0)
{
lean_object* x_81; 
lean_dec(x_79);
lean_dec(x_74);
lean_dec(x_19);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_20);
x_22 = x_81;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_82 = x_20;
} else {
 lean_dec_ref(x_20);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_79;
}
lean_ctor_set(x_83, 0, x_74);
lean_ctor_set(x_83, 1, x_19);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(1, 1, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_22 = x_85;
x_23 = x_47;
goto block_29;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_38, 1);
lean_inc(x_86);
lean_dec(x_38);
x_87 = lean_ctor_get(x_39, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_88 = x_39;
} else {
 lean_dec_ref(x_39);
 x_88 = lean_box(0);
}
x_89 = lean_int_neg(x_87);
lean_dec(x_87);
x_90 = lean_int_ediv(x_89, x_36);
lean_dec(x_36);
lean_dec(x_89);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_19);
if (lean_is_scalar(x_88)) {
 x_92 = lean_alloc_ctor(1, 1, 0);
} else {
 x_92 = x_88;
}
lean_ctor_set(x_92, 0, x_91);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_22 = x_93;
x_23 = x_86;
goto block_29;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_88);
x_94 = lean_ctor_get(x_20, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_96 = x_94;
} else {
 lean_dec_ref(x_94);
 x_96 = lean_box(0);
}
x_97 = lean_int_dec_lt(x_90, x_95);
lean_dec(x_95);
if (x_97 == 0)
{
lean_object* x_98; 
lean_dec(x_96);
lean_dec(x_90);
lean_dec(x_19);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_20);
x_22 = x_98;
x_23 = x_86;
goto block_29;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_99 = x_20;
} else {
 lean_dec_ref(x_20);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_96;
}
lean_ctor_set(x_100, 0, x_90);
lean_ctor_set(x_100, 1, x_19);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(1, 1, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_22 = x_102;
x_23 = x_86;
goto block_29;
}
}
}
}
}
block_29:
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_3);
if (lean_is_scalar(x_21)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_21;
}
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
x_26 = 1;
x_27 = lean_usize_add(x_6, x_26);
x_6 = x_27;
x_7 = x_25;
x_16 = x_23;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_box(0);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
x_17 = lean_array_size(x_13);
x_18 = 0;
x_19 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__3(x_1, x_13, x_14, x_15, x_13, x_17, x_18, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2___lambda__1(x_23, x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_20);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_19, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_28);
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
lean_dec(x_21);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_19);
if (x_32 == 0)
{
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_19, 0);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_2, 0);
x_37 = lean_box(0);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_3);
x_40 = lean_array_size(x_36);
x_41 = 0;
x_42 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__4(x_36, x_37, x_38, x_36, x_40, x_41, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_box(0);
x_48 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2___lambda__1(x_46, x_47, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_45);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_43);
x_49 = !lean_is_exclusive(x_42);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_42, 0);
lean_dec(x_50);
x_51 = lean_ctor_get(x_44, 0);
lean_inc(x_51);
lean_dec(x_44);
lean_ctor_set(x_42, 0, x_51);
return x_42;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_42, 1);
lean_inc(x_52);
lean_dec(x_42);
x_53 = lean_ctor_get(x_44, 0);
lean_inc(x_53);
lean_dec(x_44);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_42);
if (x_55 == 0)
{
return x_42;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_42, 0);
x_57 = lean_ctor_get(x_42, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_42);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_6, x_5);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_30; 
x_19 = lean_array_uget(x_4, x_6);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_21 = x_7;
} else {
 lean_dec_ref(x_7);
 x_21 = lean_box(0);
}
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_3);
x_31 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___rarg(x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 2);
lean_inc(x_37);
lean_dec(x_30);
x_38 = l_Int_Linear_Poly_eval_x3f(x_37, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_3);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___rarg(x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_40);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_38);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_38, 1);
x_48 = lean_ctor_get(x_38, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_39);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_39, 0);
x_51 = lean_int_neg(x_50);
lean_dec(x_50);
x_52 = lean_int_ediv(x_51, x_36);
lean_dec(x_36);
lean_dec(x_51);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_53; 
lean_ctor_set(x_38, 1, x_19);
lean_ctor_set(x_38, 0, x_52);
lean_ctor_set(x_39, 0, x_38);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_39);
x_22 = x_53;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_54; uint8_t x_55; 
lean_free_object(x_39);
lean_free_object(x_38);
x_54 = lean_ctor_get(x_20, 0);
lean_inc(x_54);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
lean_dec(x_57);
x_58 = lean_int_dec_lt(x_52, x_56);
lean_dec(x_56);
if (x_58 == 0)
{
lean_object* x_59; 
lean_free_object(x_54);
lean_dec(x_52);
lean_dec(x_19);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_20);
x_22 = x_59;
x_23 = x_47;
goto block_29;
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_20);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_20, 0);
lean_dec(x_61);
lean_ctor_set(x_54, 1, x_19);
lean_ctor_set(x_54, 0, x_52);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_20);
x_22 = x_62;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_20);
lean_ctor_set(x_54, 1, x_19);
lean_ctor_set(x_54, 0, x_52);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_54);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_22 = x_64;
x_23 = x_47;
goto block_29;
}
}
}
else
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_54, 0);
lean_inc(x_65);
lean_dec(x_54);
x_66 = lean_int_dec_lt(x_52, x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_52);
lean_dec(x_19);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_20);
x_22 = x_67;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_68 = x_20;
} else {
 lean_dec_ref(x_20);
 x_68 = lean_box(0);
}
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_52);
lean_ctor_set(x_69, 1, x_19);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(1, 1, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_22 = x_71;
x_23 = x_47;
goto block_29;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_39, 0);
lean_inc(x_72);
lean_dec(x_39);
x_73 = lean_int_neg(x_72);
lean_dec(x_72);
x_74 = lean_int_ediv(x_73, x_36);
lean_dec(x_36);
lean_dec(x_73);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_ctor_set(x_38, 1, x_19);
lean_ctor_set(x_38, 0, x_74);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_38);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_22 = x_76;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_free_object(x_38);
x_77 = lean_ctor_get(x_20, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
x_80 = lean_int_dec_lt(x_74, x_78);
lean_dec(x_78);
if (x_80 == 0)
{
lean_object* x_81; 
lean_dec(x_79);
lean_dec(x_74);
lean_dec(x_19);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_20);
x_22 = x_81;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_82 = x_20;
} else {
 lean_dec_ref(x_20);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_79;
}
lean_ctor_set(x_83, 0, x_74);
lean_ctor_set(x_83, 1, x_19);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(1, 1, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_22 = x_85;
x_23 = x_47;
goto block_29;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_38, 1);
lean_inc(x_86);
lean_dec(x_38);
x_87 = lean_ctor_get(x_39, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_88 = x_39;
} else {
 lean_dec_ref(x_39);
 x_88 = lean_box(0);
}
x_89 = lean_int_neg(x_87);
lean_dec(x_87);
x_90 = lean_int_ediv(x_89, x_36);
lean_dec(x_36);
lean_dec(x_89);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_19);
if (lean_is_scalar(x_88)) {
 x_92 = lean_alloc_ctor(1, 1, 0);
} else {
 x_92 = x_88;
}
lean_ctor_set(x_92, 0, x_91);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_22 = x_93;
x_23 = x_86;
goto block_29;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_88);
x_94 = lean_ctor_get(x_20, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_96 = x_94;
} else {
 lean_dec_ref(x_94);
 x_96 = lean_box(0);
}
x_97 = lean_int_dec_lt(x_90, x_95);
lean_dec(x_95);
if (x_97 == 0)
{
lean_object* x_98; 
lean_dec(x_96);
lean_dec(x_90);
lean_dec(x_19);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_20);
x_22 = x_98;
x_23 = x_86;
goto block_29;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_99 = x_20;
} else {
 lean_dec_ref(x_20);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_96;
}
lean_ctor_set(x_100, 0, x_90);
lean_ctor_set(x_100, 1, x_19);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(1, 1, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_22 = x_102;
x_23 = x_86;
goto block_29;
}
}
}
}
}
block_29:
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_3);
if (lean_is_scalar(x_21)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_21;
}
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
x_26 = 1;
x_27 = lean_usize_add(x_6, x_26);
x_6 = x_27;
x_7 = x_25;
x_16 = x_23;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_13 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__2(x_2, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_box(0);
x_24 = lean_ctor_get(x_1, 1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
x_27 = lean_array_size(x_24);
x_28 = 0;
x_29 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__5(x_23, x_24, x_25, x_24, x_27, x_28, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_30);
x_38 = !lean_is_exclusive(x_29);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_29, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_40);
return x_29;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_dec(x_29);
x_42 = lean_ctor_get(x_31, 0);
lean_inc(x_42);
lean_dec(x_31);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_29);
if (x_44 == 0)
{
return x_29;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_29, 0);
x_46 = lean_ctor_get(x_29, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_29);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_13);
if (x_48 == 0)
{
return x_13;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_13, 0);
x_50 = lean_ctor_get(x_13, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_13);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_ctor_get(x_12, 4);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
x_17 = lean_nat_dec_lt(x_1, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
x_18 = l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___closed__1;
x_19 = l_outOfBounds___rarg(x_18);
x_20 = l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__1(x_19, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___closed__1;
x_30 = l_Lean_PersistentArray_get_x21___rarg(x_29, x_15, x_1);
x_31 = l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__1(x_30, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__3___boxed(lean_object** _args) {
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
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_20 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__3(x_1, x_2, x_3, x_4, x_5, x_18, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__4(x_1, x_2, x_3, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__5(x_1, x_2, x_3, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_nat_to_int(x_1);
x_16 = lean_int_ediv(x_2, x_15);
x_17 = lean_int_ediv(x_3, x_15);
x_18 = lean_int_ediv(x_4, x_15);
lean_dec(x_15);
x_19 = l_Lean_Meta_Grind_Arith_Cutsat_gcdExt(x_17, x_16);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 1);
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_dec(x_25);
x_26 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1___closed__1;
x_27 = lean_int_dec_lt(x_24, x_26);
x_28 = lean_int_neg(x_18);
lean_dec(x_18);
if (x_27 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_int_mul(x_28, x_24);
lean_dec(x_24);
lean_dec(x_28);
lean_ctor_set(x_21, 1, x_29);
lean_ctor_set(x_21, 0, x_16);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 0, x_30);
return x_19;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_int_emod(x_24, x_16);
lean_dec(x_24);
x_32 = lean_int_mul(x_28, x_31);
lean_dec(x_31);
lean_dec(x_28);
lean_ctor_set(x_21, 1, x_32);
lean_ctor_set(x_21, 0, x_16);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 0, x_33);
return x_19;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_21, 0);
lean_inc(x_34);
lean_dec(x_21);
x_35 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1___closed__1;
x_36 = lean_int_dec_lt(x_34, x_35);
x_37 = lean_int_neg(x_18);
lean_dec(x_18);
if (x_36 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_int_mul(x_37, x_34);
lean_dec(x_34);
lean_dec(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_16);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 0, x_40);
return x_19;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_int_emod(x_34, x_16);
lean_dec(x_34);
x_42 = lean_int_mul(x_37, x_41);
lean_dec(x_41);
lean_dec(x_37);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_16);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 0, x_44);
return x_19;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
lean_dec(x_19);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
x_48 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1___closed__1;
x_49 = lean_int_dec_lt(x_46, x_48);
x_50 = lean_int_neg(x_18);
lean_dec(x_18);
if (x_49 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_int_mul(x_50, x_46);
lean_dec(x_46);
lean_dec(x_50);
if (lean_is_scalar(x_47)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_47;
}
lean_ctor_set(x_52, 0, x_16);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_14);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_int_emod(x_46, x_16);
lean_dec(x_46);
x_56 = lean_int_mul(x_50, x_55);
lean_dec(x_55);
lean_dec(x_50);
if (lean_is_scalar(x_47)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_47;
}
lean_ctor_set(x_57, 0, x_16);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_14);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_11);
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 2);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = l_Int_Linear_Poly_eval_x3f(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_13);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_16, 1);
x_22 = lean_ctor_get(x_16, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = l_Int_gcd(x_15, x_13);
lean_inc(x_24);
x_25 = lean_nat_to_int(x_24);
x_26 = lean_int_emod(x_23, x_25);
lean_dec(x_25);
x_27 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1___closed__1;
x_28 = lean_int_dec_eq(x_26, x_27);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_13);
x_29 = lean_box(0);
lean_ctor_set(x_16, 0, x_29);
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_free_object(x_16);
x_30 = lean_box(0);
x_31 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1(x_24, x_15, x_13, x_23, x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_23);
lean_dec(x_13);
lean_dec(x_15);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_dec(x_16);
x_33 = lean_ctor_get(x_17, 0);
lean_inc(x_33);
lean_dec(x_17);
x_34 = l_Int_gcd(x_15, x_13);
lean_inc(x_34);
x_35 = lean_nat_to_int(x_34);
x_36 = lean_int_emod(x_33, x_35);
lean_dec(x_35);
x_37 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1___closed__1;
x_38 = lean_int_dec_eq(x_36, x_37);
lean_dec(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_15);
lean_dec(x_13);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_32);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_box(0);
x_42 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1(x_34, x_15, x_13, x_33, x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_32);
lean_dec(x_33);
lean_dec(x_13);
lean_dec(x_15);
return x_42;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
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
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_st_ref_take(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 13);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_13, 13);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_14, 1);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_15, 9);
x_23 = l_Lean_PersistentArray_push___rarg(x_22, x_1);
lean_ctor_set(x_15, 9, x_23);
x_24 = lean_st_ref_set(x_3, x_13, x_16);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
x_33 = lean_ctor_get(x_15, 2);
x_34 = lean_ctor_get(x_15, 3);
x_35 = lean_ctor_get(x_15, 4);
x_36 = lean_ctor_get(x_15, 5);
x_37 = lean_ctor_get(x_15, 6);
x_38 = lean_ctor_get(x_15, 7);
x_39 = lean_ctor_get(x_15, 8);
x_40 = lean_ctor_get(x_15, 9);
x_41 = lean_ctor_get(x_15, 10);
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
lean_inc(x_31);
lean_dec(x_15);
x_42 = l_Lean_PersistentArray_push___rarg(x_40, x_1);
x_43 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_43, 0, x_31);
lean_ctor_set(x_43, 1, x_32);
lean_ctor_set(x_43, 2, x_33);
lean_ctor_set(x_43, 3, x_34);
lean_ctor_set(x_43, 4, x_35);
lean_ctor_set(x_43, 5, x_36);
lean_ctor_set(x_43, 6, x_37);
lean_ctor_set(x_43, 7, x_38);
lean_ctor_set(x_43, 8, x_39);
lean_ctor_set(x_43, 9, x_42);
lean_ctor_set(x_43, 10, x_41);
lean_ctor_set(x_14, 1, x_43);
x_44 = lean_st_ref_set(x_3, x_13, x_16);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
x_47 = lean_box(0);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_49 = lean_ctor_get(x_14, 0);
lean_inc(x_49);
lean_dec(x_14);
x_50 = lean_ctor_get(x_15, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_15, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_15, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_15, 3);
lean_inc(x_53);
x_54 = lean_ctor_get(x_15, 4);
lean_inc(x_54);
x_55 = lean_ctor_get(x_15, 5);
lean_inc(x_55);
x_56 = lean_ctor_get(x_15, 6);
lean_inc(x_56);
x_57 = lean_ctor_get(x_15, 7);
lean_inc(x_57);
x_58 = lean_ctor_get(x_15, 8);
lean_inc(x_58);
x_59 = lean_ctor_get(x_15, 9);
lean_inc(x_59);
x_60 = lean_ctor_get(x_15, 10);
lean_inc(x_60);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 lean_ctor_release(x_15, 3);
 lean_ctor_release(x_15, 4);
 lean_ctor_release(x_15, 5);
 lean_ctor_release(x_15, 6);
 lean_ctor_release(x_15, 7);
 lean_ctor_release(x_15, 8);
 lean_ctor_release(x_15, 9);
 lean_ctor_release(x_15, 10);
 x_61 = x_15;
} else {
 lean_dec_ref(x_15);
 x_61 = lean_box(0);
}
x_62 = l_Lean_PersistentArray_push___rarg(x_59, x_1);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 11, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_50);
lean_ctor_set(x_63, 1, x_51);
lean_ctor_set(x_63, 2, x_52);
lean_ctor_set(x_63, 3, x_53);
lean_ctor_set(x_63, 4, x_54);
lean_ctor_set(x_63, 5, x_55);
lean_ctor_set(x_63, 6, x_56);
lean_ctor_set(x_63, 7, x_57);
lean_ctor_set(x_63, 8, x_58);
lean_ctor_set(x_63, 9, x_62);
lean_ctor_set(x_63, 10, x_60);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_49);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_13, 13, x_64);
x_65 = lean_st_ref_set(x_3, x_13, x_16);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = lean_box(0);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_70 = lean_ctor_get(x_13, 0);
x_71 = lean_ctor_get(x_13, 1);
x_72 = lean_ctor_get(x_13, 2);
x_73 = lean_ctor_get(x_13, 3);
x_74 = lean_ctor_get(x_13, 4);
x_75 = lean_ctor_get(x_13, 5);
x_76 = lean_ctor_get(x_13, 6);
x_77 = lean_ctor_get_uint8(x_13, sizeof(void*)*15);
x_78 = lean_ctor_get(x_13, 7);
x_79 = lean_ctor_get(x_13, 8);
x_80 = lean_ctor_get(x_13, 9);
x_81 = lean_ctor_get(x_13, 10);
x_82 = lean_ctor_get(x_13, 11);
x_83 = lean_ctor_get(x_13, 12);
x_84 = lean_ctor_get(x_13, 14);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_13);
x_85 = lean_ctor_get(x_14, 0);
lean_inc(x_85);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_86 = x_14;
} else {
 lean_dec_ref(x_14);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get(x_15, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_15, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_15, 2);
lean_inc(x_89);
x_90 = lean_ctor_get(x_15, 3);
lean_inc(x_90);
x_91 = lean_ctor_get(x_15, 4);
lean_inc(x_91);
x_92 = lean_ctor_get(x_15, 5);
lean_inc(x_92);
x_93 = lean_ctor_get(x_15, 6);
lean_inc(x_93);
x_94 = lean_ctor_get(x_15, 7);
lean_inc(x_94);
x_95 = lean_ctor_get(x_15, 8);
lean_inc(x_95);
x_96 = lean_ctor_get(x_15, 9);
lean_inc(x_96);
x_97 = lean_ctor_get(x_15, 10);
lean_inc(x_97);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 lean_ctor_release(x_15, 3);
 lean_ctor_release(x_15, 4);
 lean_ctor_release(x_15, 5);
 lean_ctor_release(x_15, 6);
 lean_ctor_release(x_15, 7);
 lean_ctor_release(x_15, 8);
 lean_ctor_release(x_15, 9);
 lean_ctor_release(x_15, 10);
 x_98 = x_15;
} else {
 lean_dec_ref(x_15);
 x_98 = lean_box(0);
}
x_99 = l_Lean_PersistentArray_push___rarg(x_96, x_1);
if (lean_is_scalar(x_98)) {
 x_100 = lean_alloc_ctor(0, 11, 0);
} else {
 x_100 = x_98;
}
lean_ctor_set(x_100, 0, x_87);
lean_ctor_set(x_100, 1, x_88);
lean_ctor_set(x_100, 2, x_89);
lean_ctor_set(x_100, 3, x_90);
lean_ctor_set(x_100, 4, x_91);
lean_ctor_set(x_100, 5, x_92);
lean_ctor_set(x_100, 6, x_93);
lean_ctor_set(x_100, 7, x_94);
lean_ctor_set(x_100, 8, x_95);
lean_ctor_set(x_100, 9, x_99);
lean_ctor_set(x_100, 10, x_97);
if (lean_is_scalar(x_86)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_86;
}
lean_ctor_set(x_101, 0, x_85);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_102, 0, x_70);
lean_ctor_set(x_102, 1, x_71);
lean_ctor_set(x_102, 2, x_72);
lean_ctor_set(x_102, 3, x_73);
lean_ctor_set(x_102, 4, x_74);
lean_ctor_set(x_102, 5, x_75);
lean_ctor_set(x_102, 6, x_76);
lean_ctor_set(x_102, 7, x_78);
lean_ctor_set(x_102, 8, x_79);
lean_ctor_set(x_102, 9, x_80);
lean_ctor_set(x_102, 10, x_81);
lean_ctor_set(x_102, 11, x_82);
lean_ctor_set(x_102, 12, x_83);
lean_ctor_set(x_102, 13, x_101);
lean_ctor_set(x_102, 14, x_84);
lean_ctor_set_uint8(x_102, sizeof(void*)*15, x_77);
x_103 = lean_st_ref_set(x_3, x_102, x_16);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
x_106 = lean_box(0);
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_105;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_104);
return x_107;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`grind` internal error, variable is already assigned", 52, 52);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cutsat", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assign", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__3;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__4;
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__5;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 9);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_nat_dec_eq(x_1, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_free_object(x_12);
x_19 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 9);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_22, 2);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_nat_dec_lt(x_23, x_1);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
x_25 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__2;
x_26 = l_Lean_throwError___at_Int_Linear_Poly_updateOccs___spec__1(x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_st_ref_take(x_3, x_21);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 13);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_28, 13);
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
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_30, 9);
x_38 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1___closed__1;
x_39 = l_Lean_PersistentArray_push___rarg(x_37, x_38);
lean_ctor_set(x_30, 9, x_39);
x_40 = lean_st_ref_set(x_3, x_28, x_31);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_11 = x_41;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_43 = lean_ctor_get(x_30, 0);
x_44 = lean_ctor_get(x_30, 1);
x_45 = lean_ctor_get(x_30, 2);
x_46 = lean_ctor_get(x_30, 3);
x_47 = lean_ctor_get(x_30, 4);
x_48 = lean_ctor_get(x_30, 5);
x_49 = lean_ctor_get(x_30, 6);
x_50 = lean_ctor_get(x_30, 7);
x_51 = lean_ctor_get(x_30, 8);
x_52 = lean_ctor_get(x_30, 9);
x_53 = lean_ctor_get(x_30, 10);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_30);
x_54 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1___closed__1;
x_55 = l_Lean_PersistentArray_push___rarg(x_52, x_54);
x_56 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_56, 0, x_43);
lean_ctor_set(x_56, 1, x_44);
lean_ctor_set(x_56, 2, x_45);
lean_ctor_set(x_56, 3, x_46);
lean_ctor_set(x_56, 4, x_47);
lean_ctor_set(x_56, 5, x_48);
lean_ctor_set(x_56, 6, x_49);
lean_ctor_set(x_56, 7, x_50);
lean_ctor_set(x_56, 8, x_51);
lean_ctor_set(x_56, 9, x_55);
lean_ctor_set(x_56, 10, x_53);
lean_ctor_set(x_29, 1, x_56);
x_57 = lean_st_ref_set(x_3, x_28, x_31);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_11 = x_58;
goto _start;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_60 = lean_ctor_get(x_29, 0);
lean_inc(x_60);
lean_dec(x_29);
x_61 = lean_ctor_get(x_30, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_30, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_30, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_30, 3);
lean_inc(x_64);
x_65 = lean_ctor_get(x_30, 4);
lean_inc(x_65);
x_66 = lean_ctor_get(x_30, 5);
lean_inc(x_66);
x_67 = lean_ctor_get(x_30, 6);
lean_inc(x_67);
x_68 = lean_ctor_get(x_30, 7);
lean_inc(x_68);
x_69 = lean_ctor_get(x_30, 8);
lean_inc(x_69);
x_70 = lean_ctor_get(x_30, 9);
lean_inc(x_70);
x_71 = lean_ctor_get(x_30, 10);
lean_inc(x_71);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 lean_ctor_release(x_30, 3);
 lean_ctor_release(x_30, 4);
 lean_ctor_release(x_30, 5);
 lean_ctor_release(x_30, 6);
 lean_ctor_release(x_30, 7);
 lean_ctor_release(x_30, 8);
 lean_ctor_release(x_30, 9);
 lean_ctor_release(x_30, 10);
 x_72 = x_30;
} else {
 lean_dec_ref(x_30);
 x_72 = lean_box(0);
}
x_73 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1___closed__1;
x_74 = l_Lean_PersistentArray_push___rarg(x_70, x_73);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(0, 11, 0);
} else {
 x_75 = x_72;
}
lean_ctor_set(x_75, 0, x_61);
lean_ctor_set(x_75, 1, x_62);
lean_ctor_set(x_75, 2, x_63);
lean_ctor_set(x_75, 3, x_64);
lean_ctor_set(x_75, 4, x_65);
lean_ctor_set(x_75, 5, x_66);
lean_ctor_set(x_75, 6, x_67);
lean_ctor_set(x_75, 7, x_68);
lean_ctor_set(x_75, 8, x_69);
lean_ctor_set(x_75, 9, x_74);
lean_ctor_set(x_75, 10, x_71);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_60);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_28, 13, x_76);
x_77 = lean_st_ref_set(x_3, x_28, x_31);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_11 = x_78;
goto _start;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_80 = lean_ctor_get(x_28, 0);
x_81 = lean_ctor_get(x_28, 1);
x_82 = lean_ctor_get(x_28, 2);
x_83 = lean_ctor_get(x_28, 3);
x_84 = lean_ctor_get(x_28, 4);
x_85 = lean_ctor_get(x_28, 5);
x_86 = lean_ctor_get(x_28, 6);
x_87 = lean_ctor_get_uint8(x_28, sizeof(void*)*15);
x_88 = lean_ctor_get(x_28, 7);
x_89 = lean_ctor_get(x_28, 8);
x_90 = lean_ctor_get(x_28, 9);
x_91 = lean_ctor_get(x_28, 10);
x_92 = lean_ctor_get(x_28, 11);
x_93 = lean_ctor_get(x_28, 12);
x_94 = lean_ctor_get(x_28, 14);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_28);
x_95 = lean_ctor_get(x_29, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_96 = x_29;
} else {
 lean_dec_ref(x_29);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_30, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_30, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_30, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_30, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_30, 4);
lean_inc(x_101);
x_102 = lean_ctor_get(x_30, 5);
lean_inc(x_102);
x_103 = lean_ctor_get(x_30, 6);
lean_inc(x_103);
x_104 = lean_ctor_get(x_30, 7);
lean_inc(x_104);
x_105 = lean_ctor_get(x_30, 8);
lean_inc(x_105);
x_106 = lean_ctor_get(x_30, 9);
lean_inc(x_106);
x_107 = lean_ctor_get(x_30, 10);
lean_inc(x_107);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 lean_ctor_release(x_30, 3);
 lean_ctor_release(x_30, 4);
 lean_ctor_release(x_30, 5);
 lean_ctor_release(x_30, 6);
 lean_ctor_release(x_30, 7);
 lean_ctor_release(x_30, 8);
 lean_ctor_release(x_30, 9);
 lean_ctor_release(x_30, 10);
 x_108 = x_30;
} else {
 lean_dec_ref(x_30);
 x_108 = lean_box(0);
}
x_109 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1___closed__1;
x_110 = l_Lean_PersistentArray_push___rarg(x_106, x_109);
if (lean_is_scalar(x_108)) {
 x_111 = lean_alloc_ctor(0, 11, 0);
} else {
 x_111 = x_108;
}
lean_ctor_set(x_111, 0, x_97);
lean_ctor_set(x_111, 1, x_98);
lean_ctor_set(x_111, 2, x_99);
lean_ctor_set(x_111, 3, x_100);
lean_ctor_set(x_111, 4, x_101);
lean_ctor_set(x_111, 5, x_102);
lean_ctor_set(x_111, 6, x_103);
lean_ctor_set(x_111, 7, x_104);
lean_ctor_set(x_111, 8, x_105);
lean_ctor_set(x_111, 9, x_110);
lean_ctor_set(x_111, 10, x_107);
if (lean_is_scalar(x_96)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_96;
}
lean_ctor_set(x_112, 0, x_95);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_113, 0, x_80);
lean_ctor_set(x_113, 1, x_81);
lean_ctor_set(x_113, 2, x_82);
lean_ctor_set(x_113, 3, x_83);
lean_ctor_set(x_113, 4, x_84);
lean_ctor_set(x_113, 5, x_85);
lean_ctor_set(x_113, 6, x_86);
lean_ctor_set(x_113, 7, x_88);
lean_ctor_set(x_113, 8, x_89);
lean_ctor_set(x_113, 9, x_90);
lean_ctor_set(x_113, 10, x_91);
lean_ctor_set(x_113, 11, x_92);
lean_ctor_set(x_113, 12, x_93);
lean_ctor_set(x_113, 13, x_112);
lean_ctor_set(x_113, 14, x_94);
lean_ctor_set_uint8(x_113, sizeof(void*)*15, x_87);
x_114 = lean_st_ref_set(x_3, x_113, x_31);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_11 = x_115;
goto _start;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_117 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__6;
x_118 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_117, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_unbox(x_119);
lean_dec(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_free_object(x_12);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_dec(x_118);
x_122 = lean_box(0);
x_123 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___lambda__1(x_2, x_122, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_121);
return x_123;
}
else
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_118);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_125 = lean_ctor_get(x_118, 1);
x_126 = lean_ctor_get(x_118, 0);
lean_dec(x_126);
x_127 = l_Lean_Meta_Grind_Arith_Cutsat_getVar(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_125);
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_129 = lean_ctor_get(x_127, 0);
x_130 = lean_ctor_get(x_127, 1);
x_131 = l_Lean_quoteIfNotAtom(x_129);
x_132 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__8;
lean_ctor_set_tag(x_127, 7);
lean_ctor_set(x_127, 1, x_131);
lean_ctor_set(x_127, 0, x_132);
x_133 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__10;
lean_ctor_set_tag(x_118, 7);
lean_ctor_set(x_118, 1, x_133);
lean_ctor_set(x_118, 0, x_127);
x_134 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1___closed__1;
x_135 = lean_int_dec_lt(x_2, x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_136 = lean_nat_abs(x_2);
x_137 = l___private_Init_Data_Repr_0__Nat_reprFast(x_136);
x_138 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_138, 0, x_137);
x_139 = l_Lean_MessageData_ofFormat(x_138);
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_139);
lean_ctor_set(x_12, 0, x_118);
x_140 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_140, 0, x_12);
lean_ctor_set(x_140, 1, x_132);
x_141 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_117, x_140, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_130);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___lambda__1(x_2, x_142, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_143);
lean_dec(x_142);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_145 = lean_nat_abs(x_2);
x_146 = lean_unsigned_to_nat(1u);
x_147 = lean_nat_sub(x_145, x_146);
lean_dec(x_145);
x_148 = lean_nat_add(x_147, x_146);
lean_dec(x_147);
x_149 = l___private_Init_Data_Repr_0__Nat_reprFast(x_148);
x_150 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__11;
x_151 = lean_string_append(x_150, x_149);
lean_dec(x_149);
x_152 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_152, 0, x_151);
x_153 = l_Lean_MessageData_ofFormat(x_152);
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_153);
lean_ctor_set(x_12, 0, x_118);
x_154 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_154, 0, x_12);
lean_ctor_set(x_154, 1, x_132);
x_155 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_117, x_154, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_130);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___lambda__1(x_2, x_156, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_157);
lean_dec(x_156);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_159 = lean_ctor_get(x_127, 0);
x_160 = lean_ctor_get(x_127, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_127);
x_161 = l_Lean_quoteIfNotAtom(x_159);
x_162 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__8;
x_163 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
x_164 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__10;
lean_ctor_set_tag(x_118, 7);
lean_ctor_set(x_118, 1, x_164);
lean_ctor_set(x_118, 0, x_163);
x_165 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1___closed__1;
x_166 = lean_int_dec_lt(x_2, x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_167 = lean_nat_abs(x_2);
x_168 = l___private_Init_Data_Repr_0__Nat_reprFast(x_167);
x_169 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_169, 0, x_168);
x_170 = l_Lean_MessageData_ofFormat(x_169);
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_170);
lean_ctor_set(x_12, 0, x_118);
x_171 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_171, 0, x_12);
lean_ctor_set(x_171, 1, x_162);
x_172 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_117, x_171, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_160);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_175 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___lambda__1(x_2, x_173, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_174);
lean_dec(x_173);
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_176 = lean_nat_abs(x_2);
x_177 = lean_unsigned_to_nat(1u);
x_178 = lean_nat_sub(x_176, x_177);
lean_dec(x_176);
x_179 = lean_nat_add(x_178, x_177);
lean_dec(x_178);
x_180 = l___private_Init_Data_Repr_0__Nat_reprFast(x_179);
x_181 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__11;
x_182 = lean_string_append(x_181, x_180);
lean_dec(x_180);
x_183 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_183, 0, x_182);
x_184 = l_Lean_MessageData_ofFormat(x_183);
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_184);
lean_ctor_set(x_12, 0, x_118);
x_185 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_185, 0, x_12);
lean_ctor_set(x_185, 1, x_162);
x_186 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_117, x_185, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_160);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___lambda__1(x_2, x_187, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_188);
lean_dec(x_187);
return x_189;
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_190 = lean_ctor_get(x_118, 1);
lean_inc(x_190);
lean_dec(x_118);
x_191 = l_Lean_Meta_Grind_Arith_Cutsat_getVar(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_190);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_194 = x_191;
} else {
 lean_dec_ref(x_191);
 x_194 = lean_box(0);
}
x_195 = l_Lean_quoteIfNotAtom(x_192);
x_196 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__8;
if (lean_is_scalar(x_194)) {
 x_197 = lean_alloc_ctor(7, 2, 0);
} else {
 x_197 = x_194;
 lean_ctor_set_tag(x_197, 7);
}
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_195);
x_198 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__10;
x_199 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
x_200 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1___closed__1;
x_201 = lean_int_dec_lt(x_2, x_200);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_202 = lean_nat_abs(x_2);
x_203 = l___private_Init_Data_Repr_0__Nat_reprFast(x_202);
x_204 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_204, 0, x_203);
x_205 = l_Lean_MessageData_ofFormat(x_204);
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_205);
lean_ctor_set(x_12, 0, x_199);
x_206 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_206, 0, x_12);
lean_ctor_set(x_206, 1, x_196);
x_207 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_117, x_206, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_193);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___lambda__1(x_2, x_208, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_209);
lean_dec(x_208);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_211 = lean_nat_abs(x_2);
x_212 = lean_unsigned_to_nat(1u);
x_213 = lean_nat_sub(x_211, x_212);
lean_dec(x_211);
x_214 = lean_nat_add(x_213, x_212);
lean_dec(x_213);
x_215 = l___private_Init_Data_Repr_0__Nat_reprFast(x_214);
x_216 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__11;
x_217 = lean_string_append(x_216, x_215);
lean_dec(x_215);
x_218 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_218, 0, x_217);
x_219 = l_Lean_MessageData_ofFormat(x_218);
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_219);
lean_ctor_set(x_12, 0, x_199);
x_220 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_220, 0, x_12);
lean_ctor_set(x_220, 1, x_196);
x_221 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_117, x_220, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_193);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_224 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___lambda__1(x_2, x_222, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_223);
lean_dec(x_222);
return x_224;
}
}
}
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; 
x_225 = lean_ctor_get(x_12, 0);
x_226 = lean_ctor_get(x_12, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_12);
x_227 = lean_ctor_get(x_225, 9);
lean_inc(x_227);
lean_dec(x_225);
x_228 = lean_ctor_get(x_227, 2);
lean_inc(x_228);
lean_dec(x_227);
x_229 = lean_nat_dec_eq(x_1, x_228);
lean_dec(x_228);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_230 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_226);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = lean_ctor_get(x_231, 9);
lean_inc(x_233);
lean_dec(x_231);
x_234 = lean_ctor_get(x_233, 2);
lean_inc(x_234);
lean_dec(x_233);
x_235 = lean_nat_dec_lt(x_234, x_1);
lean_dec(x_234);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; 
lean_dec(x_2);
x_236 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__2;
x_237 = l_Lean_throwError___at_Int_Linear_Poly_updateOccs___spec__1(x_236, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_232);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_238 = lean_st_ref_take(x_3, x_232);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_239, 13);
lean_inc(x_240);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
x_242 = lean_ctor_get(x_238, 1);
lean_inc(x_242);
lean_dec(x_238);
x_243 = lean_ctor_get(x_239, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_239, 1);
lean_inc(x_244);
x_245 = lean_ctor_get(x_239, 2);
lean_inc(x_245);
x_246 = lean_ctor_get(x_239, 3);
lean_inc(x_246);
x_247 = lean_ctor_get(x_239, 4);
lean_inc(x_247);
x_248 = lean_ctor_get(x_239, 5);
lean_inc(x_248);
x_249 = lean_ctor_get(x_239, 6);
lean_inc(x_249);
x_250 = lean_ctor_get_uint8(x_239, sizeof(void*)*15);
x_251 = lean_ctor_get(x_239, 7);
lean_inc(x_251);
x_252 = lean_ctor_get(x_239, 8);
lean_inc(x_252);
x_253 = lean_ctor_get(x_239, 9);
lean_inc(x_253);
x_254 = lean_ctor_get(x_239, 10);
lean_inc(x_254);
x_255 = lean_ctor_get(x_239, 11);
lean_inc(x_255);
x_256 = lean_ctor_get(x_239, 12);
lean_inc(x_256);
x_257 = lean_ctor_get(x_239, 14);
lean_inc(x_257);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 lean_ctor_release(x_239, 2);
 lean_ctor_release(x_239, 3);
 lean_ctor_release(x_239, 4);
 lean_ctor_release(x_239, 5);
 lean_ctor_release(x_239, 6);
 lean_ctor_release(x_239, 7);
 lean_ctor_release(x_239, 8);
 lean_ctor_release(x_239, 9);
 lean_ctor_release(x_239, 10);
 lean_ctor_release(x_239, 11);
 lean_ctor_release(x_239, 12);
 lean_ctor_release(x_239, 13);
 lean_ctor_release(x_239, 14);
 x_258 = x_239;
} else {
 lean_dec_ref(x_239);
 x_258 = lean_box(0);
}
x_259 = lean_ctor_get(x_240, 0);
lean_inc(x_259);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_260 = x_240;
} else {
 lean_dec_ref(x_240);
 x_260 = lean_box(0);
}
x_261 = lean_ctor_get(x_241, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_241, 1);
lean_inc(x_262);
x_263 = lean_ctor_get(x_241, 2);
lean_inc(x_263);
x_264 = lean_ctor_get(x_241, 3);
lean_inc(x_264);
x_265 = lean_ctor_get(x_241, 4);
lean_inc(x_265);
x_266 = lean_ctor_get(x_241, 5);
lean_inc(x_266);
x_267 = lean_ctor_get(x_241, 6);
lean_inc(x_267);
x_268 = lean_ctor_get(x_241, 7);
lean_inc(x_268);
x_269 = lean_ctor_get(x_241, 8);
lean_inc(x_269);
x_270 = lean_ctor_get(x_241, 9);
lean_inc(x_270);
x_271 = lean_ctor_get(x_241, 10);
lean_inc(x_271);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 lean_ctor_release(x_241, 2);
 lean_ctor_release(x_241, 3);
 lean_ctor_release(x_241, 4);
 lean_ctor_release(x_241, 5);
 lean_ctor_release(x_241, 6);
 lean_ctor_release(x_241, 7);
 lean_ctor_release(x_241, 8);
 lean_ctor_release(x_241, 9);
 lean_ctor_release(x_241, 10);
 x_272 = x_241;
} else {
 lean_dec_ref(x_241);
 x_272 = lean_box(0);
}
x_273 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1___closed__1;
x_274 = l_Lean_PersistentArray_push___rarg(x_270, x_273);
if (lean_is_scalar(x_272)) {
 x_275 = lean_alloc_ctor(0, 11, 0);
} else {
 x_275 = x_272;
}
lean_ctor_set(x_275, 0, x_261);
lean_ctor_set(x_275, 1, x_262);
lean_ctor_set(x_275, 2, x_263);
lean_ctor_set(x_275, 3, x_264);
lean_ctor_set(x_275, 4, x_265);
lean_ctor_set(x_275, 5, x_266);
lean_ctor_set(x_275, 6, x_267);
lean_ctor_set(x_275, 7, x_268);
lean_ctor_set(x_275, 8, x_269);
lean_ctor_set(x_275, 9, x_274);
lean_ctor_set(x_275, 10, x_271);
if (lean_is_scalar(x_260)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_260;
}
lean_ctor_set(x_276, 0, x_259);
lean_ctor_set(x_276, 1, x_275);
if (lean_is_scalar(x_258)) {
 x_277 = lean_alloc_ctor(0, 15, 1);
} else {
 x_277 = x_258;
}
lean_ctor_set(x_277, 0, x_243);
lean_ctor_set(x_277, 1, x_244);
lean_ctor_set(x_277, 2, x_245);
lean_ctor_set(x_277, 3, x_246);
lean_ctor_set(x_277, 4, x_247);
lean_ctor_set(x_277, 5, x_248);
lean_ctor_set(x_277, 6, x_249);
lean_ctor_set(x_277, 7, x_251);
lean_ctor_set(x_277, 8, x_252);
lean_ctor_set(x_277, 9, x_253);
lean_ctor_set(x_277, 10, x_254);
lean_ctor_set(x_277, 11, x_255);
lean_ctor_set(x_277, 12, x_256);
lean_ctor_set(x_277, 13, x_276);
lean_ctor_set(x_277, 14, x_257);
lean_ctor_set_uint8(x_277, sizeof(void*)*15, x_250);
x_278 = lean_st_ref_set(x_3, x_277, x_242);
x_279 = lean_ctor_get(x_278, 1);
lean_inc(x_279);
lean_dec(x_278);
x_11 = x_279;
goto _start;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
x_281 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__6;
x_282 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_281, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_226);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_unbox(x_283);
lean_dec(x_283);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_282, 1);
lean_inc(x_285);
lean_dec(x_282);
x_286 = lean_box(0);
x_287 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___lambda__1(x_2, x_286, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_285);
return x_287;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; 
x_288 = lean_ctor_get(x_282, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_289 = x_282;
} else {
 lean_dec_ref(x_282);
 x_289 = lean_box(0);
}
x_290 = l_Lean_Meta_Grind_Arith_Cutsat_getVar(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_288);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 x_293 = x_290;
} else {
 lean_dec_ref(x_290);
 x_293 = lean_box(0);
}
x_294 = l_Lean_quoteIfNotAtom(x_291);
x_295 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__8;
if (lean_is_scalar(x_293)) {
 x_296 = lean_alloc_ctor(7, 2, 0);
} else {
 x_296 = x_293;
 lean_ctor_set_tag(x_296, 7);
}
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_294);
x_297 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__10;
if (lean_is_scalar(x_289)) {
 x_298 = lean_alloc_ctor(7, 2, 0);
} else {
 x_298 = x_289;
 lean_ctor_set_tag(x_298, 7);
}
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
x_299 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1___closed__1;
x_300 = lean_int_dec_lt(x_2, x_299);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_301 = lean_nat_abs(x_2);
x_302 = l___private_Init_Data_Repr_0__Nat_reprFast(x_301);
x_303 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_303, 0, x_302);
x_304 = l_Lean_MessageData_ofFormat(x_303);
x_305 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_305, 0, x_298);
lean_ctor_set(x_305, 1, x_304);
x_306 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_295);
x_307 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_281, x_306, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_292);
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec(x_307);
x_310 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___lambda__1(x_2, x_308, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_309);
lean_dec(x_308);
return x_310;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_311 = lean_nat_abs(x_2);
x_312 = lean_unsigned_to_nat(1u);
x_313 = lean_nat_sub(x_311, x_312);
lean_dec(x_311);
x_314 = lean_nat_add(x_313, x_312);
lean_dec(x_313);
x_315 = l___private_Init_Data_Repr_0__Nat_reprFast(x_314);
x_316 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__11;
x_317 = lean_string_append(x_316, x_315);
lean_dec(x_315);
x_318 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_318, 0, x_317);
x_319 = l_Lean_MessageData_ofFormat(x_318);
x_320 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_320, 0, x_298);
lean_ctor_set(x_320, 1, x_319);
x_321 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_295);
x_322 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_281, x_321, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_292);
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_322, 1);
lean_inc(x_324);
lean_dec(x_322);
x_325 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___lambda__1(x_2, x_323, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_324);
lean_dec(x_323);
return x_325;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instMonadMetaM;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__1;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__2;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__3;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__4;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__5;
x_12 = lean_panic_fn(x_11, x_1);
x_13 = lean_apply_9(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("NIY", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: ", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("a₁.natAbs != 1 && a₂.natAbs != 1\n    ", 41, 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__3;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.Arith.Cutsat.Search", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Grind.Arith.Cutsat.resolveLowerUpperConflict", 54, 54);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__6;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__7;
x_3 = lean_unsigned_to_nat(83u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__5;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_13);
lean_dec(x_2);
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___rarg(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_1);
x_16 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___rarg(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 2);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_15, 2);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_nat_abs(x_19);
lean_dec(x_19);
lean_inc(x_21);
x_22 = lean_nat_to_int(x_21);
x_23 = l_Int_Linear_Poly_mul(x_18, x_22);
lean_dec(x_22);
x_24 = lean_nat_abs(x_17);
lean_dec(x_17);
lean_inc(x_24);
x_25 = lean_nat_to_int(x_24);
x_26 = l_Int_Linear_Poly_mul(x_20, x_25);
lean_dec(x_25);
x_27 = lean_unsigned_to_nat(100000000u);
x_28 = l_Int_Linear_Poly_combine_x27(x_27, x_23, x_26);
lean_inc(x_28);
x_29 = l_Int_Linear_Poly_satisfiedLe(x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = 0;
x_34 = lean_unbox(x_31);
lean_dec(x_31);
x_35 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_34, x_33);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
lean_free_object(x_29);
lean_dec(x_28);
lean_dec(x_2);
lean_dec(x_1);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_dec_eq(x_24, x_36);
lean_dec(x_24);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = lean_nat_dec_eq(x_21, x_36);
lean_dec(x_21);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__2;
x_40 = l_Lean_throwError___at_Int_Linear_Poly_updateOccs___spec__1(x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__8;
x_42 = l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1(x_41, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_21);
x_43 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__8;
x_44 = l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1(x_43, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_24);
lean_dec(x_21);
lean_ctor_set_tag(x_29, 4);
lean_ctor_set(x_29, 1, x_2);
lean_ctor_set(x_29, 0, x_1);
x_45 = l_Lean_Meta_Grind_Arith_Cutsat_mkLeCnstr(x_28, x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assert(x_46, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_47);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_29, 0);
x_50 = lean_ctor_get(x_29, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_29);
x_51 = 0;
x_52 = lean_unbox(x_49);
lean_dec(x_49);
x_53 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_52, x_51);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
lean_dec(x_28);
lean_dec(x_2);
lean_dec(x_1);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_dec_eq(x_24, x_54);
lean_dec(x_24);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = lean_nat_dec_eq(x_21, x_54);
lean_dec(x_21);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__2;
x_58 = l_Lean_throwError___at_Int_Linear_Poly_updateOccs___spec__1(x_57, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_50);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__8;
x_60 = l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1(x_59, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_50);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_21);
x_61 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__8;
x_62 = l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1(x_61, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_50);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_24);
lean_dec(x_21);
x_63 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_2);
x_64 = l_Lean_Meta_Grind_Arith_Cutsat_mkLeCnstr(x_28, x_63, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_50);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assert(x_65, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_66);
return x_67;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("conflict", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__3;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__4;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__2;
x_13 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1(x_1, x_2, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_13, 1);
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
lean_inc(x_1);
x_22 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_2);
x_26 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__8;
lean_ctor_set_tag(x_26, 7);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 0, x_30);
x_31 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__4;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_31);
lean_ctor_set(x_22, 0, x_26);
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_28);
lean_ctor_set(x_13, 0, x_22);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_13);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_12, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1(x_1, x_2, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_35);
lean_dec(x_34);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_26);
x_39 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__8;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_24);
x_41 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__4;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_41);
lean_ctor_set(x_22, 0, x_40);
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_37);
lean_ctor_set(x_13, 0, x_22);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_13);
lean_ctor_set(x_42, 1, x_39);
x_43 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_12, x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_38);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1(x_1, x_2, x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_45);
lean_dec(x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_47 = lean_ctor_get(x_22, 0);
x_48 = lean_ctor_get(x_22, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_22);
lean_inc(x_2);
x_49 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
x_53 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__8;
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(7, 2, 0);
} else {
 x_54 = x_52;
 lean_ctor_set_tag(x_54, 7);
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_47);
x_55 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__4;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_50);
lean_ctor_set(x_13, 0, x_56);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_13);
lean_ctor_set(x_57, 1, x_53);
x_58 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_12, x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_51);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1(x_1, x_2, x_59, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_60);
lean_dec(x_59);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_62 = lean_ctor_get(x_13, 1);
lean_inc(x_62);
lean_dec(x_13);
lean_inc(x_1);
x_63 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
lean_inc(x_2);
x_67 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_65);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_70 = x_67;
} else {
 lean_dec_ref(x_67);
 x_70 = lean_box(0);
}
x_71 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__8;
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(7, 2, 0);
} else {
 x_72 = x_70;
 lean_ctor_set_tag(x_72, 7);
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_64);
x_73 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__4;
if (lean_is_scalar(x_66)) {
 x_74 = lean_alloc_ctor(7, 2, 0);
} else {
 x_74 = x_66;
 lean_ctor_set_tag(x_74, 7);
}
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_68);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_71);
x_77 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_12, x_76, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_69);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1(x_1, x_2, x_78, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_79);
lean_dec(x_78);
return x_80;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec(x_12);
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 2);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = l_Int_gcd(x_14, x_16);
lean_dec(x_16);
lean_dec(x_14);
x_18 = lean_nat_to_int(x_17);
x_19 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_19, 0, x_1);
x_20 = l_Lean_Meta_Grind_Arith_Cutsat_mkDvdCnstr(x_18, x_15, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__2;
x_12 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___lambda__1(x_1, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_12, 1);
x_20 = lean_ctor_get(x_12, 0);
lean_dec(x_20);
lean_inc(x_1);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__8;
lean_ctor_set_tag(x_21, 7);
lean_ctor_set(x_21, 1, x_23);
lean_ctor_set(x_21, 0, x_25);
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_25);
lean_ctor_set(x_12, 0, x_21);
x_26 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___lambda__1(x_1, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_28);
lean_dec(x_27);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__8;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_32);
lean_ctor_set(x_12, 0, x_33);
x_34 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_31);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___lambda__1(x_1, x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_38 = lean_ctor_get(x_12, 1);
lean_inc(x_38);
lean_dec(x_12);
lean_inc(x_1);
x_39 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__8;
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(7, 2, 0);
} else {
 x_44 = x_42;
 lean_ctor_set_tag(x_44, 7);
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_11, x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_41);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___lambda__1(x_1, x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_48);
lean_dec(x_47);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_decideVar___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_decideVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ≤ ", 5, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_decideVar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_decideVar___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_decideVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_60; lean_object* x_61; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_155 = lean_box(0);
x_156 = lean_ctor_get(x_18, 2);
lean_inc(x_156);
lean_dec(x_18);
x_157 = lean_ctor_get(x_156, 2);
lean_inc(x_157);
x_158 = lean_nat_dec_lt(x_1, x_157);
lean_dec(x_157);
if (x_158 == 0)
{
lean_object* x_159; 
lean_dec(x_156);
x_159 = l_outOfBounds___rarg(x_155);
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_20);
x_21 = x_159;
goto block_59;
}
else
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_12, 0);
lean_inc(x_160);
lean_dec(x_12);
x_60 = x_159;
x_61 = x_160;
goto block_154;
}
}
else
{
lean_object* x_161; 
x_161 = l_Lean_PersistentArray_get_x21___rarg(x_155, x_156, x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_20);
x_21 = x_161;
goto block_59;
}
else
{
lean_object* x_162; 
x_162 = lean_ctor_get(x_12, 0);
lean_inc(x_162);
lean_dec(x_12);
x_60 = x_161;
x_61 = x_162;
goto block_154;
}
}
block_59:
{
if (lean_obj_tag(x_15) == 0)
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1___closed__1;
x_23 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment(x_1, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
lean_inc(x_24);
x_25 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_24);
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment(x_1, x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_25);
if (x_33 == 0)
{
return x_25;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_25, 0);
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_25);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_15, 0);
lean_inc(x_37);
lean_dec(x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment(x_1, x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_37, 0);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_ctor_get(x_21, 0);
lean_inc(x_41);
lean_dec(x_21);
lean_inc(x_41);
x_42 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_40);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_44);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_41);
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_dec(x_42);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_int_sub(x_40, x_49);
lean_dec(x_40);
x_51 = lean_int_ediv(x_50, x_48);
lean_dec(x_50);
x_52 = lean_int_mul(x_51, x_48);
lean_dec(x_48);
lean_dec(x_51);
x_53 = lean_int_add(x_52, x_49);
lean_dec(x_49);
lean_dec(x_52);
x_54 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment(x_1, x_53, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_47);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_42);
if (x_55 == 0)
{
return x_42;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_42, 0);
x_57 = lean_ctor_get(x_42, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_42);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
block_154:
{
if (lean_obj_tag(x_15) == 0)
{
lean_dec(x_20);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec(x_61);
x_63 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment(x_1, x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
lean_dec(x_60);
lean_inc(x_65);
x_66 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f(x_65, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_64);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict(x_65, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_68);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_65);
x_70 = lean_ctor_get(x_67, 0);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_dec(x_66);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_int_sub(x_64, x_73);
lean_dec(x_64);
x_75 = l_Int_Linear_cdiv(x_74, x_72);
lean_dec(x_74);
x_76 = lean_int_mul(x_75, x_72);
lean_dec(x_72);
lean_dec(x_75);
x_77 = lean_int_add(x_76, x_73);
lean_dec(x_73);
lean_dec(x_76);
x_78 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment(x_1, x_77, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_71);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_78;
}
}
else
{
uint8_t x_79; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_79 = !lean_is_exclusive(x_66);
if (x_79 == 0)
{
return x_66;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_66, 0);
x_81 = lean_ctor_get(x_66, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_66);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_15, 0);
lean_inc(x_83);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_84 = x_15;
} else {
 lean_dec_ref(x_15);
 x_84 = lean_box(0);
}
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_85 = lean_ctor_get(x_61, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_61, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_87 = x_61;
} else {
 lean_dec_ref(x_61);
 x_87 = lean_box(0);
}
x_88 = lean_ctor_get(x_83, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_90 = x_83;
} else {
 lean_dec_ref(x_83);
 x_90 = lean_box(0);
}
x_91 = lean_int_dec_le(x_85, x_88);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_92 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__2;
x_93 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_92, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_unbox(x_94);
lean_dec(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_90);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_20);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
x_97 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict(x_86, x_89, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_96);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_140; uint8_t x_141; 
x_98 = lean_ctor_get(x_93, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_99 = x_93;
} else {
 lean_dec_ref(x_93);
 x_99 = lean_box(0);
}
x_100 = l_Lean_Meta_Grind_Arith_Cutsat_getVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_98);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_103 = x_100;
} else {
 lean_dec_ref(x_100);
 x_103 = lean_box(0);
}
x_104 = l_Lean_MessageData_ofExpr(x_101);
x_140 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1___closed__1;
x_141 = lean_int_dec_lt(x_85, x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_nat_abs(x_85);
lean_dec(x_85);
x_143 = l___private_Init_Data_Repr_0__Nat_reprFast(x_142);
x_105 = x_143;
goto block_139;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_144 = lean_nat_abs(x_85);
lean_dec(x_85);
x_145 = lean_unsigned_to_nat(1u);
x_146 = lean_nat_sub(x_144, x_145);
lean_dec(x_144);
x_147 = lean_nat_add(x_146, x_145);
lean_dec(x_146);
x_148 = l___private_Init_Data_Repr_0__Nat_reprFast(x_147);
x_149 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__11;
x_150 = lean_string_append(x_149, x_148);
lean_dec(x_148);
x_105 = x_150;
goto block_139;
}
block_139:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
if (lean_is_scalar(x_84)) {
 x_106 = lean_alloc_ctor(3, 1, 0);
} else {
 x_106 = x_84;
 lean_ctor_set_tag(x_106, 3);
}
lean_ctor_set(x_106, 0, x_105);
x_107 = l_Lean_MessageData_ofFormat(x_106);
x_108 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__8;
if (lean_is_scalar(x_103)) {
 x_109 = lean_alloc_ctor(7, 2, 0);
} else {
 x_109 = x_103;
 lean_ctor_set_tag(x_109, 7);
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
x_110 = l_Lean_Meta_Grind_Arith_Cutsat_decideVar___closed__2;
if (lean_is_scalar(x_99)) {
 x_111 = lean_alloc_ctor(7, 2, 0);
} else {
 x_111 = x_99;
 lean_ctor_set_tag(x_111, 7);
}
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
if (lean_is_scalar(x_90)) {
 x_112 = lean_alloc_ctor(7, 2, 0);
} else {
 x_112 = x_90;
 lean_ctor_set_tag(x_112, 7);
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_104);
if (lean_is_scalar(x_87)) {
 x_113 = lean_alloc_ctor(7, 2, 0);
} else {
 x_113 = x_87;
 lean_ctor_set_tag(x_113, 7);
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_110);
x_114 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1___closed__1;
x_115 = lean_int_dec_lt(x_88, x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_116 = lean_nat_abs(x_88);
lean_dec(x_88);
x_117 = l___private_Init_Data_Repr_0__Nat_reprFast(x_116);
x_118 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_118, 0, x_117);
x_119 = l_Lean_MessageData_ofFormat(x_118);
if (lean_is_scalar(x_20)) {
 x_120 = lean_alloc_ctor(7, 2, 0);
} else {
 x_120 = x_20;
 lean_ctor_set_tag(x_120, 7);
}
lean_ctor_set(x_120, 0, x_113);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_108);
x_122 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_92, x_121, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_102);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
lean_dec(x_122);
x_124 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict(x_86, x_89, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_123);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_125 = lean_nat_abs(x_88);
lean_dec(x_88);
x_126 = lean_unsigned_to_nat(1u);
x_127 = lean_nat_sub(x_125, x_126);
lean_dec(x_125);
x_128 = lean_nat_add(x_127, x_126);
lean_dec(x_127);
x_129 = l___private_Init_Data_Repr_0__Nat_reprFast(x_128);
x_130 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__11;
x_131 = lean_string_append(x_130, x_129);
lean_dec(x_129);
x_132 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_133 = l_Lean_MessageData_ofFormat(x_132);
if (lean_is_scalar(x_20)) {
 x_134 = lean_alloc_ctor(7, 2, 0);
} else {
 x_134 = x_20;
 lean_ctor_set_tag(x_134, 7);
}
lean_ctor_set(x_134, 0, x_113);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_108);
x_136 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_92, x_135, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_102);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec(x_136);
x_138 = l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict(x_86, x_89, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_137);
return x_138;
}
}
}
}
else
{
lean_object* x_151; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_84);
lean_dec(x_20);
x_151 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment(x_1, x_85, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_20);
x_152 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1___closed__1;
x_153 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment(x_1, x_152, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_153;
}
}
}
}
else
{
uint8_t x_163; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_163 = !lean_is_exclusive(x_14);
if (x_163 == 0)
{
return x_14;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_14, 0);
x_165 = lean_ctor_get(x_14, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_14);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_167 = !lean_is_exclusive(x_11);
if (x_167 == 0)
{
return x_11;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_11, 0);
x_169 = lean_ctor_get(x_11, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_11);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_decideVar___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_decideVar___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_decideVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_decideVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_15, 9);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_18, 2);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_nat_dec_eq(x_17, x_19);
lean_dec(x_19);
lean_dec(x_17);
x_21 = lean_box(x_20);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
lean_dec(x_11);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_22, 9);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_ctor_get(x_26, 2);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_nat_dec_eq(x_25, x_27);
lean_dec(x_27);
lean_dec(x_25);
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasAssignment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_Arith_Cutsat_hasAssignment(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_isDone___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_isDone___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_isDone___lambda__1___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_isDone___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_Meta_Grind_isInconsistent(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_isDone___lambda__2___closed__1;
x_16 = lean_box(0);
x_17 = lean_apply_10(x_15, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
lean_dec(x_19);
x_20 = 1;
x_21 = lean_box(x_20);
lean_ctor_set(x_11, 0, x_21);
return x_11;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_dec(x_11);
x_23 = 1;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_isDone___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_isDone___lambda__2___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_isDone(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Meta_Grind_Arith_Cutsat_hasAssignment(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_isDone___closed__1;
x_15 = lean_box(0);
x_16 = lean_apply_10(x_14, x_15, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
lean_dec(x_18);
x_19 = 1;
x_20 = lean_box(x_19);
lean_ctor_set(x_10, 0, x_20);
return x_10;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = 1;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_isDone___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_isDone___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_isDone___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_isDone___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 9);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Meta_Grind_Arith_Cutsat_decideVar(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___spec__1___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_dec(x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_isDone(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_17 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___spec__1___lambda__1(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
lean_dec(x_18);
x_2 = x_26;
x_11 = x_25;
goto _start;
}
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_12);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_12, 0);
lean_dec(x_33);
x_34 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___spec__1___closed__2;
lean_ctor_set(x_12, 0, x_34);
return x_12;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
lean_dec(x_12);
x_36 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___spec__1___closed__2;
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_12);
if (x_38 == 0)
{
return x_12;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_12, 0);
x_40 = lean_ctor_get(x_12, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_12);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__1() {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__1;
x_11 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___spec__1(x_10, x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_11, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_11);
if (x_26 == 0)
{
return x_11;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__3);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__4);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__5);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__6);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__7);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__8);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__9 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__9);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__10 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__10);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__11 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___closed__11);
l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__1 = _init_l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__1);
l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__2 = _init_l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__2);
l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__3 = _init_l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__3();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__3);
l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__4 = _init_l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__4();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__4);
l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__5 = _init_l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__5();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___spec__1___closed__5);
l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__5 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__5);
l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__6 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__6);
l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__7 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__7);
l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__8 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___lambda__1___closed__8);
l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveLowerUpperConflict___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_decideVar___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_decideVar___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_decideVar___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_decideVar___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_decideVar___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_decideVar___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_isDone___lambda__2___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_isDone___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_isDone___lambda__2___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_isDone___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_isDone___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_isDone___closed__1);
l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___spec__1___closed__1 = _init_l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___spec__1___closed__1();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___spec__1___closed__1);
l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___spec__1___closed__2 = _init_l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___spec__1___closed__2();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___spec__1___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
