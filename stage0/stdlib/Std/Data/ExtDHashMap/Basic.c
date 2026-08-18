// Lean compiler output
// Module: Std.Data.ExtDHashMap.Basic
// Imports: public import Std.Data.DHashMap.Lemmas import all Std.Data.DHashMap.Lemmas
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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instForInOfForIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_clearCell___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_mk___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_mk___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_mk(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_mk___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_lift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_lift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_lift_u2082___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_lift_u2082(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_lift_u2082___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_pliftOn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_pliftOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_pliftOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_emptyWithCapacity___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_emptyWithCapacity___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_emptyWithCapacity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_emptyWithCapacity___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_ExtDHashMap_instEmptyCollection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtDHashMap_instEmptyCollection___closed__0;
static lean_once_cell_t l_Std_ExtDHashMap_instEmptyCollection___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtDHashMap_instEmptyCollection___closed__1;
static lean_once_cell_t l_Std_ExtDHashMap_instEmptyCollection___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtDHashMap_instEmptyCollection___closed__2;
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instEmptyCollection(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInhabited___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0;
static lean_once_cell_t l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__1;
static lean_once_cell_t l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__2;
static lean_once_cell_t l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insertIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_containsThenInsert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_containsThenInsert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_containsThenInsertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_containsThenInsertIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getThenInsertIfNew_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getThenInsertIfNew_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_contains___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instDecidableMem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_instDecidableMem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instDecidableMem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getThenInsertIfNew_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getThenInsertIfNew_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKeyD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_size(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_map___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filterMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filterMap___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filterMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filterMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_modify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_modify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_alter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_alter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insertMany___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertMany___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertManyIfNewUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_union___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtDHashMap_union___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtDHashMap_union___redArg___closed__0 = (const lean_object*)&l_Std_ExtDHashMap_union___redArg___closed__0_value;
static const lean_closure_object l_Std_ExtDHashMap_union___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtDHashMap_union___redArg___closed__1 = (const lean_object*)&l_Std_ExtDHashMap_union___redArg___closed__1_value;
static const lean_closure_object l_Std_ExtDHashMap_union___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtDHashMap_union___redArg___closed__2 = (const lean_object*)&l_Std_ExtDHashMap_union___redArg___closed__2_value;
static const lean_closure_object l_Std_ExtDHashMap_union___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtDHashMap_union___redArg___closed__3 = (const lean_object*)&l_Std_ExtDHashMap_union___redArg___closed__3_value;
static const lean_closure_object l_Std_ExtDHashMap_union___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtDHashMap_union___redArg___closed__4 = (const lean_object*)&l_Std_ExtDHashMap_union___redArg___closed__4_value;
static const lean_closure_object l_Std_ExtDHashMap_union___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtDHashMap_union___redArg___closed__5 = (const lean_object*)&l_Std_ExtDHashMap_union___redArg___closed__5_value;
static const lean_closure_object l_Std_ExtDHashMap_union___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtDHashMap_union___redArg___closed__6 = (const lean_object*)&l_Std_ExtDHashMap_union___redArg___closed__6_value;
static const lean_ctor_object l_Std_ExtDHashMap_union___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_ExtDHashMap_union___redArg___closed__0_value),((lean_object*)&l_Std_ExtDHashMap_union___redArg___closed__1_value)}};
static const lean_object* l_Std_ExtDHashMap_union___redArg___closed__7 = (const lean_object*)&l_Std_ExtDHashMap_union___redArg___closed__7_value;
static const lean_ctor_object l_Std_ExtDHashMap_union___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_ExtDHashMap_union___redArg___closed__7_value),((lean_object*)&l_Std_ExtDHashMap_union___redArg___closed__2_value),((lean_object*)&l_Std_ExtDHashMap_union___redArg___closed__3_value),((lean_object*)&l_Std_ExtDHashMap_union___redArg___closed__4_value),((lean_object*)&l_Std_ExtDHashMap_union___redArg___closed__5_value)}};
static const lean_object* l_Std_ExtDHashMap_union___redArg___closed__8 = (const lean_object*)&l_Std_ExtDHashMap_union___redArg___closed__8_value;
static const lean_ctor_object l_Std_ExtDHashMap_union___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_ExtDHashMap_union___redArg___closed__8_value),((lean_object*)&l_Std_ExtDHashMap_union___redArg___closed__6_value)}};
static const lean_object* l_Std_ExtDHashMap_union___redArg___closed__9 = (const lean_object*)&l_Std_ExtDHashMap_union___redArg___closed__9_value;
static const lean_closure_object l_Std_ExtDHashMap_union___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_ExtDHashMap_union___redArg___closed__9_value)} };
static const lean_object* l_Std_ExtDHashMap_union___redArg___closed__10 = (const lean_object*)&l_Std_ExtDHashMap_union___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_union___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_union(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instUnionOfEquivBEqOfLawfulHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instUnionOfEquivBEqOfLawfulHashable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instBEqOfLawfulBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_beq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_Const_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_inter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInterOfEquivBEqOfLawfulHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInterOfEquivBEqOfLawfulHashable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_diff___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_diff___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_diff___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_diff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instSDiffOfEquivBEqOfLawfulHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instSDiffOfEquivBEqOfLawfulHashable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_ExtDHashMap_union___redArg___closed__9_value)} };
static const lean_object* l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__0 = (const lean_object*)&l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__0_value;
static const lean_closure_object l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__0_value)} };
static const lean_object* l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__1 = (const lean_object*)&l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__1_value;
static lean_once_cell_t l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__2;
static lean_once_cell_t l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_unitOfArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_unitOfArray(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtDHashMap_ofList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_ExtDHashMap_union___redArg___closed__9_value)} };
static const lean_object* l_Std_ExtDHashMap_ofList___redArg___closed__0 = (const lean_object*)&l_Std_ExtDHashMap_ofList___redArg___closed__0_value;
static const lean_closure_object l_Std_ExtDHashMap_ofList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_ExtDHashMap_ofList___redArg___closed__0_value)} };
static const lean_object* l_Std_ExtDHashMap_ofList___redArg___closed__1 = (const lean_object*)&l_Std_ExtDHashMap_ofList___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_ofList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_ofList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_ofList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_ofList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_unitOfList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_unitOfList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_mk___redArg(lean_object* v_m_1_){
_start:
{
lean_inc_ref(v_m_1_);
return v_m_1_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_mk___redArg___boxed(lean_object* v_m_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l_Std_ExtDHashMap_mk___redArg(v_m_2_);
lean_dec_ref(v_m_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_mk(lean_object* v_00_u03b1_4_, lean_object* v_00_u03b2_5_, lean_object* v_x_6_, lean_object* v_x_7_, lean_object* v_m_8_){
_start:
{
lean_inc_ref(v_m_8_);
return v_m_8_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_mk___boxed(lean_object* v_00_u03b1_9_, lean_object* v_00_u03b2_10_, lean_object* v_x_11_, lean_object* v_x_12_, lean_object* v_m_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_ExtDHashMap_mk(v_00_u03b1_9_, v_00_u03b2_10_, v_x_11_, v_x_12_, v_m_13_);
lean_dec_ref(v_m_13_);
lean_dec_ref(v_x_12_);
lean_dec_ref(v_x_11_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_lift___redArg(lean_object* v_f_15_, lean_object* v_m_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_apply_1(v_f_15_, v_m_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_lift(lean_object* v_00_u03b1_18_, lean_object* v_00_u03b2_19_, lean_object* v_x_20_, lean_object* v_x_21_, lean_object* v_00_u03b3_22_, lean_object* v_f_23_, lean_object* v_h_24_, lean_object* v_m_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lean_apply_1(v_f_23_, v_m_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_lift___boxed(lean_object* v_00_u03b1_27_, lean_object* v_00_u03b2_28_, lean_object* v_x_29_, lean_object* v_x_30_, lean_object* v_00_u03b3_31_, lean_object* v_f_32_, lean_object* v_h_33_, lean_object* v_m_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Std_ExtDHashMap_lift(v_00_u03b1_27_, v_00_u03b2_28_, v_x_29_, v_x_30_, v_00_u03b3_31_, v_f_32_, v_h_33_, v_m_34_);
lean_dec_ref(v_x_30_);
lean_dec_ref(v_x_29_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_lift_u2082___redArg(lean_object* v_f_36_, lean_object* v_m_u2081_37_, lean_object* v_m_u2082_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lean_apply_2(v_f_36_, v_m_u2081_37_, v_m_u2082_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_lift_u2082(lean_object* v_00_u03b1_40_, lean_object* v_00_u03b2_41_, lean_object* v_x_42_, lean_object* v_x_43_, lean_object* v_00_u03b3_44_, lean_object* v_f_45_, lean_object* v_h_46_, lean_object* v_m_u2081_47_, lean_object* v_m_u2082_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_apply_2(v_f_45_, v_m_u2081_47_, v_m_u2082_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_lift_u2082___boxed(lean_object* v_00_u03b1_50_, lean_object* v_00_u03b2_51_, lean_object* v_x_52_, lean_object* v_x_53_, lean_object* v_00_u03b3_54_, lean_object* v_f_55_, lean_object* v_h_56_, lean_object* v_m_u2081_57_, lean_object* v_m_u2082_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Std_ExtDHashMap_lift_u2082(v_00_u03b1_50_, v_00_u03b2_51_, v_x_52_, v_x_53_, v_00_u03b3_54_, v_f_55_, v_h_56_, v_m_u2081_57_, v_m_u2082_58_);
lean_dec_ref(v_x_53_);
lean_dec_ref(v_x_52_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_pliftOn___redArg(lean_object* v_m_60_, lean_object* v_f_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = lean_apply_2(v_f_61_, v_m_60_, lean_box(0));
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_pliftOn(lean_object* v_00_u03b1_63_, lean_object* v_00_u03b2_64_, lean_object* v_x_65_, lean_object* v_x_66_, lean_object* v_00_u03b3_67_, lean_object* v_m_68_, lean_object* v_f_69_, lean_object* v_h_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lean_apply_2(v_f_69_, v_m_68_, lean_box(0));
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_pliftOn___boxed(lean_object* v_00_u03b1_72_, lean_object* v_00_u03b2_73_, lean_object* v_x_74_, lean_object* v_x_75_, lean_object* v_00_u03b3_76_, lean_object* v_m_77_, lean_object* v_f_78_, lean_object* v_h_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Std_ExtDHashMap_pliftOn(v_00_u03b1_72_, v_00_u03b2_73_, v_x_74_, v_x_75_, v_00_u03b3_76_, v_m_77_, v_f_78_, v_h_79_);
lean_dec_ref(v_x_75_);
lean_dec_ref(v_x_74_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_emptyWithCapacity___redArg(lean_object* v_capacity_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v_cellCount_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_82_ = lean_unsigned_to_nat(4u);
v___x_83_ = lean_nat_mul(v_capacity_81_, v___x_82_);
v___x_84_ = lean_unsigned_to_nat(2u);
v___x_85_ = lean_nat_add(v___x_83_, v___x_84_);
lean_dec(v___x_83_);
v___x_86_ = lean_unsigned_to_nat(3u);
v___x_87_ = lean_nat_div(v___x_85_, v___x_86_);
lean_dec(v___x_85_);
v_cellCount_88_ = l_Nat_nextPowerOfTwo(v___x_87_);
lean_dec(v___x_87_);
v___x_89_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_88_);
v___x_90_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_88_);
v___x_91_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_88_);
v___x_92_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_92_, 0, v___x_89_);
lean_ctor_set(v___x_92_, 1, v___x_90_);
lean_ctor_set(v___x_92_, 2, v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_emptyWithCapacity___redArg___boxed(lean_object* v_capacity_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Std_ExtDHashMap_emptyWithCapacity___redArg(v_capacity_93_);
lean_dec(v_capacity_93_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_emptyWithCapacity(lean_object* v_00_u03b1_95_, lean_object* v_00_u03b2_96_, lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_capacity_99_){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v_cellCount_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_100_ = lean_unsigned_to_nat(4u);
v___x_101_ = lean_nat_mul(v_capacity_99_, v___x_100_);
v___x_102_ = lean_unsigned_to_nat(2u);
v___x_103_ = lean_nat_add(v___x_101_, v___x_102_);
lean_dec(v___x_101_);
v___x_104_ = lean_unsigned_to_nat(3u);
v___x_105_ = lean_nat_div(v___x_103_, v___x_104_);
lean_dec(v___x_103_);
v_cellCount_106_ = l_Nat_nextPowerOfTwo(v___x_105_);
lean_dec(v___x_105_);
v___x_107_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_106_);
v___x_108_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_106_);
v___x_109_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_106_);
v___x_110_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_110_, 0, v___x_107_);
lean_ctor_set(v___x_110_, 1, v___x_108_);
lean_ctor_set(v___x_110_, 2, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_emptyWithCapacity___boxed(lean_object* v_00_u03b1_111_, lean_object* v_00_u03b2_112_, lean_object* v_inst_113_, lean_object* v_inst_114_, lean_object* v_capacity_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Std_ExtDHashMap_emptyWithCapacity(v_00_u03b1_111_, v_00_u03b2_112_, v_inst_113_, v_inst_114_, v_capacity_115_);
lean_dec(v_capacity_115_);
lean_dec_ref(v_inst_114_);
lean_dec_ref(v_inst_113_);
return v_res_116_;
}
}
static lean_object* _init_l_Std_ExtDHashMap_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v_cellCount_117_; lean_object* v___x_118_; 
v_cellCount_117_ = lean_unsigned_to_nat(16u);
v___x_118_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_117_);
return v___x_118_;
}
}
static lean_object* _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1(void){
_start:
{
lean_object* v_cellCount_119_; lean_object* v___x_120_; 
v_cellCount_119_ = lean_unsigned_to_nat(16u);
v___x_120_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_119_);
return v___x_120_;
}
}
static lean_object* _init_l_Std_ExtDHashMap_instEmptyCollection___closed__2(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_121_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1);
v___x_122_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___closed__0, &l_Std_ExtDHashMap_instEmptyCollection___closed__0_once, _init_l_Std_ExtDHashMap_instEmptyCollection___closed__0);
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
lean_ctor_set(v___x_124_, 1, v___x_122_);
lean_ctor_set(v___x_124_, 2, v___x_121_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instEmptyCollection(lean_object* v_00_u03b1_125_, lean_object* v_00_u03b2_126_, lean_object* v_inst_127_, lean_object* v_inst_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___closed__2, &l_Std_ExtDHashMap_instEmptyCollection___closed__2_once, _init_l_Std_ExtDHashMap_instEmptyCollection___closed__2);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instEmptyCollection___boxed(lean_object* v_00_u03b1_130_, lean_object* v_00_u03b2_131_, lean_object* v_inst_132_, lean_object* v_inst_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Std_ExtDHashMap_instEmptyCollection(v_00_u03b1_130_, v_00_u03b2_131_, v_inst_132_, v_inst_133_);
lean_dec_ref(v_inst_133_);
lean_dec_ref(v_inst_132_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInhabited(lean_object* v_00_u03b1_135_, lean_object* v_00_u03b2_136_, lean_object* v_inst_137_, lean_object* v_inst_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___closed__2, &l_Std_ExtDHashMap_instEmptyCollection___closed__2_once, _init_l_Std_ExtDHashMap_instEmptyCollection___closed__2);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInhabited___boxed(lean_object* v_00_u03b1_140_, lean_object* v_00_u03b2_141_, lean_object* v_inst_142_, lean_object* v_inst_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Std_ExtDHashMap_instInhabited(v_00_u03b1_140_, v_00_u03b2_141_, v_inst_142_, v_inst_143_);
lean_dec_ref(v_inst_143_);
lean_dec_ref(v_inst_142_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insert___redArg(lean_object* v_x_145_, lean_object* v_x_146_, lean_object* v_m_147_, lean_object* v_a_148_, lean_object* v_b_149_){
_start:
{
lean_object* v___y_151_; lean_object* v_i_152_; lean_object* v___y_168_; lean_object* v_i_169_; lean_object* v___y_175_; lean_object* v___x_184_; 
lean_inc(v_a_148_);
lean_inc_ref(v_x_146_);
lean_inc_ref(v_x_145_);
v___x_184_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_145_, v_x_146_, v_m_147_, v_a_148_);
switch(lean_obj_tag(v___x_184_))
{
case 0:
{
lean_object* v_index_185_; lean_object* v_size_186_; lean_object* v___x_187_; 
lean_dec_ref(v_x_146_);
lean_dec_ref(v_x_145_);
v_index_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_index_185_);
lean_dec_ref_known(v___x_184_, 3);
v_size_186_ = lean_ctor_get(v_m_147_, 0);
lean_inc(v_size_186_);
v___x_187_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_147_, v_size_186_, v_index_185_, v_a_148_, v_b_149_);
lean_dec(v_index_185_);
return v___x_187_;
}
case 1:
{
lean_object* v_index_188_; lean_object* v_size_189_; lean_object* v_keyArray_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v_index_188_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_index_188_);
lean_dec_ref_known(v___x_184_, 1);
v_size_189_ = lean_ctor_get(v_m_147_, 0);
v_keyArray_190_ = lean_ctor_get(v_m_147_, 1);
v___x_191_ = lean_unsigned_to_nat(1u);
v___x_192_ = lean_nat_add(v_size_189_, v___x_191_);
v___x_193_ = lean_array_get_size(v_keyArray_190_);
v___x_194_ = lean_nat_dec_lt(v___x_192_, v___x_193_);
if (v___x_194_ == 0)
{
lean_dec(v___x_192_);
lean_dec(v_index_188_);
goto v___jp_157_;
}
else
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_195_ = lean_unsigned_to_nat(4u);
v___x_196_ = lean_nat_mul(v___x_192_, v___x_195_);
v___x_197_ = lean_unsigned_to_nat(3u);
v___x_198_ = lean_nat_mul(v___x_193_, v___x_197_);
v___x_199_ = lean_nat_dec_le(v___x_196_, v___x_198_);
lean_dec(v___x_198_);
lean_dec(v___x_196_);
if (v___x_199_ == 0)
{
lean_dec(v___x_192_);
lean_dec(v_index_188_);
goto v___jp_157_;
}
else
{
lean_object* v___x_200_; 
lean_dec_ref(v_x_146_);
lean_dec_ref(v_x_145_);
v___x_200_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_147_, v___x_192_, v_index_188_, v_a_148_, v_b_149_);
lean_dec(v_index_188_);
return v___x_200_;
}
}
}
default: 
{
lean_object* v_size_201_; lean_object* v_keyArray_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
v_size_201_ = lean_ctor_get(v_m_147_, 0);
v_keyArray_202_ = lean_ctor_get(v_m_147_, 1);
v___x_203_ = lean_unsigned_to_nat(1u);
v___x_204_ = lean_nat_add(v_size_201_, v___x_203_);
v___x_205_ = lean_array_get_size(v_keyArray_202_);
v___x_206_ = lean_nat_dec_lt(v___x_204_, v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; 
lean_dec(v___x_204_);
lean_inc_ref(v_x_146_);
lean_inc_ref(v_x_145_);
v___x_207_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_145_, v_x_146_, v_m_147_);
v___y_175_ = v___x_207_;
goto v___jp_174_;
}
else
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_208_ = lean_unsigned_to_nat(4u);
v___x_209_ = lean_nat_mul(v___x_204_, v___x_208_);
lean_dec(v___x_204_);
v___x_210_ = lean_unsigned_to_nat(3u);
v___x_211_ = lean_nat_mul(v___x_205_, v___x_210_);
v___x_212_ = lean_nat_dec_le(v___x_209_, v___x_211_);
lean_dec(v___x_211_);
lean_dec(v___x_209_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; 
lean_inc_ref(v_x_146_);
lean_inc_ref(v_x_145_);
v___x_213_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_145_, v_x_146_, v_m_147_);
v___y_175_ = v___x_213_;
goto v___jp_174_;
}
else
{
v___y_175_ = v_m_147_;
goto v___jp_174_;
}
}
}
}
v___jp_150_:
{
lean_object* v_size_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v_size_153_ = lean_ctor_get(v___y_151_, 0);
v___x_154_ = lean_unsigned_to_nat(1u);
v___x_155_ = lean_nat_add(v_size_153_, v___x_154_);
v___x_156_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_151_, v___x_155_, v_i_152_, v_a_148_, v_b_149_);
lean_dec(v_i_152_);
return v___x_156_;
}
v___jp_157_:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
lean_inc_ref(v_x_146_);
lean_inc_ref(v_x_145_);
v___x_158_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_145_, v_x_146_, v_m_147_);
lean_inc(v_a_148_);
v___x_159_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_145_, v_x_146_, v___x_158_, v_a_148_);
switch(lean_obj_tag(v___x_159_))
{
case 0:
{
lean_object* v_index_160_; lean_object* v_size_161_; lean_object* v___x_162_; 
v_index_160_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_index_160_);
lean_dec_ref_known(v___x_159_, 3);
v_size_161_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_size_161_);
v___x_162_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_158_, v_size_161_, v_index_160_, v_a_148_, v_b_149_);
lean_dec(v_index_160_);
return v___x_162_;
}
case 1:
{
lean_object* v_index_163_; 
v_index_163_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_index_163_);
lean_dec_ref_known(v___x_159_, 1);
v___y_151_ = v___x_158_;
v_i_152_ = v_index_163_;
goto v___jp_150_;
}
default: 
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_158_, v___x_164_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v_index_166_; 
v_index_166_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_index_166_);
lean_dec_ref_known(v___x_165_, 1);
v___y_151_ = v___x_158_;
v_i_152_ = v_index_166_;
goto v___jp_150_;
}
else
{
lean_dec(v_b_149_);
lean_dec(v_a_148_);
return v___x_158_;
}
}
}
}
v___jp_167_:
{
lean_object* v_size_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v_size_170_ = lean_ctor_get(v___y_168_, 0);
v___x_171_ = lean_unsigned_to_nat(1u);
v___x_172_ = lean_nat_add(v_size_170_, v___x_171_);
v___x_173_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_168_, v___x_172_, v_i_169_, v_a_148_, v_b_149_);
lean_dec(v_i_169_);
return v___x_173_;
}
v___jp_174_:
{
lean_object* v___x_176_; 
lean_inc(v_a_148_);
v___x_176_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_145_, v_x_146_, v___y_175_, v_a_148_);
switch(lean_obj_tag(v___x_176_))
{
case 0:
{
lean_object* v_index_177_; lean_object* v_size_178_; lean_object* v___x_179_; 
v_index_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_index_177_);
lean_dec_ref_known(v___x_176_, 3);
v_size_178_ = lean_ctor_get(v___y_175_, 0);
lean_inc(v_size_178_);
v___x_179_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_175_, v_size_178_, v_index_177_, v_a_148_, v_b_149_);
lean_dec(v_index_177_);
return v___x_179_;
}
case 1:
{
lean_object* v_index_180_; 
v_index_180_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_index_180_);
lean_dec_ref_known(v___x_176_, 1);
v___y_168_ = v___y_175_;
v_i_169_ = v_index_180_;
goto v___jp_167_;
}
default: 
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_unsigned_to_nat(0u);
v___x_182_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_175_, v___x_181_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_index_183_; 
v_index_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_index_183_);
lean_dec_ref_known(v___x_182_, 1);
v___y_168_ = v___y_175_;
v_i_169_ = v_index_183_;
goto v___jp_167_;
}
else
{
lean_dec(v_b_149_);
lean_dec(v_a_148_);
return v___y_175_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insert(lean_object* v_00_u03b1_214_, lean_object* v_00_u03b2_215_, lean_object* v_x_216_, lean_object* v_x_217_, lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_m_220_, lean_object* v_a_221_, lean_object* v_b_222_){
_start:
{
lean_object* v___y_224_; lean_object* v_i_225_; lean_object* v___y_241_; lean_object* v_i_242_; lean_object* v___y_248_; lean_object* v___x_257_; 
lean_inc(v_a_221_);
lean_inc_ref(v_x_217_);
lean_inc_ref(v_x_216_);
v___x_257_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_216_, v_x_217_, v_m_220_, v_a_221_);
switch(lean_obj_tag(v___x_257_))
{
case 0:
{
lean_object* v_index_258_; lean_object* v_size_259_; lean_object* v___x_260_; 
lean_dec_ref(v_x_217_);
lean_dec_ref(v_x_216_);
v_index_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_index_258_);
lean_dec_ref_known(v___x_257_, 3);
v_size_259_ = lean_ctor_get(v_m_220_, 0);
lean_inc(v_size_259_);
v___x_260_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_220_, v_size_259_, v_index_258_, v_a_221_, v_b_222_);
lean_dec(v_index_258_);
return v___x_260_;
}
case 1:
{
lean_object* v_index_261_; lean_object* v_size_262_; lean_object* v_keyArray_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v_index_261_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_index_261_);
lean_dec_ref_known(v___x_257_, 1);
v_size_262_ = lean_ctor_get(v_m_220_, 0);
v_keyArray_263_ = lean_ctor_get(v_m_220_, 1);
v___x_264_ = lean_unsigned_to_nat(1u);
v___x_265_ = lean_nat_add(v_size_262_, v___x_264_);
v___x_266_ = lean_array_get_size(v_keyArray_263_);
v___x_267_ = lean_nat_dec_lt(v___x_265_, v___x_266_);
if (v___x_267_ == 0)
{
lean_dec(v___x_265_);
lean_dec(v_index_261_);
goto v___jp_230_;
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_268_ = lean_unsigned_to_nat(4u);
v___x_269_ = lean_nat_mul(v___x_265_, v___x_268_);
v___x_270_ = lean_unsigned_to_nat(3u);
v___x_271_ = lean_nat_mul(v___x_266_, v___x_270_);
v___x_272_ = lean_nat_dec_le(v___x_269_, v___x_271_);
lean_dec(v___x_271_);
lean_dec(v___x_269_);
if (v___x_272_ == 0)
{
lean_dec(v___x_265_);
lean_dec(v_index_261_);
goto v___jp_230_;
}
else
{
lean_object* v___x_273_; 
lean_dec_ref(v_x_217_);
lean_dec_ref(v_x_216_);
v___x_273_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_220_, v___x_265_, v_index_261_, v_a_221_, v_b_222_);
lean_dec(v_index_261_);
return v___x_273_;
}
}
}
default: 
{
lean_object* v_size_274_; lean_object* v_keyArray_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v_size_274_ = lean_ctor_get(v_m_220_, 0);
v_keyArray_275_ = lean_ctor_get(v_m_220_, 1);
v___x_276_ = lean_unsigned_to_nat(1u);
v___x_277_ = lean_nat_add(v_size_274_, v___x_276_);
v___x_278_ = lean_array_get_size(v_keyArray_275_);
v___x_279_ = lean_nat_dec_lt(v___x_277_, v___x_278_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; 
lean_dec(v___x_277_);
lean_inc_ref(v_x_217_);
lean_inc_ref(v_x_216_);
v___x_280_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_216_, v_x_217_, v_m_220_);
v___y_248_ = v___x_280_;
goto v___jp_247_;
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_281_ = lean_unsigned_to_nat(4u);
v___x_282_ = lean_nat_mul(v___x_277_, v___x_281_);
lean_dec(v___x_277_);
v___x_283_ = lean_unsigned_to_nat(3u);
v___x_284_ = lean_nat_mul(v___x_278_, v___x_283_);
v___x_285_ = lean_nat_dec_le(v___x_282_, v___x_284_);
lean_dec(v___x_284_);
lean_dec(v___x_282_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; 
lean_inc_ref(v_x_217_);
lean_inc_ref(v_x_216_);
v___x_286_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_216_, v_x_217_, v_m_220_);
v___y_248_ = v___x_286_;
goto v___jp_247_;
}
else
{
v___y_248_ = v_m_220_;
goto v___jp_247_;
}
}
}
}
v___jp_223_:
{
lean_object* v_size_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_size_226_ = lean_ctor_get(v___y_224_, 0);
v___x_227_ = lean_unsigned_to_nat(1u);
v___x_228_ = lean_nat_add(v_size_226_, v___x_227_);
v___x_229_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_224_, v___x_228_, v_i_225_, v_a_221_, v_b_222_);
lean_dec(v_i_225_);
return v___x_229_;
}
v___jp_230_:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
lean_inc_ref(v_x_217_);
lean_inc_ref(v_x_216_);
v___x_231_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_216_, v_x_217_, v_m_220_);
lean_inc(v_a_221_);
v___x_232_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_216_, v_x_217_, v___x_231_, v_a_221_);
switch(lean_obj_tag(v___x_232_))
{
case 0:
{
lean_object* v_index_233_; lean_object* v_size_234_; lean_object* v___x_235_; 
v_index_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_index_233_);
lean_dec_ref_known(v___x_232_, 3);
v_size_234_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_size_234_);
v___x_235_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_231_, v_size_234_, v_index_233_, v_a_221_, v_b_222_);
lean_dec(v_index_233_);
return v___x_235_;
}
case 1:
{
lean_object* v_index_236_; 
v_index_236_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_index_236_);
lean_dec_ref_known(v___x_232_, 1);
v___y_224_ = v___x_231_;
v_i_225_ = v_index_236_;
goto v___jp_223_;
}
default: 
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = lean_unsigned_to_nat(0u);
v___x_238_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_231_, v___x_237_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_index_239_; 
v_index_239_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_index_239_);
lean_dec_ref_known(v___x_238_, 1);
v___y_224_ = v___x_231_;
v_i_225_ = v_index_239_;
goto v___jp_223_;
}
else
{
lean_dec(v_b_222_);
lean_dec(v_a_221_);
return v___x_231_;
}
}
}
}
v___jp_240_:
{
lean_object* v_size_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v_size_243_ = lean_ctor_get(v___y_241_, 0);
v___x_244_ = lean_unsigned_to_nat(1u);
v___x_245_ = lean_nat_add(v_size_243_, v___x_244_);
v___x_246_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_241_, v___x_245_, v_i_242_, v_a_221_, v_b_222_);
lean_dec(v_i_242_);
return v___x_246_;
}
v___jp_247_:
{
lean_object* v___x_249_; 
lean_inc(v_a_221_);
v___x_249_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_216_, v_x_217_, v___y_248_, v_a_221_);
switch(lean_obj_tag(v___x_249_))
{
case 0:
{
lean_object* v_index_250_; lean_object* v_size_251_; lean_object* v___x_252_; 
v_index_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_index_250_);
lean_dec_ref_known(v___x_249_, 3);
v_size_251_ = lean_ctor_get(v___y_248_, 0);
lean_inc(v_size_251_);
v___x_252_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_248_, v_size_251_, v_index_250_, v_a_221_, v_b_222_);
lean_dec(v_index_250_);
return v___x_252_;
}
case 1:
{
lean_object* v_index_253_; 
v_index_253_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_index_253_);
lean_dec_ref_known(v___x_249_, 1);
v___y_241_ = v___y_248_;
v_i_242_ = v_index_253_;
goto v___jp_240_;
}
default: 
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_unsigned_to_nat(0u);
v___x_255_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_248_, v___x_254_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_index_256_; 
v_index_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_index_256_);
lean_dec_ref_known(v___x_255_, 1);
v___y_241_ = v___y_248_;
v_i_242_ = v_index_256_;
goto v___jp_240_;
}
else
{
lean_dec(v_b_222_);
lean_dec(v_a_221_);
return v___y_248_;
}
}
}
}
}
}
static lean_object* _init_l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___closed__0, &l_Std_ExtDHashMap_instEmptyCollection___closed__0_once, _init_l_Std_ExtDHashMap_instEmptyCollection___closed__0);
v___x_288_ = lean_array_get_size(v___x_287_);
return v___x_288_;
}
}
static uint8_t _init_l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_289_ = lean_obj_once(&l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0, &l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0_once, _init_l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0);
v___x_290_ = lean_unsigned_to_nat(1u);
v___x_291_ = lean_nat_dec_lt(v___x_290_, v___x_289_);
return v___x_291_;
}
}
static lean_object* _init_l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_292_ = lean_unsigned_to_nat(3u);
v___x_293_ = lean_obj_once(&l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0, &l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0_once, _init_l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0);
v___x_294_ = lean_nat_mul(v___x_293_, v___x_292_);
return v___x_294_;
}
}
static uint8_t _init_l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_295_ = lean_obj_once(&l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__2, &l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__2_once, _init_l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__2);
v___x_296_ = lean_unsigned_to_nat(4u);
v___x_297_ = lean_nat_dec_le(v___x_296_, v___x_295_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_298_, lean_object* v_x_299_, lean_object* v_x_300_){
_start:
{
lean_object* v_fst_301_; lean_object* v_snd_302_; lean_object* v___y_304_; lean_object* v_i_305_; lean_object* v___y_311_; lean_object* v_i_312_; lean_object* v___y_318_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_338_; 
v_fst_301_ = lean_ctor_get(v_x_300_, 0);
lean_inc_n(v_fst_301_, 2);
v_snd_302_ = lean_ctor_get(v_x_300_, 1);
lean_inc(v_snd_302_);
lean_dec_ref(v_x_300_);
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___closed__2, &l_Std_ExtDHashMap_instEmptyCollection___closed__2_once, _init_l_Std_ExtDHashMap_instEmptyCollection___closed__2);
lean_inc_ref(v_x_299_);
lean_inc_ref(v_x_298_);
v___x_338_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_298_, v_x_299_, v___x_328_, v_fst_301_);
switch(lean_obj_tag(v___x_338_))
{
case 0:
{
lean_object* v_index_339_; lean_object* v___x_340_; 
lean_dec_ref(v_x_299_);
lean_dec_ref(v_x_298_);
v_index_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_index_339_);
lean_dec_ref_known(v___x_338_, 3);
v___x_340_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_328_, v___x_327_, v_index_339_, v_fst_301_, v_snd_302_);
lean_dec(v_index_339_);
return v___x_340_;
}
case 1:
{
lean_object* v_index_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v_index_341_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_index_341_);
lean_dec_ref_known(v___x_338_, 1);
v___x_342_ = lean_unsigned_to_nat(1u);
v___x_343_ = lean_uint8_once(&l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__1, &l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__1_once, _init_l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__1);
if (v___x_343_ == 0)
{
lean_dec(v_index_341_);
goto v___jp_329_;
}
else
{
uint8_t v___x_344_; 
v___x_344_ = lean_uint8_once(&l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__3, &l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__3_once, _init_l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__3);
if (v___x_344_ == 0)
{
lean_dec(v_index_341_);
goto v___jp_329_;
}
else
{
lean_object* v___x_345_; 
lean_dec_ref(v_x_299_);
lean_dec_ref(v_x_298_);
v___x_345_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_328_, v___x_342_, v_index_341_, v_fst_301_, v_snd_302_);
lean_dec(v_index_341_);
return v___x_345_;
}
}
}
default: 
{
uint8_t v___x_346_; 
v___x_346_ = lean_uint8_once(&l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__1, &l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__1_once, _init_l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__1);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; 
lean_inc_ref(v_x_299_);
lean_inc_ref(v_x_298_);
v___x_347_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_298_, v_x_299_, v___x_328_);
v___y_318_ = v___x_347_;
goto v___jp_317_;
}
else
{
uint8_t v___x_348_; 
v___x_348_ = lean_uint8_once(&l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__3, &l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__3_once, _init_l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__3);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; 
lean_inc_ref(v_x_299_);
lean_inc_ref(v_x_298_);
v___x_349_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_298_, v_x_299_, v___x_328_);
v___y_318_ = v___x_349_;
goto v___jp_317_;
}
else
{
v___y_318_ = v___x_328_;
goto v___jp_317_;
}
}
}
}
v___jp_303_:
{
lean_object* v_size_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v_size_306_ = lean_ctor_get(v___y_304_, 0);
v___x_307_ = lean_unsigned_to_nat(1u);
v___x_308_ = lean_nat_add(v_size_306_, v___x_307_);
v___x_309_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_304_, v___x_308_, v_i_305_, v_fst_301_, v_snd_302_);
lean_dec(v_i_305_);
return v___x_309_;
}
v___jp_310_:
{
lean_object* v_size_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v_size_313_ = lean_ctor_get(v___y_311_, 0);
v___x_314_ = lean_unsigned_to_nat(1u);
v___x_315_ = lean_nat_add(v_size_313_, v___x_314_);
v___x_316_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_311_, v___x_315_, v_i_312_, v_fst_301_, v_snd_302_);
lean_dec(v_i_312_);
return v___x_316_;
}
v___jp_317_:
{
lean_object* v___x_319_; 
lean_inc(v_fst_301_);
v___x_319_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_298_, v_x_299_, v___y_318_, v_fst_301_);
switch(lean_obj_tag(v___x_319_))
{
case 0:
{
lean_object* v_index_320_; lean_object* v_size_321_; lean_object* v___x_322_; 
v_index_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_index_320_);
lean_dec_ref_known(v___x_319_, 3);
v_size_321_ = lean_ctor_get(v___y_318_, 0);
lean_inc(v_size_321_);
v___x_322_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_318_, v_size_321_, v_index_320_, v_fst_301_, v_snd_302_);
lean_dec(v_index_320_);
return v___x_322_;
}
case 1:
{
lean_object* v_index_323_; 
v_index_323_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_index_323_);
lean_dec_ref_known(v___x_319_, 1);
v___y_311_ = v___y_318_;
v_i_312_ = v_index_323_;
goto v___jp_310_;
}
default: 
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_unsigned_to_nat(0u);
v___x_325_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_318_, v___x_324_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_index_326_; 
v_index_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_index_326_);
lean_dec_ref_known(v___x_325_, 1);
v___y_311_ = v___y_318_;
v_i_312_ = v_index_326_;
goto v___jp_310_;
}
else
{
lean_dec(v_snd_302_);
lean_dec(v_fst_301_);
return v___y_318_;
}
}
}
}
v___jp_329_:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
lean_inc_ref(v_x_299_);
lean_inc_ref(v_x_298_);
v___x_330_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_298_, v_x_299_, v___x_328_);
lean_inc(v_fst_301_);
v___x_331_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_298_, v_x_299_, v___x_330_, v_fst_301_);
switch(lean_obj_tag(v___x_331_))
{
case 0:
{
lean_object* v_index_332_; lean_object* v_size_333_; lean_object* v___x_334_; 
v_index_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_index_332_);
lean_dec_ref_known(v___x_331_, 3);
v_size_333_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_size_333_);
v___x_334_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_330_, v_size_333_, v_index_332_, v_fst_301_, v_snd_302_);
lean_dec(v_index_332_);
return v___x_334_;
}
case 1:
{
lean_object* v_index_335_; 
v_index_335_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_index_335_);
lean_dec_ref_known(v___x_331_, 1);
v___y_304_ = v___x_330_;
v_i_305_ = v_index_335_;
goto v___jp_303_;
}
default: 
{
lean_object* v___x_336_; 
v___x_336_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_330_, v___x_327_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_index_337_; 
v_index_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_index_337_);
lean_dec_ref_known(v___x_336_, 1);
v___y_304_ = v___x_330_;
v_i_305_ = v_index_337_;
goto v___jp_303_;
}
else
{
lean_dec(v_snd_302_);
lean_dec(v_fst_301_);
return v___x_330_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_350_, lean_object* v_x_351_){
_start:
{
lean_object* v___f_352_; 
v___f_352_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_352_, 0, v_x_350_);
lean_closure_set(v___f_352_, 1, v_x_351_);
return v___f_352_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_353_, lean_object* v_00_u03b2_354_, lean_object* v_x_355_, lean_object* v_x_356_, lean_object* v_inst_357_, lean_object* v_inst_358_){
_start:
{
lean_object* v___f_359_; 
v___f_359_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_359_, 0, v_x_355_);
lean_closure_set(v___f_359_, 1, v_x_356_);
return v___f_359_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_360_, lean_object* v_x_361_, lean_object* v_x_362_, lean_object* v_x_363_){
_start:
{
lean_object* v_fst_364_; lean_object* v_snd_365_; lean_object* v___y_367_; lean_object* v_i_368_; lean_object* v___y_374_; lean_object* v___y_384_; lean_object* v_i_385_; lean_object* v___x_400_; 
v_fst_364_ = lean_ctor_get(v_x_362_, 0);
lean_inc_n(v_fst_364_, 2);
v_snd_365_ = lean_ctor_get(v_x_362_, 1);
lean_inc(v_snd_365_);
lean_dec_ref(v_x_362_);
lean_inc_ref(v_x_361_);
lean_inc_ref(v_x_360_);
v___x_400_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_360_, v_x_361_, v_x_363_, v_fst_364_);
switch(lean_obj_tag(v___x_400_))
{
case 0:
{
lean_object* v_index_401_; lean_object* v_size_402_; lean_object* v___x_403_; 
lean_dec_ref(v_x_361_);
lean_dec_ref(v_x_360_);
v_index_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_index_401_);
lean_dec_ref_known(v___x_400_, 3);
v_size_402_ = lean_ctor_get(v_x_363_, 0);
lean_inc(v_size_402_);
v___x_403_ = l_Std_DHashMap_Raw_setEntry___redArg(v_x_363_, v_size_402_, v_index_401_, v_fst_364_, v_snd_365_);
lean_dec(v_index_401_);
return v___x_403_;
}
case 1:
{
lean_object* v_index_404_; lean_object* v_size_405_; lean_object* v_keyArray_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v_index_404_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_index_404_);
lean_dec_ref_known(v___x_400_, 1);
v_size_405_ = lean_ctor_get(v_x_363_, 0);
v_keyArray_406_ = lean_ctor_get(v_x_363_, 1);
v___x_407_ = lean_unsigned_to_nat(1u);
v___x_408_ = lean_nat_add(v_size_405_, v___x_407_);
v___x_409_ = lean_array_get_size(v_keyArray_406_);
v___x_410_ = lean_nat_dec_lt(v___x_408_, v___x_409_);
if (v___x_410_ == 0)
{
lean_dec(v___x_408_);
lean_dec(v_index_404_);
goto v___jp_390_;
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_411_ = lean_unsigned_to_nat(4u);
v___x_412_ = lean_nat_mul(v___x_408_, v___x_411_);
v___x_413_ = lean_unsigned_to_nat(3u);
v___x_414_ = lean_nat_mul(v___x_409_, v___x_413_);
v___x_415_ = lean_nat_dec_le(v___x_412_, v___x_414_);
lean_dec(v___x_414_);
lean_dec(v___x_412_);
if (v___x_415_ == 0)
{
lean_dec(v___x_408_);
lean_dec(v_index_404_);
goto v___jp_390_;
}
else
{
lean_object* v___x_416_; 
lean_dec_ref(v_x_361_);
lean_dec_ref(v_x_360_);
v___x_416_ = l_Std_DHashMap_Raw_setEntry___redArg(v_x_363_, v___x_408_, v_index_404_, v_fst_364_, v_snd_365_);
lean_dec(v_index_404_);
return v___x_416_;
}
}
}
default: 
{
lean_object* v_size_417_; lean_object* v_keyArray_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
v_size_417_ = lean_ctor_get(v_x_363_, 0);
v_keyArray_418_ = lean_ctor_get(v_x_363_, 1);
v___x_419_ = lean_unsigned_to_nat(1u);
v___x_420_ = lean_nat_add(v_size_417_, v___x_419_);
v___x_421_ = lean_array_get_size(v_keyArray_418_);
v___x_422_ = lean_nat_dec_lt(v___x_420_, v___x_421_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; 
lean_dec(v___x_420_);
lean_inc_ref(v_x_361_);
lean_inc_ref(v_x_360_);
v___x_423_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_360_, v_x_361_, v_x_363_);
v___y_374_ = v___x_423_;
goto v___jp_373_;
}
else
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_424_ = lean_unsigned_to_nat(4u);
v___x_425_ = lean_nat_mul(v___x_420_, v___x_424_);
lean_dec(v___x_420_);
v___x_426_ = lean_unsigned_to_nat(3u);
v___x_427_ = lean_nat_mul(v___x_421_, v___x_426_);
v___x_428_ = lean_nat_dec_le(v___x_425_, v___x_427_);
lean_dec(v___x_427_);
lean_dec(v___x_425_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; 
lean_inc_ref(v_x_361_);
lean_inc_ref(v_x_360_);
v___x_429_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_360_, v_x_361_, v_x_363_);
v___y_374_ = v___x_429_;
goto v___jp_373_;
}
else
{
v___y_374_ = v_x_363_;
goto v___jp_373_;
}
}
}
}
v___jp_366_:
{
lean_object* v_size_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v_size_369_ = lean_ctor_get(v___y_367_, 0);
v___x_370_ = lean_unsigned_to_nat(1u);
v___x_371_ = lean_nat_add(v_size_369_, v___x_370_);
v___x_372_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_367_, v___x_371_, v_i_368_, v_fst_364_, v_snd_365_);
lean_dec(v_i_368_);
return v___x_372_;
}
v___jp_373_:
{
lean_object* v___x_375_; 
lean_inc(v_fst_364_);
v___x_375_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_360_, v_x_361_, v___y_374_, v_fst_364_);
switch(lean_obj_tag(v___x_375_))
{
case 0:
{
lean_object* v_index_376_; lean_object* v_size_377_; lean_object* v___x_378_; 
v_index_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_index_376_);
lean_dec_ref_known(v___x_375_, 3);
v_size_377_ = lean_ctor_get(v___y_374_, 0);
lean_inc(v_size_377_);
v___x_378_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_374_, v_size_377_, v_index_376_, v_fst_364_, v_snd_365_);
lean_dec(v_index_376_);
return v___x_378_;
}
case 1:
{
lean_object* v_index_379_; 
v_index_379_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_index_379_);
lean_dec_ref_known(v___x_375_, 1);
v___y_367_ = v___y_374_;
v_i_368_ = v_index_379_;
goto v___jp_366_;
}
default: 
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_unsigned_to_nat(0u);
v___x_381_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_374_, v___x_380_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_index_382_; 
v_index_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_index_382_);
lean_dec_ref_known(v___x_381_, 1);
v___y_367_ = v___y_374_;
v_i_368_ = v_index_382_;
goto v___jp_366_;
}
else
{
lean_dec(v_snd_365_);
lean_dec(v_fst_364_);
return v___y_374_;
}
}
}
}
v___jp_383_:
{
lean_object* v_size_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v_size_386_ = lean_ctor_get(v___y_384_, 0);
v___x_387_ = lean_unsigned_to_nat(1u);
v___x_388_ = lean_nat_add(v_size_386_, v___x_387_);
v___x_389_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_384_, v___x_388_, v_i_385_, v_fst_364_, v_snd_365_);
lean_dec(v_i_385_);
return v___x_389_;
}
v___jp_390_:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
lean_inc_ref(v_x_361_);
lean_inc_ref(v_x_360_);
v___x_391_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_360_, v_x_361_, v_x_363_);
lean_inc(v_fst_364_);
v___x_392_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_360_, v_x_361_, v___x_391_, v_fst_364_);
switch(lean_obj_tag(v___x_392_))
{
case 0:
{
lean_object* v_index_393_; lean_object* v_size_394_; lean_object* v___x_395_; 
v_index_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_index_393_);
lean_dec_ref_known(v___x_392_, 3);
v_size_394_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_size_394_);
v___x_395_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_391_, v_size_394_, v_index_393_, v_fst_364_, v_snd_365_);
lean_dec(v_index_393_);
return v___x_395_;
}
case 1:
{
lean_object* v_index_396_; 
v_index_396_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_index_396_);
lean_dec_ref_known(v___x_392_, 1);
v___y_384_ = v___x_391_;
v_i_385_ = v_index_396_;
goto v___jp_383_;
}
default: 
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = lean_unsigned_to_nat(0u);
v___x_398_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_391_, v___x_397_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_index_399_; 
v_index_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_index_399_);
lean_dec_ref_known(v___x_398_, 1);
v___y_384_ = v___x_391_;
v_i_385_ = v_index_399_;
goto v___jp_383_;
}
else
{
lean_dec(v_snd_365_);
lean_dec(v_fst_364_);
return v___x_391_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_430_, lean_object* v_x_431_){
_start:
{
lean_object* v___f_432_; 
v___f_432_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_432_, 0, v_x_430_);
lean_closure_set(v___f_432_, 1, v_x_431_);
return v___f_432_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_433_, lean_object* v_00_u03b2_434_, lean_object* v_x_435_, lean_object* v_x_436_, lean_object* v_inst_437_, lean_object* v_inst_438_){
_start:
{
lean_object* v___f_439_; 
v___f_439_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_439_, 0, v_x_435_);
lean_closure_set(v___f_439_, 1, v_x_436_);
return v___f_439_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insertIfNew___redArg(lean_object* v_x_440_, lean_object* v_x_441_, lean_object* v_m_442_, lean_object* v_a_443_, lean_object* v_b_444_){
_start:
{
lean_object* v___y_446_; lean_object* v_i_447_; lean_object* v___y_463_; lean_object* v_i_464_; lean_object* v___y_470_; lean_object* v___x_479_; 
lean_inc(v_a_443_);
lean_inc_ref(v_x_441_);
lean_inc_ref(v_x_440_);
v___x_479_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_440_, v_x_441_, v_m_442_, v_a_443_);
switch(lean_obj_tag(v___x_479_))
{
case 0:
{
lean_dec_ref_known(v___x_479_, 3);
lean_dec(v_b_444_);
lean_dec(v_a_443_);
lean_dec_ref(v_x_441_);
lean_dec_ref(v_x_440_);
return v_m_442_;
}
case 1:
{
lean_object* v_index_480_; lean_object* v_size_481_; lean_object* v_keyArray_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v_index_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_index_480_);
lean_dec_ref_known(v___x_479_, 1);
v_size_481_ = lean_ctor_get(v_m_442_, 0);
v_keyArray_482_ = lean_ctor_get(v_m_442_, 1);
v___x_483_ = lean_unsigned_to_nat(1u);
v___x_484_ = lean_nat_add(v_size_481_, v___x_483_);
v___x_485_ = lean_array_get_size(v_keyArray_482_);
v___x_486_ = lean_nat_dec_lt(v___x_484_, v___x_485_);
if (v___x_486_ == 0)
{
lean_dec(v___x_484_);
lean_dec(v_index_480_);
goto v___jp_452_;
}
else
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_487_ = lean_unsigned_to_nat(4u);
v___x_488_ = lean_nat_mul(v___x_484_, v___x_487_);
v___x_489_ = lean_unsigned_to_nat(3u);
v___x_490_ = lean_nat_mul(v___x_485_, v___x_489_);
v___x_491_ = lean_nat_dec_le(v___x_488_, v___x_490_);
lean_dec(v___x_490_);
lean_dec(v___x_488_);
if (v___x_491_ == 0)
{
lean_dec(v___x_484_);
lean_dec(v_index_480_);
goto v___jp_452_;
}
else
{
lean_object* v___x_492_; 
lean_dec_ref(v_x_441_);
lean_dec_ref(v_x_440_);
v___x_492_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_442_, v___x_484_, v_index_480_, v_a_443_, v_b_444_);
lean_dec(v_index_480_);
return v___x_492_;
}
}
}
default: 
{
lean_object* v_size_493_; lean_object* v_keyArray_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; uint8_t v___x_498_; 
v_size_493_ = lean_ctor_get(v_m_442_, 0);
v_keyArray_494_ = lean_ctor_get(v_m_442_, 1);
v___x_495_ = lean_unsigned_to_nat(1u);
v___x_496_ = lean_nat_add(v_size_493_, v___x_495_);
v___x_497_ = lean_array_get_size(v_keyArray_494_);
v___x_498_ = lean_nat_dec_lt(v___x_496_, v___x_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; 
lean_dec(v___x_496_);
lean_inc_ref(v_x_441_);
lean_inc_ref(v_x_440_);
v___x_499_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_440_, v_x_441_, v_m_442_);
v___y_470_ = v___x_499_;
goto v___jp_469_;
}
else
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_500_ = lean_unsigned_to_nat(4u);
v___x_501_ = lean_nat_mul(v___x_496_, v___x_500_);
lean_dec(v___x_496_);
v___x_502_ = lean_unsigned_to_nat(3u);
v___x_503_ = lean_nat_mul(v___x_497_, v___x_502_);
v___x_504_ = lean_nat_dec_le(v___x_501_, v___x_503_);
lean_dec(v___x_503_);
lean_dec(v___x_501_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; 
lean_inc_ref(v_x_441_);
lean_inc_ref(v_x_440_);
v___x_505_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_440_, v_x_441_, v_m_442_);
v___y_470_ = v___x_505_;
goto v___jp_469_;
}
else
{
v___y_470_ = v_m_442_;
goto v___jp_469_;
}
}
}
}
v___jp_445_:
{
lean_object* v_size_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v_size_448_ = lean_ctor_get(v___y_446_, 0);
v___x_449_ = lean_unsigned_to_nat(1u);
v___x_450_ = lean_nat_add(v_size_448_, v___x_449_);
v___x_451_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_446_, v___x_450_, v_i_447_, v_a_443_, v_b_444_);
lean_dec(v_i_447_);
return v___x_451_;
}
v___jp_452_:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
lean_inc_ref(v_x_441_);
lean_inc_ref(v_x_440_);
v___x_453_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_440_, v_x_441_, v_m_442_);
lean_inc(v_a_443_);
v___x_454_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_440_, v_x_441_, v___x_453_, v_a_443_);
switch(lean_obj_tag(v___x_454_))
{
case 0:
{
lean_object* v_index_455_; lean_object* v_size_456_; lean_object* v___x_457_; 
v_index_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc(v_index_455_);
lean_dec_ref_known(v___x_454_, 3);
v_size_456_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_size_456_);
v___x_457_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_453_, v_size_456_, v_index_455_, v_a_443_, v_b_444_);
lean_dec(v_index_455_);
return v___x_457_;
}
case 1:
{
lean_object* v_index_458_; 
v_index_458_ = lean_ctor_get(v___x_454_, 0);
lean_inc(v_index_458_);
lean_dec_ref_known(v___x_454_, 1);
v___y_446_ = v___x_453_;
v_i_447_ = v_index_458_;
goto v___jp_445_;
}
default: 
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = lean_unsigned_to_nat(0u);
v___x_460_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_453_, v___x_459_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_index_461_; 
v_index_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_index_461_);
lean_dec_ref_known(v___x_460_, 1);
v___y_446_ = v___x_453_;
v_i_447_ = v_index_461_;
goto v___jp_445_;
}
else
{
lean_dec(v_b_444_);
lean_dec(v_a_443_);
return v___x_453_;
}
}
}
}
v___jp_462_:
{
lean_object* v_size_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_size_465_ = lean_ctor_get(v___y_463_, 0);
v___x_466_ = lean_unsigned_to_nat(1u);
v___x_467_ = lean_nat_add(v_size_465_, v___x_466_);
v___x_468_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_463_, v___x_467_, v_i_464_, v_a_443_, v_b_444_);
lean_dec(v_i_464_);
return v___x_468_;
}
v___jp_469_:
{
lean_object* v___x_471_; 
lean_inc(v_a_443_);
v___x_471_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_440_, v_x_441_, v___y_470_, v_a_443_);
switch(lean_obj_tag(v___x_471_))
{
case 0:
{
lean_object* v_index_472_; lean_object* v_size_473_; lean_object* v___x_474_; 
v_index_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_index_472_);
lean_dec_ref_known(v___x_471_, 3);
v_size_473_ = lean_ctor_get(v___y_470_, 0);
lean_inc(v_size_473_);
v___x_474_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_470_, v_size_473_, v_index_472_, v_a_443_, v_b_444_);
lean_dec(v_index_472_);
return v___x_474_;
}
case 1:
{
lean_object* v_index_475_; 
v_index_475_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_index_475_);
lean_dec_ref_known(v___x_471_, 1);
v___y_463_ = v___y_470_;
v_i_464_ = v_index_475_;
goto v___jp_462_;
}
default: 
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_470_, v___x_476_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_index_478_; 
v_index_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_index_478_);
lean_dec_ref_known(v___x_477_, 1);
v___y_463_ = v___y_470_;
v_i_464_ = v_index_478_;
goto v___jp_462_;
}
else
{
lean_dec(v_b_444_);
lean_dec(v_a_443_);
return v___y_470_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insertIfNew(lean_object* v_00_u03b1_506_, lean_object* v_00_u03b2_507_, lean_object* v_x_508_, lean_object* v_x_509_, lean_object* v_inst_510_, lean_object* v_inst_511_, lean_object* v_m_512_, lean_object* v_a_513_, lean_object* v_b_514_){
_start:
{
lean_object* v___y_516_; lean_object* v_i_517_; lean_object* v___y_533_; lean_object* v_i_534_; lean_object* v___y_540_; lean_object* v___x_549_; 
lean_inc(v_a_513_);
lean_inc_ref(v_x_509_);
lean_inc_ref(v_x_508_);
v___x_549_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_508_, v_x_509_, v_m_512_, v_a_513_);
switch(lean_obj_tag(v___x_549_))
{
case 0:
{
lean_dec_ref_known(v___x_549_, 3);
lean_dec(v_b_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_x_509_);
lean_dec_ref(v_x_508_);
return v_m_512_;
}
case 1:
{
lean_object* v_index_550_; lean_object* v_size_551_; lean_object* v_keyArray_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v_index_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_index_550_);
lean_dec_ref_known(v___x_549_, 1);
v_size_551_ = lean_ctor_get(v_m_512_, 0);
v_keyArray_552_ = lean_ctor_get(v_m_512_, 1);
v___x_553_ = lean_unsigned_to_nat(1u);
v___x_554_ = lean_nat_add(v_size_551_, v___x_553_);
v___x_555_ = lean_array_get_size(v_keyArray_552_);
v___x_556_ = lean_nat_dec_lt(v___x_554_, v___x_555_);
if (v___x_556_ == 0)
{
lean_dec(v___x_554_);
lean_dec(v_index_550_);
goto v___jp_522_;
}
else
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_557_ = lean_unsigned_to_nat(4u);
v___x_558_ = lean_nat_mul(v___x_554_, v___x_557_);
v___x_559_ = lean_unsigned_to_nat(3u);
v___x_560_ = lean_nat_mul(v___x_555_, v___x_559_);
v___x_561_ = lean_nat_dec_le(v___x_558_, v___x_560_);
lean_dec(v___x_560_);
lean_dec(v___x_558_);
if (v___x_561_ == 0)
{
lean_dec(v___x_554_);
lean_dec(v_index_550_);
goto v___jp_522_;
}
else
{
lean_object* v___x_562_; 
lean_dec_ref(v_x_509_);
lean_dec_ref(v_x_508_);
v___x_562_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_512_, v___x_554_, v_index_550_, v_a_513_, v_b_514_);
lean_dec(v_index_550_);
return v___x_562_;
}
}
}
default: 
{
lean_object* v_size_563_; lean_object* v_keyArray_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v_size_563_ = lean_ctor_get(v_m_512_, 0);
v_keyArray_564_ = lean_ctor_get(v_m_512_, 1);
v___x_565_ = lean_unsigned_to_nat(1u);
v___x_566_ = lean_nat_add(v_size_563_, v___x_565_);
v___x_567_ = lean_array_get_size(v_keyArray_564_);
v___x_568_ = lean_nat_dec_lt(v___x_566_, v___x_567_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; 
lean_dec(v___x_566_);
lean_inc_ref(v_x_509_);
lean_inc_ref(v_x_508_);
v___x_569_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_508_, v_x_509_, v_m_512_);
v___y_540_ = v___x_569_;
goto v___jp_539_;
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_570_ = lean_unsigned_to_nat(4u);
v___x_571_ = lean_nat_mul(v___x_566_, v___x_570_);
lean_dec(v___x_566_);
v___x_572_ = lean_unsigned_to_nat(3u);
v___x_573_ = lean_nat_mul(v___x_567_, v___x_572_);
v___x_574_ = lean_nat_dec_le(v___x_571_, v___x_573_);
lean_dec(v___x_573_);
lean_dec(v___x_571_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; 
lean_inc_ref(v_x_509_);
lean_inc_ref(v_x_508_);
v___x_575_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_508_, v_x_509_, v_m_512_);
v___y_540_ = v___x_575_;
goto v___jp_539_;
}
else
{
v___y_540_ = v_m_512_;
goto v___jp_539_;
}
}
}
}
v___jp_515_:
{
lean_object* v_size_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v_size_518_ = lean_ctor_get(v___y_516_, 0);
v___x_519_ = lean_unsigned_to_nat(1u);
v___x_520_ = lean_nat_add(v_size_518_, v___x_519_);
v___x_521_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_516_, v___x_520_, v_i_517_, v_a_513_, v_b_514_);
lean_dec(v_i_517_);
return v___x_521_;
}
v___jp_522_:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
lean_inc_ref(v_x_509_);
lean_inc_ref(v_x_508_);
v___x_523_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_508_, v_x_509_, v_m_512_);
lean_inc(v_a_513_);
v___x_524_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_508_, v_x_509_, v___x_523_, v_a_513_);
switch(lean_obj_tag(v___x_524_))
{
case 0:
{
lean_object* v_index_525_; lean_object* v_size_526_; lean_object* v___x_527_; 
v_index_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_index_525_);
lean_dec_ref_known(v___x_524_, 3);
v_size_526_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_size_526_);
v___x_527_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_523_, v_size_526_, v_index_525_, v_a_513_, v_b_514_);
lean_dec(v_index_525_);
return v___x_527_;
}
case 1:
{
lean_object* v_index_528_; 
v_index_528_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_index_528_);
lean_dec_ref_known(v___x_524_, 1);
v___y_516_ = v___x_523_;
v_i_517_ = v_index_528_;
goto v___jp_515_;
}
default: 
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_523_, v___x_529_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_index_531_; 
v_index_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_index_531_);
lean_dec_ref_known(v___x_530_, 1);
v___y_516_ = v___x_523_;
v_i_517_ = v_index_531_;
goto v___jp_515_;
}
else
{
lean_dec(v_b_514_);
lean_dec(v_a_513_);
return v___x_523_;
}
}
}
}
v___jp_532_:
{
lean_object* v_size_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v_size_535_ = lean_ctor_get(v___y_533_, 0);
v___x_536_ = lean_unsigned_to_nat(1u);
v___x_537_ = lean_nat_add(v_size_535_, v___x_536_);
v___x_538_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_533_, v___x_537_, v_i_534_, v_a_513_, v_b_514_);
lean_dec(v_i_534_);
return v___x_538_;
}
v___jp_539_:
{
lean_object* v___x_541_; 
lean_inc(v_a_513_);
v___x_541_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_508_, v_x_509_, v___y_540_, v_a_513_);
switch(lean_obj_tag(v___x_541_))
{
case 0:
{
lean_object* v_index_542_; lean_object* v_size_543_; lean_object* v___x_544_; 
v_index_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_index_542_);
lean_dec_ref_known(v___x_541_, 3);
v_size_543_ = lean_ctor_get(v___y_540_, 0);
lean_inc(v_size_543_);
v___x_544_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_540_, v_size_543_, v_index_542_, v_a_513_, v_b_514_);
lean_dec(v_index_542_);
return v___x_544_;
}
case 1:
{
lean_object* v_index_545_; 
v_index_545_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_index_545_);
lean_dec_ref_known(v___x_541_, 1);
v___y_533_ = v___y_540_;
v_i_534_ = v_index_545_;
goto v___jp_532_;
}
default: 
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_540_, v___x_546_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_index_548_; 
v_index_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_index_548_);
lean_dec_ref_known(v___x_547_, 1);
v___y_533_ = v___y_540_;
v_i_534_ = v_index_548_;
goto v___jp_532_;
}
else
{
lean_dec(v_b_514_);
lean_dec(v_a_513_);
return v___y_540_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_containsThenInsert___redArg(lean_object* v_x_576_, lean_object* v_x_577_, lean_object* v_m_578_, lean_object* v_a_579_, lean_object* v_b_580_){
_start:
{
lean_object* v___x_581_; 
lean_inc(v_a_579_);
lean_inc_ref(v_x_577_);
lean_inc_ref(v_x_576_);
v___x_581_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_576_, v_x_577_, v_m_578_, v_a_579_);
switch(lean_obj_tag(v___x_581_))
{
case 0:
{
lean_object* v_index_582_; lean_object* v_size_583_; uint8_t v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
lean_dec_ref(v_x_577_);
lean_dec_ref(v_x_576_);
v_index_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_index_582_);
lean_dec_ref_known(v___x_581_, 3);
v_size_583_ = lean_ctor_get(v_m_578_, 0);
lean_inc(v_size_583_);
v___x_584_ = 1;
v___x_585_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_578_, v_size_583_, v_index_582_, v_a_579_, v_b_580_);
lean_dec(v_index_582_);
v___x_586_ = lean_box(v___x_584_);
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v___x_585_);
return v___x_587_;
}
case 1:
{
lean_object* v_index_588_; lean_object* v_size_589_; lean_object* v_keyArray_590_; uint8_t v___x_591_; lean_object* v___y_593_; lean_object* v_i_594_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v_index_588_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_index_588_);
lean_dec_ref_known(v___x_581_, 1);
v_size_589_ = lean_ctor_get(v_m_578_, 0);
v_keyArray_590_ = lean_ctor_get(v_m_578_, 1);
v___x_591_ = 0;
v___x_615_ = lean_unsigned_to_nat(1u);
v___x_616_ = lean_nat_add(v_size_589_, v___x_615_);
v___x_617_ = lean_array_get_size(v_keyArray_590_);
v___x_618_ = lean_nat_dec_lt(v___x_616_, v___x_617_);
if (v___x_618_ == 0)
{
lean_dec(v___x_616_);
lean_dec(v_index_588_);
goto v___jp_601_;
}
else
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_619_ = lean_unsigned_to_nat(4u);
v___x_620_ = lean_nat_mul(v___x_616_, v___x_619_);
v___x_621_ = lean_unsigned_to_nat(3u);
v___x_622_ = lean_nat_mul(v___x_617_, v___x_621_);
v___x_623_ = lean_nat_dec_le(v___x_620_, v___x_622_);
lean_dec(v___x_622_);
lean_dec(v___x_620_);
if (v___x_623_ == 0)
{
lean_dec(v___x_616_);
lean_dec(v_index_588_);
goto v___jp_601_;
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
lean_dec_ref(v_x_577_);
lean_dec_ref(v_x_576_);
v___x_624_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_578_, v___x_616_, v_index_588_, v_a_579_, v_b_580_);
lean_dec(v_index_588_);
v___x_625_ = lean_box(v___x_591_);
v___x_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v___x_624_);
return v___x_626_;
}
}
v___jp_592_:
{
lean_object* v_size_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v_size_595_ = lean_ctor_get(v___y_593_, 0);
v___x_596_ = lean_unsigned_to_nat(1u);
v___x_597_ = lean_nat_add(v_size_595_, v___x_596_);
v___x_598_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_593_, v___x_597_, v_i_594_, v_a_579_, v_b_580_);
lean_dec(v_i_594_);
v___x_599_ = lean_box(v___x_591_);
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
lean_ctor_set(v___x_600_, 1, v___x_598_);
return v___x_600_;
}
v___jp_601_:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
lean_inc_ref(v_x_577_);
lean_inc_ref(v_x_576_);
v___x_602_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_576_, v_x_577_, v_m_578_);
lean_inc(v_a_579_);
v___x_603_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_576_, v_x_577_, v___x_602_, v_a_579_);
switch(lean_obj_tag(v___x_603_))
{
case 0:
{
lean_object* v_index_604_; lean_object* v_size_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v_index_604_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_index_604_);
lean_dec_ref_known(v___x_603_, 3);
v_size_605_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_size_605_);
v___x_606_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_602_, v_size_605_, v_index_604_, v_a_579_, v_b_580_);
lean_dec(v_index_604_);
v___x_607_ = lean_box(v___x_591_);
v___x_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
lean_ctor_set(v___x_608_, 1, v___x_606_);
return v___x_608_;
}
case 1:
{
lean_object* v_index_609_; 
v_index_609_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_index_609_);
lean_dec_ref_known(v___x_603_, 1);
v___y_593_ = v___x_602_;
v_i_594_ = v_index_609_;
goto v___jp_592_;
}
default: 
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_unsigned_to_nat(0u);
v___x_611_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_602_, v___x_610_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v_index_612_; 
v_index_612_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_index_612_);
lean_dec_ref_known(v___x_611_, 1);
v___y_593_ = v___x_602_;
v_i_594_ = v_index_612_;
goto v___jp_592_;
}
else
{
lean_object* v___x_613_; lean_object* v___x_614_; 
lean_dec(v_b_580_);
lean_dec(v_a_579_);
v___x_613_ = lean_box(v___x_591_);
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v___x_602_);
return v___x_614_;
}
}
}
}
}
default: 
{
lean_object* v_size_627_; lean_object* v_keyArray_628_; uint8_t v___x_629_; lean_object* v___y_631_; lean_object* v_i_632_; lean_object* v___y_640_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v_size_627_ = lean_ctor_get(v_m_578_, 0);
v_keyArray_628_ = lean_ctor_get(v_m_578_, 1);
v___x_629_ = 0;
v___x_653_ = lean_unsigned_to_nat(1u);
v___x_654_ = lean_nat_add(v_size_627_, v___x_653_);
v___x_655_ = lean_array_get_size(v_keyArray_628_);
v___x_656_ = lean_nat_dec_lt(v___x_654_, v___x_655_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; 
lean_dec(v___x_654_);
lean_inc_ref(v_x_577_);
lean_inc_ref(v_x_576_);
v___x_657_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_576_, v_x_577_, v_m_578_);
v___y_640_ = v___x_657_;
goto v___jp_639_;
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_658_ = lean_unsigned_to_nat(4u);
v___x_659_ = lean_nat_mul(v___x_654_, v___x_658_);
lean_dec(v___x_654_);
v___x_660_ = lean_unsigned_to_nat(3u);
v___x_661_ = lean_nat_mul(v___x_655_, v___x_660_);
v___x_662_ = lean_nat_dec_le(v___x_659_, v___x_661_);
lean_dec(v___x_661_);
lean_dec(v___x_659_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; 
lean_inc_ref(v_x_577_);
lean_inc_ref(v_x_576_);
v___x_663_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_576_, v_x_577_, v_m_578_);
v___y_640_ = v___x_663_;
goto v___jp_639_;
}
else
{
v___y_640_ = v_m_578_;
goto v___jp_639_;
}
}
v___jp_630_:
{
lean_object* v_size_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v_size_633_ = lean_ctor_get(v___y_631_, 0);
v___x_634_ = lean_unsigned_to_nat(1u);
v___x_635_ = lean_nat_add(v_size_633_, v___x_634_);
v___x_636_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_631_, v___x_635_, v_i_632_, v_a_579_, v_b_580_);
lean_dec(v_i_632_);
v___x_637_ = lean_box(v___x_629_);
v___x_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
lean_ctor_set(v___x_638_, 1, v___x_636_);
return v___x_638_;
}
v___jp_639_:
{
lean_object* v___x_641_; 
lean_inc(v_a_579_);
v___x_641_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_576_, v_x_577_, v___y_640_, v_a_579_);
switch(lean_obj_tag(v___x_641_))
{
case 0:
{
lean_object* v_index_642_; lean_object* v_size_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v_index_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_index_642_);
lean_dec_ref_known(v___x_641_, 3);
v_size_643_ = lean_ctor_get(v___y_640_, 0);
lean_inc(v_size_643_);
v___x_644_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_640_, v_size_643_, v_index_642_, v_a_579_, v_b_580_);
lean_dec(v_index_642_);
v___x_645_ = lean_box(v___x_629_);
v___x_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set(v___x_646_, 1, v___x_644_);
return v___x_646_;
}
case 1:
{
lean_object* v_index_647_; 
v_index_647_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_index_647_);
lean_dec_ref_known(v___x_641_, 1);
v___y_631_ = v___y_640_;
v_i_632_ = v_index_647_;
goto v___jp_630_;
}
default: 
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_unsigned_to_nat(0u);
v___x_649_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_640_, v___x_648_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_index_650_; 
v_index_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_index_650_);
lean_dec_ref_known(v___x_649_, 1);
v___y_631_ = v___y_640_;
v_i_632_ = v_index_650_;
goto v___jp_630_;
}
else
{
lean_object* v___x_651_; lean_object* v___x_652_; 
lean_dec(v_b_580_);
lean_dec(v_a_579_);
v___x_651_ = lean_box(v___x_629_);
v___x_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v___y_640_);
return v___x_652_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_containsThenInsert(lean_object* v_00_u03b1_664_, lean_object* v_00_u03b2_665_, lean_object* v_x_666_, lean_object* v_x_667_, lean_object* v_inst_668_, lean_object* v_inst_669_, lean_object* v_m_670_, lean_object* v_a_671_, lean_object* v_b_672_){
_start:
{
lean_object* v___x_673_; 
lean_inc(v_a_671_);
lean_inc_ref(v_x_667_);
lean_inc_ref(v_x_666_);
v___x_673_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_666_, v_x_667_, v_m_670_, v_a_671_);
switch(lean_obj_tag(v___x_673_))
{
case 0:
{
lean_object* v_index_674_; lean_object* v_size_675_; uint8_t v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
lean_dec_ref(v_x_667_);
lean_dec_ref(v_x_666_);
v_index_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_index_674_);
lean_dec_ref_known(v___x_673_, 3);
v_size_675_ = lean_ctor_get(v_m_670_, 0);
lean_inc(v_size_675_);
v___x_676_ = 1;
v___x_677_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_670_, v_size_675_, v_index_674_, v_a_671_, v_b_672_);
lean_dec(v_index_674_);
v___x_678_ = lean_box(v___x_676_);
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
lean_ctor_set(v___x_679_, 1, v___x_677_);
return v___x_679_;
}
case 1:
{
lean_object* v_index_680_; lean_object* v_size_681_; lean_object* v_keyArray_682_; uint8_t v___x_683_; lean_object* v___y_685_; lean_object* v_i_686_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
v_index_680_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_index_680_);
lean_dec_ref_known(v___x_673_, 1);
v_size_681_ = lean_ctor_get(v_m_670_, 0);
v_keyArray_682_ = lean_ctor_get(v_m_670_, 1);
v___x_683_ = 0;
v___x_707_ = lean_unsigned_to_nat(1u);
v___x_708_ = lean_nat_add(v_size_681_, v___x_707_);
v___x_709_ = lean_array_get_size(v_keyArray_682_);
v___x_710_ = lean_nat_dec_lt(v___x_708_, v___x_709_);
if (v___x_710_ == 0)
{
lean_dec(v___x_708_);
lean_dec(v_index_680_);
goto v___jp_693_;
}
else
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_711_ = lean_unsigned_to_nat(4u);
v___x_712_ = lean_nat_mul(v___x_708_, v___x_711_);
v___x_713_ = lean_unsigned_to_nat(3u);
v___x_714_ = lean_nat_mul(v___x_709_, v___x_713_);
v___x_715_ = lean_nat_dec_le(v___x_712_, v___x_714_);
lean_dec(v___x_714_);
lean_dec(v___x_712_);
if (v___x_715_ == 0)
{
lean_dec(v___x_708_);
lean_dec(v_index_680_);
goto v___jp_693_;
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
lean_dec_ref(v_x_667_);
lean_dec_ref(v_x_666_);
v___x_716_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_670_, v___x_708_, v_index_680_, v_a_671_, v_b_672_);
lean_dec(v_index_680_);
v___x_717_ = lean_box(v___x_683_);
v___x_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
lean_ctor_set(v___x_718_, 1, v___x_716_);
return v___x_718_;
}
}
v___jp_684_:
{
lean_object* v_size_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v_size_687_ = lean_ctor_get(v___y_685_, 0);
v___x_688_ = lean_unsigned_to_nat(1u);
v___x_689_ = lean_nat_add(v_size_687_, v___x_688_);
v___x_690_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_685_, v___x_689_, v_i_686_, v_a_671_, v_b_672_);
lean_dec(v_i_686_);
v___x_691_ = lean_box(v___x_683_);
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v___x_690_);
return v___x_692_;
}
v___jp_693_:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
lean_inc_ref(v_x_667_);
lean_inc_ref(v_x_666_);
v___x_694_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_666_, v_x_667_, v_m_670_);
lean_inc(v_a_671_);
v___x_695_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_666_, v_x_667_, v___x_694_, v_a_671_);
switch(lean_obj_tag(v___x_695_))
{
case 0:
{
lean_object* v_index_696_; lean_object* v_size_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v_index_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_index_696_);
lean_dec_ref_known(v___x_695_, 3);
v_size_697_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_size_697_);
v___x_698_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_694_, v_size_697_, v_index_696_, v_a_671_, v_b_672_);
lean_dec(v_index_696_);
v___x_699_ = lean_box(v___x_683_);
v___x_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v___x_698_);
return v___x_700_;
}
case 1:
{
lean_object* v_index_701_; 
v_index_701_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_index_701_);
lean_dec_ref_known(v___x_695_, 1);
v___y_685_ = v___x_694_;
v_i_686_ = v_index_701_;
goto v___jp_684_;
}
default: 
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = lean_unsigned_to_nat(0u);
v___x_703_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_694_, v___x_702_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_index_704_; 
v_index_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_index_704_);
lean_dec_ref_known(v___x_703_, 1);
v___y_685_ = v___x_694_;
v_i_686_ = v_index_704_;
goto v___jp_684_;
}
else
{
lean_object* v___x_705_; lean_object* v___x_706_; 
lean_dec(v_b_672_);
lean_dec(v_a_671_);
v___x_705_ = lean_box(v___x_683_);
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
lean_ctor_set(v___x_706_, 1, v___x_694_);
return v___x_706_;
}
}
}
}
}
default: 
{
lean_object* v_size_719_; lean_object* v_keyArray_720_; uint8_t v___x_721_; lean_object* v___y_723_; lean_object* v_i_724_; lean_object* v___y_732_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; uint8_t v___x_748_; 
v_size_719_ = lean_ctor_get(v_m_670_, 0);
v_keyArray_720_ = lean_ctor_get(v_m_670_, 1);
v___x_721_ = 0;
v___x_745_ = lean_unsigned_to_nat(1u);
v___x_746_ = lean_nat_add(v_size_719_, v___x_745_);
v___x_747_ = lean_array_get_size(v_keyArray_720_);
v___x_748_ = lean_nat_dec_lt(v___x_746_, v___x_747_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; 
lean_dec(v___x_746_);
lean_inc_ref(v_x_667_);
lean_inc_ref(v_x_666_);
v___x_749_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_666_, v_x_667_, v_m_670_);
v___y_732_ = v___x_749_;
goto v___jp_731_;
}
else
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; uint8_t v___x_754_; 
v___x_750_ = lean_unsigned_to_nat(4u);
v___x_751_ = lean_nat_mul(v___x_746_, v___x_750_);
lean_dec(v___x_746_);
v___x_752_ = lean_unsigned_to_nat(3u);
v___x_753_ = lean_nat_mul(v___x_747_, v___x_752_);
v___x_754_ = lean_nat_dec_le(v___x_751_, v___x_753_);
lean_dec(v___x_753_);
lean_dec(v___x_751_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; 
lean_inc_ref(v_x_667_);
lean_inc_ref(v_x_666_);
v___x_755_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_666_, v_x_667_, v_m_670_);
v___y_732_ = v___x_755_;
goto v___jp_731_;
}
else
{
v___y_732_ = v_m_670_;
goto v___jp_731_;
}
}
v___jp_722_:
{
lean_object* v_size_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v_size_725_ = lean_ctor_get(v___y_723_, 0);
v___x_726_ = lean_unsigned_to_nat(1u);
v___x_727_ = lean_nat_add(v_size_725_, v___x_726_);
v___x_728_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_723_, v___x_727_, v_i_724_, v_a_671_, v_b_672_);
lean_dec(v_i_724_);
v___x_729_ = lean_box(v___x_721_);
v___x_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
lean_ctor_set(v___x_730_, 1, v___x_728_);
return v___x_730_;
}
v___jp_731_:
{
lean_object* v___x_733_; 
lean_inc(v_a_671_);
v___x_733_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_666_, v_x_667_, v___y_732_, v_a_671_);
switch(lean_obj_tag(v___x_733_))
{
case 0:
{
lean_object* v_index_734_; lean_object* v_size_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v_index_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_index_734_);
lean_dec_ref_known(v___x_733_, 3);
v_size_735_ = lean_ctor_get(v___y_732_, 0);
lean_inc(v_size_735_);
v___x_736_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_732_, v_size_735_, v_index_734_, v_a_671_, v_b_672_);
lean_dec(v_index_734_);
v___x_737_ = lean_box(v___x_721_);
v___x_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
lean_ctor_set(v___x_738_, 1, v___x_736_);
return v___x_738_;
}
case 1:
{
lean_object* v_index_739_; 
v_index_739_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_index_739_);
lean_dec_ref_known(v___x_733_, 1);
v___y_723_ = v___y_732_;
v_i_724_ = v_index_739_;
goto v___jp_722_;
}
default: 
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = lean_unsigned_to_nat(0u);
v___x_741_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_732_, v___x_740_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_index_742_; 
v_index_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_index_742_);
lean_dec_ref_known(v___x_741_, 1);
v___y_723_ = v___y_732_;
v_i_724_ = v_index_742_;
goto v___jp_722_;
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; 
lean_dec(v_b_672_);
lean_dec(v_a_671_);
v___x_743_ = lean_box(v___x_721_);
v___x_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
lean_ctor_set(v___x_744_, 1, v___y_732_);
return v___x_744_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_containsThenInsertIfNew___redArg(lean_object* v_x_756_, lean_object* v_x_757_, lean_object* v_m_758_, lean_object* v_a_759_, lean_object* v_b_760_){
_start:
{
lean_object* v___x_761_; 
lean_inc(v_a_759_);
lean_inc_ref(v_x_757_);
lean_inc_ref(v_x_756_);
v___x_761_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_756_, v_x_757_, v_m_758_, v_a_759_);
switch(lean_obj_tag(v___x_761_))
{
case 0:
{
uint8_t v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
lean_dec_ref_known(v___x_761_, 3);
lean_dec(v_b_760_);
lean_dec(v_a_759_);
lean_dec_ref(v_x_757_);
lean_dec_ref(v_x_756_);
v___x_762_ = 1;
v___x_763_ = lean_box(v___x_762_);
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
lean_ctor_set(v___x_764_, 1, v_m_758_);
return v___x_764_;
}
case 1:
{
lean_object* v_index_765_; lean_object* v_size_766_; lean_object* v_keyArray_767_; uint8_t v___x_768_; lean_object* v___y_770_; lean_object* v_i_771_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v_index_765_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_index_765_);
lean_dec_ref_known(v___x_761_, 1);
v_size_766_ = lean_ctor_get(v_m_758_, 0);
v_keyArray_767_ = lean_ctor_get(v_m_758_, 1);
v___x_768_ = 0;
v___x_792_ = lean_unsigned_to_nat(1u);
v___x_793_ = lean_nat_add(v_size_766_, v___x_792_);
v___x_794_ = lean_array_get_size(v_keyArray_767_);
v___x_795_ = lean_nat_dec_lt(v___x_793_, v___x_794_);
if (v___x_795_ == 0)
{
lean_dec(v___x_793_);
lean_dec(v_index_765_);
goto v___jp_778_;
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v___x_796_ = lean_unsigned_to_nat(4u);
v___x_797_ = lean_nat_mul(v___x_793_, v___x_796_);
v___x_798_ = lean_unsigned_to_nat(3u);
v___x_799_ = lean_nat_mul(v___x_794_, v___x_798_);
v___x_800_ = lean_nat_dec_le(v___x_797_, v___x_799_);
lean_dec(v___x_799_);
lean_dec(v___x_797_);
if (v___x_800_ == 0)
{
lean_dec(v___x_793_);
lean_dec(v_index_765_);
goto v___jp_778_;
}
else
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
lean_dec_ref(v_x_757_);
lean_dec_ref(v_x_756_);
v___x_801_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_758_, v___x_793_, v_index_765_, v_a_759_, v_b_760_);
lean_dec(v_index_765_);
v___x_802_ = lean_box(v___x_768_);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
lean_ctor_set(v___x_803_, 1, v___x_801_);
return v___x_803_;
}
}
v___jp_769_:
{
lean_object* v_size_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v_size_772_ = lean_ctor_get(v___y_770_, 0);
v___x_773_ = lean_unsigned_to_nat(1u);
v___x_774_ = lean_nat_add(v_size_772_, v___x_773_);
v___x_775_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_770_, v___x_774_, v_i_771_, v_a_759_, v_b_760_);
lean_dec(v_i_771_);
v___x_776_ = lean_box(v___x_768_);
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
lean_ctor_set(v___x_777_, 1, v___x_775_);
return v___x_777_;
}
v___jp_778_:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
lean_inc_ref(v_x_757_);
lean_inc_ref(v_x_756_);
v___x_779_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_756_, v_x_757_, v_m_758_);
lean_inc(v_a_759_);
v___x_780_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_756_, v_x_757_, v___x_779_, v_a_759_);
switch(lean_obj_tag(v___x_780_))
{
case 0:
{
lean_object* v_index_781_; lean_object* v_size_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v_index_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_index_781_);
lean_dec_ref_known(v___x_780_, 3);
v_size_782_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_size_782_);
v___x_783_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_779_, v_size_782_, v_index_781_, v_a_759_, v_b_760_);
lean_dec(v_index_781_);
v___x_784_ = lean_box(v___x_768_);
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
lean_ctor_set(v___x_785_, 1, v___x_783_);
return v___x_785_;
}
case 1:
{
lean_object* v_index_786_; 
v_index_786_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_index_786_);
lean_dec_ref_known(v___x_780_, 1);
v___y_770_ = v___x_779_;
v_i_771_ = v_index_786_;
goto v___jp_769_;
}
default: 
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = lean_unsigned_to_nat(0u);
v___x_788_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_779_, v___x_787_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_index_789_; 
v_index_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_index_789_);
lean_dec_ref_known(v___x_788_, 1);
v___y_770_ = v___x_779_;
v_i_771_ = v_index_789_;
goto v___jp_769_;
}
else
{
lean_object* v___x_790_; lean_object* v___x_791_; 
lean_dec(v_b_760_);
lean_dec(v_a_759_);
v___x_790_ = lean_box(v___x_768_);
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
lean_ctor_set(v___x_791_, 1, v___x_779_);
return v___x_791_;
}
}
}
}
}
default: 
{
lean_object* v_size_804_; lean_object* v_keyArray_805_; uint8_t v___x_806_; lean_object* v___y_808_; lean_object* v_i_809_; lean_object* v___y_817_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v_size_804_ = lean_ctor_get(v_m_758_, 0);
v_keyArray_805_ = lean_ctor_get(v_m_758_, 1);
v___x_806_ = 0;
v___x_830_ = lean_unsigned_to_nat(1u);
v___x_831_ = lean_nat_add(v_size_804_, v___x_830_);
v___x_832_ = lean_array_get_size(v_keyArray_805_);
v___x_833_ = lean_nat_dec_lt(v___x_831_, v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; 
lean_dec(v___x_831_);
lean_inc_ref(v_x_757_);
lean_inc_ref(v_x_756_);
v___x_834_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_756_, v_x_757_, v_m_758_);
v___y_817_ = v___x_834_;
goto v___jp_816_;
}
else
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_835_ = lean_unsigned_to_nat(4u);
v___x_836_ = lean_nat_mul(v___x_831_, v___x_835_);
lean_dec(v___x_831_);
v___x_837_ = lean_unsigned_to_nat(3u);
v___x_838_ = lean_nat_mul(v___x_832_, v___x_837_);
v___x_839_ = lean_nat_dec_le(v___x_836_, v___x_838_);
lean_dec(v___x_838_);
lean_dec(v___x_836_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; 
lean_inc_ref(v_x_757_);
lean_inc_ref(v_x_756_);
v___x_840_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_756_, v_x_757_, v_m_758_);
v___y_817_ = v___x_840_;
goto v___jp_816_;
}
else
{
v___y_817_ = v_m_758_;
goto v___jp_816_;
}
}
v___jp_807_:
{
lean_object* v_size_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v_size_810_ = lean_ctor_get(v___y_808_, 0);
v___x_811_ = lean_unsigned_to_nat(1u);
v___x_812_ = lean_nat_add(v_size_810_, v___x_811_);
v___x_813_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_808_, v___x_812_, v_i_809_, v_a_759_, v_b_760_);
lean_dec(v_i_809_);
v___x_814_ = lean_box(v___x_806_);
v___x_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
lean_ctor_set(v___x_815_, 1, v___x_813_);
return v___x_815_;
}
v___jp_816_:
{
lean_object* v___x_818_; 
lean_inc(v_a_759_);
v___x_818_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_756_, v_x_757_, v___y_817_, v_a_759_);
switch(lean_obj_tag(v___x_818_))
{
case 0:
{
lean_object* v_index_819_; lean_object* v_size_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v_index_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_index_819_);
lean_dec_ref_known(v___x_818_, 3);
v_size_820_ = lean_ctor_get(v___y_817_, 0);
lean_inc(v_size_820_);
v___x_821_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_817_, v_size_820_, v_index_819_, v_a_759_, v_b_760_);
lean_dec(v_index_819_);
v___x_822_ = lean_box(v___x_806_);
v___x_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
lean_ctor_set(v___x_823_, 1, v___x_821_);
return v___x_823_;
}
case 1:
{
lean_object* v_index_824_; 
v_index_824_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_index_824_);
lean_dec_ref_known(v___x_818_, 1);
v___y_808_ = v___y_817_;
v_i_809_ = v_index_824_;
goto v___jp_807_;
}
default: 
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = lean_unsigned_to_nat(0u);
v___x_826_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_817_, v___x_825_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_index_827_; 
v_index_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_index_827_);
lean_dec_ref_known(v___x_826_, 1);
v___y_808_ = v___y_817_;
v_i_809_ = v_index_827_;
goto v___jp_807_;
}
else
{
lean_object* v___x_828_; lean_object* v___x_829_; 
lean_dec(v_b_760_);
lean_dec(v_a_759_);
v___x_828_ = lean_box(v___x_806_);
v___x_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
lean_ctor_set(v___x_829_, 1, v___y_817_);
return v___x_829_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_containsThenInsertIfNew(lean_object* v_00_u03b1_841_, lean_object* v_00_u03b2_842_, lean_object* v_x_843_, lean_object* v_x_844_, lean_object* v_inst_845_, lean_object* v_inst_846_, lean_object* v_m_847_, lean_object* v_a_848_, lean_object* v_b_849_){
_start:
{
lean_object* v___x_850_; 
lean_inc(v_a_848_);
lean_inc_ref(v_x_844_);
lean_inc_ref(v_x_843_);
v___x_850_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_843_, v_x_844_, v_m_847_, v_a_848_);
switch(lean_obj_tag(v___x_850_))
{
case 0:
{
uint8_t v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
lean_dec_ref_known(v___x_850_, 3);
lean_dec(v_b_849_);
lean_dec(v_a_848_);
lean_dec_ref(v_x_844_);
lean_dec_ref(v_x_843_);
v___x_851_ = 1;
v___x_852_ = lean_box(v___x_851_);
v___x_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
lean_ctor_set(v___x_853_, 1, v_m_847_);
return v___x_853_;
}
case 1:
{
lean_object* v_index_854_; lean_object* v_size_855_; lean_object* v_keyArray_856_; uint8_t v___x_857_; lean_object* v___y_859_; lean_object* v_i_860_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; uint8_t v___x_884_; 
v_index_854_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_index_854_);
lean_dec_ref_known(v___x_850_, 1);
v_size_855_ = lean_ctor_get(v_m_847_, 0);
v_keyArray_856_ = lean_ctor_get(v_m_847_, 1);
v___x_857_ = 0;
v___x_881_ = lean_unsigned_to_nat(1u);
v___x_882_ = lean_nat_add(v_size_855_, v___x_881_);
v___x_883_ = lean_array_get_size(v_keyArray_856_);
v___x_884_ = lean_nat_dec_lt(v___x_882_, v___x_883_);
if (v___x_884_ == 0)
{
lean_dec(v___x_882_);
lean_dec(v_index_854_);
goto v___jp_867_;
}
else
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_885_ = lean_unsigned_to_nat(4u);
v___x_886_ = lean_nat_mul(v___x_882_, v___x_885_);
v___x_887_ = lean_unsigned_to_nat(3u);
v___x_888_ = lean_nat_mul(v___x_883_, v___x_887_);
v___x_889_ = lean_nat_dec_le(v___x_886_, v___x_888_);
lean_dec(v___x_888_);
lean_dec(v___x_886_);
if (v___x_889_ == 0)
{
lean_dec(v___x_882_);
lean_dec(v_index_854_);
goto v___jp_867_;
}
else
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
lean_dec_ref(v_x_844_);
lean_dec_ref(v_x_843_);
v___x_890_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_847_, v___x_882_, v_index_854_, v_a_848_, v_b_849_);
lean_dec(v_index_854_);
v___x_891_ = lean_box(v___x_857_);
v___x_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
lean_ctor_set(v___x_892_, 1, v___x_890_);
return v___x_892_;
}
}
v___jp_858_:
{
lean_object* v_size_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v_size_861_ = lean_ctor_get(v___y_859_, 0);
v___x_862_ = lean_unsigned_to_nat(1u);
v___x_863_ = lean_nat_add(v_size_861_, v___x_862_);
v___x_864_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_859_, v___x_863_, v_i_860_, v_a_848_, v_b_849_);
lean_dec(v_i_860_);
v___x_865_ = lean_box(v___x_857_);
v___x_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
lean_ctor_set(v___x_866_, 1, v___x_864_);
return v___x_866_;
}
v___jp_867_:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
lean_inc_ref(v_x_844_);
lean_inc_ref(v_x_843_);
v___x_868_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_843_, v_x_844_, v_m_847_);
lean_inc(v_a_848_);
v___x_869_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_843_, v_x_844_, v___x_868_, v_a_848_);
switch(lean_obj_tag(v___x_869_))
{
case 0:
{
lean_object* v_index_870_; lean_object* v_size_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v_index_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_index_870_);
lean_dec_ref_known(v___x_869_, 3);
v_size_871_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_size_871_);
v___x_872_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_868_, v_size_871_, v_index_870_, v_a_848_, v_b_849_);
lean_dec(v_index_870_);
v___x_873_ = lean_box(v___x_857_);
v___x_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
lean_ctor_set(v___x_874_, 1, v___x_872_);
return v___x_874_;
}
case 1:
{
lean_object* v_index_875_; 
v_index_875_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_index_875_);
lean_dec_ref_known(v___x_869_, 1);
v___y_859_ = v___x_868_;
v_i_860_ = v_index_875_;
goto v___jp_858_;
}
default: 
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = lean_unsigned_to_nat(0u);
v___x_877_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_868_, v___x_876_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_index_878_; 
v_index_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_index_878_);
lean_dec_ref_known(v___x_877_, 1);
v___y_859_ = v___x_868_;
v_i_860_ = v_index_878_;
goto v___jp_858_;
}
else
{
lean_object* v___x_879_; lean_object* v___x_880_; 
lean_dec(v_b_849_);
lean_dec(v_a_848_);
v___x_879_ = lean_box(v___x_857_);
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
lean_ctor_set(v___x_880_, 1, v___x_868_);
return v___x_880_;
}
}
}
}
}
default: 
{
lean_object* v_size_893_; lean_object* v_keyArray_894_; uint8_t v___x_895_; lean_object* v___y_897_; lean_object* v_i_898_; lean_object* v___y_906_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
v_size_893_ = lean_ctor_get(v_m_847_, 0);
v_keyArray_894_ = lean_ctor_get(v_m_847_, 1);
v___x_895_ = 0;
v___x_919_ = lean_unsigned_to_nat(1u);
v___x_920_ = lean_nat_add(v_size_893_, v___x_919_);
v___x_921_ = lean_array_get_size(v_keyArray_894_);
v___x_922_ = lean_nat_dec_lt(v___x_920_, v___x_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; 
lean_dec(v___x_920_);
lean_inc_ref(v_x_844_);
lean_inc_ref(v_x_843_);
v___x_923_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_843_, v_x_844_, v_m_847_);
v___y_906_ = v___x_923_;
goto v___jp_905_;
}
else
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_924_ = lean_unsigned_to_nat(4u);
v___x_925_ = lean_nat_mul(v___x_920_, v___x_924_);
lean_dec(v___x_920_);
v___x_926_ = lean_unsigned_to_nat(3u);
v___x_927_ = lean_nat_mul(v___x_921_, v___x_926_);
v___x_928_ = lean_nat_dec_le(v___x_925_, v___x_927_);
lean_dec(v___x_927_);
lean_dec(v___x_925_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; 
lean_inc_ref(v_x_844_);
lean_inc_ref(v_x_843_);
v___x_929_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_843_, v_x_844_, v_m_847_);
v___y_906_ = v___x_929_;
goto v___jp_905_;
}
else
{
v___y_906_ = v_m_847_;
goto v___jp_905_;
}
}
v___jp_896_:
{
lean_object* v_size_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v_size_899_ = lean_ctor_get(v___y_897_, 0);
v___x_900_ = lean_unsigned_to_nat(1u);
v___x_901_ = lean_nat_add(v_size_899_, v___x_900_);
v___x_902_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_897_, v___x_901_, v_i_898_, v_a_848_, v_b_849_);
lean_dec(v_i_898_);
v___x_903_ = lean_box(v___x_895_);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v___x_902_);
return v___x_904_;
}
v___jp_905_:
{
lean_object* v___x_907_; 
lean_inc(v_a_848_);
v___x_907_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_843_, v_x_844_, v___y_906_, v_a_848_);
switch(lean_obj_tag(v___x_907_))
{
case 0:
{
lean_object* v_index_908_; lean_object* v_size_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v_index_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_index_908_);
lean_dec_ref_known(v___x_907_, 3);
v_size_909_ = lean_ctor_get(v___y_906_, 0);
lean_inc(v_size_909_);
v___x_910_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_906_, v_size_909_, v_index_908_, v_a_848_, v_b_849_);
lean_dec(v_index_908_);
v___x_911_ = lean_box(v___x_895_);
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set(v___x_912_, 1, v___x_910_);
return v___x_912_;
}
case 1:
{
lean_object* v_index_913_; 
v_index_913_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_index_913_);
lean_dec_ref_known(v___x_907_, 1);
v___y_897_ = v___y_906_;
v_i_898_ = v_index_913_;
goto v___jp_896_;
}
default: 
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = lean_unsigned_to_nat(0u);
v___x_915_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_906_, v___x_914_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_index_916_; 
v_index_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_index_916_);
lean_dec_ref_known(v___x_915_, 1);
v___y_897_ = v___y_906_;
v_i_898_ = v_index_916_;
goto v___jp_896_;
}
else
{
lean_object* v___x_917_; lean_object* v___x_918_; 
lean_dec(v_b_849_);
lean_dec(v_a_848_);
v___x_917_ = lean_box(v___x_895_);
v___x_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
lean_ctor_set(v___x_918_, 1, v___y_906_);
return v___x_918_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getThenInsertIfNew_x3f___redArg(lean_object* v_x_930_, lean_object* v_x_931_, lean_object* v_m_932_, lean_object* v_a_933_, lean_object* v_b_934_){
_start:
{
lean_object* v___x_935_; 
lean_inc(v_a_933_);
lean_inc_ref(v_x_931_);
lean_inc_ref(v_x_930_);
v___x_935_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_930_, v_x_931_, v_m_932_, v_a_933_);
switch(lean_obj_tag(v___x_935_))
{
case 0:
{
lean_object* v_value_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
lean_dec(v_b_934_);
lean_dec(v_a_933_);
lean_dec_ref(v_x_931_);
lean_dec_ref(v_x_930_);
v_value_936_ = lean_ctor_get(v___x_935_, 2);
lean_inc(v_value_936_);
lean_dec_ref_known(v___x_935_, 3);
v___x_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_937_, 0, v_value_936_);
v___x_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set(v___x_938_, 1, v_m_932_);
return v___x_938_;
}
case 1:
{
lean_object* v_index_939_; lean_object* v_size_940_; lean_object* v_keyArray_941_; lean_object* v___x_942_; lean_object* v___y_944_; lean_object* v_i_945_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; uint8_t v___x_966_; 
v_index_939_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_index_939_);
lean_dec_ref_known(v___x_935_, 1);
v_size_940_ = lean_ctor_get(v_m_932_, 0);
v_keyArray_941_ = lean_ctor_get(v_m_932_, 1);
v___x_942_ = lean_box(0);
v___x_963_ = lean_unsigned_to_nat(1u);
v___x_964_ = lean_nat_add(v_size_940_, v___x_963_);
v___x_965_ = lean_array_get_size(v_keyArray_941_);
v___x_966_ = lean_nat_dec_lt(v___x_964_, v___x_965_);
if (v___x_966_ == 0)
{
lean_dec(v___x_964_);
lean_dec(v_index_939_);
goto v___jp_951_;
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; uint8_t v___x_971_; 
v___x_967_ = lean_unsigned_to_nat(4u);
v___x_968_ = lean_nat_mul(v___x_964_, v___x_967_);
v___x_969_ = lean_unsigned_to_nat(3u);
v___x_970_ = lean_nat_mul(v___x_965_, v___x_969_);
v___x_971_ = lean_nat_dec_le(v___x_968_, v___x_970_);
lean_dec(v___x_970_);
lean_dec(v___x_968_);
if (v___x_971_ == 0)
{
lean_dec(v___x_964_);
lean_dec(v_index_939_);
goto v___jp_951_;
}
else
{
lean_object* v___x_972_; lean_object* v___x_973_; 
lean_dec_ref(v_x_931_);
lean_dec_ref(v_x_930_);
v___x_972_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_932_, v___x_964_, v_index_939_, v_a_933_, v_b_934_);
lean_dec(v_index_939_);
v___x_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_942_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
return v___x_973_;
}
}
v___jp_943_:
{
lean_object* v_size_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v_size_946_ = lean_ctor_get(v___y_944_, 0);
v___x_947_ = lean_unsigned_to_nat(1u);
v___x_948_ = lean_nat_add(v_size_946_, v___x_947_);
v___x_949_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_944_, v___x_948_, v_i_945_, v_a_933_, v_b_934_);
lean_dec(v_i_945_);
v___x_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_942_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
return v___x_950_;
}
v___jp_951_:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
lean_inc_ref(v_x_931_);
lean_inc_ref(v_x_930_);
v___x_952_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_930_, v_x_931_, v_m_932_);
lean_inc(v_a_933_);
v___x_953_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_930_, v_x_931_, v___x_952_, v_a_933_);
switch(lean_obj_tag(v___x_953_))
{
case 0:
{
lean_object* v_index_954_; lean_object* v_size_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v_index_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_index_954_);
lean_dec_ref_known(v___x_953_, 3);
v_size_955_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_size_955_);
v___x_956_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_952_, v_size_955_, v_index_954_, v_a_933_, v_b_934_);
lean_dec(v_index_954_);
v___x_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_942_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
return v___x_957_;
}
case 1:
{
lean_object* v_index_958_; 
v_index_958_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_index_958_);
lean_dec_ref_known(v___x_953_, 1);
v___y_944_ = v___x_952_;
v_i_945_ = v_index_958_;
goto v___jp_943_;
}
default: 
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = lean_unsigned_to_nat(0u);
v___x_960_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_952_, v___x_959_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_index_961_; 
v_index_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_index_961_);
lean_dec_ref_known(v___x_960_, 1);
v___y_944_ = v___x_952_;
v_i_945_ = v_index_961_;
goto v___jp_943_;
}
else
{
lean_object* v___x_962_; 
lean_dec(v_b_934_);
lean_dec(v_a_933_);
v___x_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_942_);
lean_ctor_set(v___x_962_, 1, v___x_952_);
return v___x_962_;
}
}
}
}
}
default: 
{
lean_object* v_size_974_; lean_object* v_keyArray_975_; lean_object* v___x_976_; lean_object* v___y_978_; lean_object* v_i_979_; lean_object* v___y_986_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; uint8_t v___x_1000_; 
v_size_974_ = lean_ctor_get(v_m_932_, 0);
v_keyArray_975_ = lean_ctor_get(v_m_932_, 1);
v___x_976_ = lean_box(0);
v___x_997_ = lean_unsigned_to_nat(1u);
v___x_998_ = lean_nat_add(v_size_974_, v___x_997_);
v___x_999_ = lean_array_get_size(v_keyArray_975_);
v___x_1000_ = lean_nat_dec_lt(v___x_998_, v___x_999_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; 
lean_dec(v___x_998_);
lean_inc_ref(v_x_931_);
lean_inc_ref(v_x_930_);
v___x_1001_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_930_, v_x_931_, v_m_932_);
v___y_986_ = v___x_1001_;
goto v___jp_985_;
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1002_ = lean_unsigned_to_nat(4u);
v___x_1003_ = lean_nat_mul(v___x_998_, v___x_1002_);
lean_dec(v___x_998_);
v___x_1004_ = lean_unsigned_to_nat(3u);
v___x_1005_ = lean_nat_mul(v___x_999_, v___x_1004_);
v___x_1006_ = lean_nat_dec_le(v___x_1003_, v___x_1005_);
lean_dec(v___x_1005_);
lean_dec(v___x_1003_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; 
lean_inc_ref(v_x_931_);
lean_inc_ref(v_x_930_);
v___x_1007_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_930_, v_x_931_, v_m_932_);
v___y_986_ = v___x_1007_;
goto v___jp_985_;
}
else
{
v___y_986_ = v_m_932_;
goto v___jp_985_;
}
}
v___jp_977_:
{
lean_object* v_size_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v_size_980_ = lean_ctor_get(v___y_978_, 0);
v___x_981_ = lean_unsigned_to_nat(1u);
v___x_982_ = lean_nat_add(v_size_980_, v___x_981_);
v___x_983_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_978_, v___x_982_, v_i_979_, v_a_933_, v_b_934_);
lean_dec(v_i_979_);
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_976_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
return v___x_984_;
}
v___jp_985_:
{
lean_object* v___x_987_; 
lean_inc(v_a_933_);
v___x_987_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_930_, v_x_931_, v___y_986_, v_a_933_);
switch(lean_obj_tag(v___x_987_))
{
case 0:
{
lean_object* v_index_988_; lean_object* v_size_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v_index_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_index_988_);
lean_dec_ref_known(v___x_987_, 3);
v_size_989_ = lean_ctor_get(v___y_986_, 0);
lean_inc(v_size_989_);
v___x_990_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_986_, v_size_989_, v_index_988_, v_a_933_, v_b_934_);
lean_dec(v_index_988_);
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_976_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
return v___x_991_;
}
case 1:
{
lean_object* v_index_992_; 
v_index_992_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_index_992_);
lean_dec_ref_known(v___x_987_, 1);
v___y_978_ = v___y_986_;
v_i_979_ = v_index_992_;
goto v___jp_977_;
}
default: 
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_994_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_986_, v___x_993_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_index_995_; 
v_index_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_index_995_);
lean_dec_ref_known(v___x_994_, 1);
v___y_978_ = v___y_986_;
v_i_979_ = v_index_995_;
goto v___jp_977_;
}
else
{
lean_object* v___x_996_; 
lean_dec(v_b_934_);
lean_dec(v_a_933_);
v___x_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_976_);
lean_ctor_set(v___x_996_, 1, v___y_986_);
return v___x_996_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_1008_, lean_object* v_00_u03b2_1009_, lean_object* v_x_1010_, lean_object* v_x_1011_, lean_object* v_inst_1012_, lean_object* v_m_1013_, lean_object* v_a_1014_, lean_object* v_b_1015_){
_start:
{
lean_object* v___x_1016_; 
lean_inc(v_a_1014_);
lean_inc_ref(v_x_1011_);
lean_inc_ref(v_x_1010_);
v___x_1016_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1010_, v_x_1011_, v_m_1013_, v_a_1014_);
switch(lean_obj_tag(v___x_1016_))
{
case 0:
{
lean_object* v_value_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
lean_dec(v_b_1015_);
lean_dec(v_a_1014_);
lean_dec_ref(v_x_1011_);
lean_dec_ref(v_x_1010_);
v_value_1017_ = lean_ctor_get(v___x_1016_, 2);
lean_inc(v_value_1017_);
lean_dec_ref_known(v___x_1016_, 3);
v___x_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1018_, 0, v_value_1017_);
v___x_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
lean_ctor_set(v___x_1019_, 1, v_m_1013_);
return v___x_1019_;
}
case 1:
{
lean_object* v_index_1020_; lean_object* v_size_1021_; lean_object* v_keyArray_1022_; lean_object* v___x_1023_; lean_object* v___y_1025_; lean_object* v_i_1026_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; uint8_t v___x_1047_; 
v_index_1020_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_index_1020_);
lean_dec_ref_known(v___x_1016_, 1);
v_size_1021_ = lean_ctor_get(v_m_1013_, 0);
v_keyArray_1022_ = lean_ctor_get(v_m_1013_, 1);
v___x_1023_ = lean_box(0);
v___x_1044_ = lean_unsigned_to_nat(1u);
v___x_1045_ = lean_nat_add(v_size_1021_, v___x_1044_);
v___x_1046_ = lean_array_get_size(v_keyArray_1022_);
v___x_1047_ = lean_nat_dec_lt(v___x_1045_, v___x_1046_);
if (v___x_1047_ == 0)
{
lean_dec(v___x_1045_);
lean_dec(v_index_1020_);
goto v___jp_1032_;
}
else
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1048_ = lean_unsigned_to_nat(4u);
v___x_1049_ = lean_nat_mul(v___x_1045_, v___x_1048_);
v___x_1050_ = lean_unsigned_to_nat(3u);
v___x_1051_ = lean_nat_mul(v___x_1046_, v___x_1050_);
v___x_1052_ = lean_nat_dec_le(v___x_1049_, v___x_1051_);
lean_dec(v___x_1051_);
lean_dec(v___x_1049_);
if (v___x_1052_ == 0)
{
lean_dec(v___x_1045_);
lean_dec(v_index_1020_);
goto v___jp_1032_;
}
else
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
lean_dec_ref(v_x_1011_);
lean_dec_ref(v_x_1010_);
v___x_1053_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1013_, v___x_1045_, v_index_1020_, v_a_1014_, v_b_1015_);
lean_dec(v_index_1020_);
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1023_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
return v___x_1054_;
}
}
v___jp_1024_:
{
lean_object* v_size_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v_size_1027_ = lean_ctor_get(v___y_1025_, 0);
v___x_1028_ = lean_unsigned_to_nat(1u);
v___x_1029_ = lean_nat_add(v_size_1027_, v___x_1028_);
v___x_1030_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1025_, v___x_1029_, v_i_1026_, v_a_1014_, v_b_1015_);
lean_dec(v_i_1026_);
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1023_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
return v___x_1031_;
}
v___jp_1032_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
lean_inc_ref(v_x_1011_);
lean_inc_ref(v_x_1010_);
v___x_1033_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1010_, v_x_1011_, v_m_1013_);
lean_inc(v_a_1014_);
v___x_1034_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1010_, v_x_1011_, v___x_1033_, v_a_1014_);
switch(lean_obj_tag(v___x_1034_))
{
case 0:
{
lean_object* v_index_1035_; lean_object* v_size_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v_index_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_index_1035_);
lean_dec_ref_known(v___x_1034_, 3);
v_size_1036_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_size_1036_);
v___x_1037_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1033_, v_size_1036_, v_index_1035_, v_a_1014_, v_b_1015_);
lean_dec(v_index_1035_);
v___x_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1023_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
return v___x_1038_;
}
case 1:
{
lean_object* v_index_1039_; 
v_index_1039_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_index_1039_);
lean_dec_ref_known(v___x_1034_, 1);
v___y_1025_ = v___x_1033_;
v_i_1026_ = v_index_1039_;
goto v___jp_1024_;
}
default: 
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = lean_unsigned_to_nat(0u);
v___x_1041_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1033_, v___x_1040_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_index_1042_; 
v_index_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_index_1042_);
lean_dec_ref_known(v___x_1041_, 1);
v___y_1025_ = v___x_1033_;
v_i_1026_ = v_index_1042_;
goto v___jp_1024_;
}
else
{
lean_object* v___x_1043_; 
lean_dec(v_b_1015_);
lean_dec(v_a_1014_);
v___x_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1023_);
lean_ctor_set(v___x_1043_, 1, v___x_1033_);
return v___x_1043_;
}
}
}
}
}
default: 
{
lean_object* v_size_1055_; lean_object* v_keyArray_1056_; lean_object* v___x_1057_; lean_object* v___y_1059_; lean_object* v_i_1060_; lean_object* v___y_1067_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; uint8_t v___x_1081_; 
v_size_1055_ = lean_ctor_get(v_m_1013_, 0);
v_keyArray_1056_ = lean_ctor_get(v_m_1013_, 1);
v___x_1057_ = lean_box(0);
v___x_1078_ = lean_unsigned_to_nat(1u);
v___x_1079_ = lean_nat_add(v_size_1055_, v___x_1078_);
v___x_1080_ = lean_array_get_size(v_keyArray_1056_);
v___x_1081_ = lean_nat_dec_lt(v___x_1079_, v___x_1080_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; 
lean_dec(v___x_1079_);
lean_inc_ref(v_x_1011_);
lean_inc_ref(v_x_1010_);
v___x_1082_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1010_, v_x_1011_, v_m_1013_);
v___y_1067_ = v___x_1082_;
goto v___jp_1066_;
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1083_ = lean_unsigned_to_nat(4u);
v___x_1084_ = lean_nat_mul(v___x_1079_, v___x_1083_);
lean_dec(v___x_1079_);
v___x_1085_ = lean_unsigned_to_nat(3u);
v___x_1086_ = lean_nat_mul(v___x_1080_, v___x_1085_);
v___x_1087_ = lean_nat_dec_le(v___x_1084_, v___x_1086_);
lean_dec(v___x_1086_);
lean_dec(v___x_1084_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; 
lean_inc_ref(v_x_1011_);
lean_inc_ref(v_x_1010_);
v___x_1088_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1010_, v_x_1011_, v_m_1013_);
v___y_1067_ = v___x_1088_;
goto v___jp_1066_;
}
else
{
v___y_1067_ = v_m_1013_;
goto v___jp_1066_;
}
}
v___jp_1058_:
{
lean_object* v_size_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v_size_1061_ = lean_ctor_get(v___y_1059_, 0);
v___x_1062_ = lean_unsigned_to_nat(1u);
v___x_1063_ = lean_nat_add(v_size_1061_, v___x_1062_);
v___x_1064_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1059_, v___x_1063_, v_i_1060_, v_a_1014_, v_b_1015_);
lean_dec(v_i_1060_);
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1057_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
return v___x_1065_;
}
v___jp_1066_:
{
lean_object* v___x_1068_; 
lean_inc(v_a_1014_);
v___x_1068_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1010_, v_x_1011_, v___y_1067_, v_a_1014_);
switch(lean_obj_tag(v___x_1068_))
{
case 0:
{
lean_object* v_index_1069_; lean_object* v_size_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v_index_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_index_1069_);
lean_dec_ref_known(v___x_1068_, 3);
v_size_1070_ = lean_ctor_get(v___y_1067_, 0);
lean_inc(v_size_1070_);
v___x_1071_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1067_, v_size_1070_, v_index_1069_, v_a_1014_, v_b_1015_);
lean_dec(v_index_1069_);
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1057_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
return v___x_1072_;
}
case 1:
{
lean_object* v_index_1073_; 
v_index_1073_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_index_1073_);
lean_dec_ref_known(v___x_1068_, 1);
v___y_1059_ = v___y_1067_;
v_i_1060_ = v_index_1073_;
goto v___jp_1058_;
}
default: 
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = lean_unsigned_to_nat(0u);
v___x_1075_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1067_, v___x_1074_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_index_1076_; 
v_index_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_index_1076_);
lean_dec_ref_known(v___x_1075_, 1);
v___y_1059_ = v___y_1067_;
v_i_1060_ = v_index_1076_;
goto v___jp_1058_;
}
else
{
lean_object* v___x_1077_; 
lean_dec(v_b_1015_);
lean_dec(v_a_1014_);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1057_);
lean_ctor_set(v___x_1077_, 1, v___y_1067_);
return v___x_1077_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x3f___redArg(lean_object* v_x_1089_, lean_object* v_x_1090_, lean_object* v_m_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_x_1089_, v_x_1090_, v_m_1091_, v_a_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x3f___redArg___boxed(lean_object* v_x_1094_, lean_object* v_x_1095_, lean_object* v_m_1096_, lean_object* v_a_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Std_ExtDHashMap_get_x3f___redArg(v_x_1094_, v_x_1095_, v_m_1096_, v_a_1097_);
lean_dec(v_m_1096_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x3f(lean_object* v_00_u03b1_1099_, lean_object* v_00_u03b2_1100_, lean_object* v_x_1101_, lean_object* v_x_1102_, lean_object* v_inst_1103_, lean_object* v_m_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_x_1101_, v_x_1102_, v_m_1104_, v_a_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x3f___boxed(lean_object* v_00_u03b1_1107_, lean_object* v_00_u03b2_1108_, lean_object* v_x_1109_, lean_object* v_x_1110_, lean_object* v_inst_1111_, lean_object* v_m_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Std_ExtDHashMap_get_x3f(v_00_u03b1_1107_, v_00_u03b2_1108_, v_x_1109_, v_x_1110_, v_inst_1111_, v_m_1112_, v_a_1113_);
lean_dec(v_m_1112_);
return v_res_1114_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_contains___redArg(lean_object* v_x_1115_, lean_object* v_x_1116_, lean_object* v_m_1117_, lean_object* v_a_1118_){
_start:
{
uint8_t v___x_1119_; 
v___x_1119_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_1115_, v_x_1116_, v_m_1117_, v_a_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_contains___redArg___boxed(lean_object* v_x_1120_, lean_object* v_x_1121_, lean_object* v_m_1122_, lean_object* v_a_1123_){
_start:
{
uint8_t v_res_1124_; lean_object* v_r_1125_; 
v_res_1124_ = l_Std_ExtDHashMap_contains___redArg(v_x_1120_, v_x_1121_, v_m_1122_, v_a_1123_);
lean_dec(v_m_1122_);
v_r_1125_ = lean_box(v_res_1124_);
return v_r_1125_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_contains(lean_object* v_00_u03b1_1126_, lean_object* v_00_u03b2_1127_, lean_object* v_x_1128_, lean_object* v_x_1129_, lean_object* v_inst_1130_, lean_object* v_inst_1131_, lean_object* v_m_1132_, lean_object* v_a_1133_){
_start:
{
uint8_t v___x_1134_; 
v___x_1134_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_1128_, v_x_1129_, v_m_1132_, v_a_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_contains___boxed(lean_object* v_00_u03b1_1135_, lean_object* v_00_u03b2_1136_, lean_object* v_x_1137_, lean_object* v_x_1138_, lean_object* v_inst_1139_, lean_object* v_inst_1140_, lean_object* v_m_1141_, lean_object* v_a_1142_){
_start:
{
uint8_t v_res_1143_; lean_object* v_r_1144_; 
v_res_1143_ = l_Std_ExtDHashMap_contains(v_00_u03b1_1135_, v_00_u03b2_1136_, v_x_1137_, v_x_1138_, v_inst_1139_, v_inst_1140_, v_m_1141_, v_a_1142_);
lean_dec(v_m_1141_);
v_r_1144_ = lean_box(v_res_1143_);
return v_r_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1145_, lean_object* v_00_u03b2_1146_, lean_object* v_x_1147_, lean_object* v_x_1148_, lean_object* v_inst_1149_, lean_object* v_inst_1150_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_box(0);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable___boxed(lean_object* v_00_u03b1_1152_, lean_object* v_00_u03b2_1153_, lean_object* v_x_1154_, lean_object* v_x_1155_, lean_object* v_inst_1156_, lean_object* v_inst_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable(v_00_u03b1_1152_, v_00_u03b2_1153_, v_x_1154_, v_x_1155_, v_inst_1156_, v_inst_1157_);
lean_dec_ref(v_x_1155_);
lean_dec_ref(v_x_1154_);
return v_res_1158_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_instDecidableMem___redArg(lean_object* v_x_1159_, lean_object* v_x_1160_, lean_object* v_m_1161_, lean_object* v_a_1162_){
_start:
{
uint8_t v___x_1163_; 
v___x_1163_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_1159_, v_x_1160_, v_m_1161_, v_a_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instDecidableMem___redArg___boxed(lean_object* v_x_1164_, lean_object* v_x_1165_, lean_object* v_m_1166_, lean_object* v_a_1167_){
_start:
{
uint8_t v_res_1168_; lean_object* v_r_1169_; 
v_res_1168_ = l_Std_ExtDHashMap_instDecidableMem___redArg(v_x_1164_, v_x_1165_, v_m_1166_, v_a_1167_);
lean_dec(v_m_1166_);
v_r_1169_ = lean_box(v_res_1168_);
return v_r_1169_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_instDecidableMem(lean_object* v_00_u03b1_1170_, lean_object* v_00_u03b2_1171_, lean_object* v_x_1172_, lean_object* v_x_1173_, lean_object* v_inst_1174_, lean_object* v_inst_1175_, lean_object* v_m_1176_, lean_object* v_a_1177_){
_start:
{
uint8_t v___x_1178_; 
v___x_1178_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_1172_, v_x_1173_, v_m_1176_, v_a_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instDecidableMem___boxed(lean_object* v_00_u03b1_1179_, lean_object* v_00_u03b2_1180_, lean_object* v_x_1181_, lean_object* v_x_1182_, lean_object* v_inst_1183_, lean_object* v_inst_1184_, lean_object* v_m_1185_, lean_object* v_a_1186_){
_start:
{
uint8_t v_res_1187_; lean_object* v_r_1188_; 
v_res_1187_ = l_Std_ExtDHashMap_instDecidableMem(v_00_u03b1_1179_, v_00_u03b2_1180_, v_x_1181_, v_x_1182_, v_inst_1183_, v_inst_1184_, v_m_1185_, v_a_1186_);
lean_dec(v_m_1185_);
v_r_1188_ = lean_box(v_res_1187_);
return v_r_1188_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get___redArg(lean_object* v_x_1189_, lean_object* v_x_1190_, lean_object* v_m_1191_, lean_object* v_a_1192_){
_start:
{
lean_object* v___x_1193_; lean_object* v_val_1194_; 
v___x_1193_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_x_1189_, v_x_1190_, v_m_1191_, v_a_1192_);
v_val_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_val_1194_);
lean_dec(v___x_1193_);
return v_val_1194_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get___redArg___boxed(lean_object* v_x_1195_, lean_object* v_x_1196_, lean_object* v_m_1197_, lean_object* v_a_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Std_ExtDHashMap_get___redArg(v_x_1195_, v_x_1196_, v_m_1197_, v_a_1198_);
lean_dec(v_m_1197_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get(lean_object* v_00_u03b1_1200_, lean_object* v_00_u03b2_1201_, lean_object* v_x_1202_, lean_object* v_x_1203_, lean_object* v_inst_1204_, lean_object* v_m_1205_, lean_object* v_a_1206_, lean_object* v_h_1207_){
_start:
{
lean_object* v___x_1208_; lean_object* v_val_1209_; 
v___x_1208_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_x_1202_, v_x_1203_, v_m_1205_, v_a_1206_);
v_val_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_val_1209_);
lean_dec(v___x_1208_);
return v_val_1209_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get___boxed(lean_object* v_00_u03b1_1210_, lean_object* v_00_u03b2_1211_, lean_object* v_x_1212_, lean_object* v_x_1213_, lean_object* v_inst_1214_, lean_object* v_m_1215_, lean_object* v_a_1216_, lean_object* v_h_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Std_ExtDHashMap_get(v_00_u03b1_1210_, v_00_u03b2_1211_, v_x_1212_, v_x_1213_, v_inst_1214_, v_m_1215_, v_a_1216_, v_h_1217_);
lean_dec(v_m_1215_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x21___redArg(lean_object* v_x_1219_, lean_object* v_x_1220_, lean_object* v_m_1221_, lean_object* v_a_1222_, lean_object* v_inst_1223_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(v_x_1219_, v_x_1220_, v_m_1221_, v_a_1222_, v_inst_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x21___redArg___boxed(lean_object* v_x_1225_, lean_object* v_x_1226_, lean_object* v_m_1227_, lean_object* v_a_1228_, lean_object* v_inst_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Std_ExtDHashMap_get_x21___redArg(v_x_1225_, v_x_1226_, v_m_1227_, v_a_1228_, v_inst_1229_);
lean_dec(v_inst_1229_);
lean_dec(v_m_1227_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x21(lean_object* v_00_u03b1_1231_, lean_object* v_00_u03b2_1232_, lean_object* v_x_1233_, lean_object* v_x_1234_, lean_object* v_inst_1235_, lean_object* v_m_1236_, lean_object* v_a_1237_, lean_object* v_inst_1238_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(v_x_1233_, v_x_1234_, v_m_1236_, v_a_1237_, v_inst_1238_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x21___boxed(lean_object* v_00_u03b1_1240_, lean_object* v_00_u03b2_1241_, lean_object* v_x_1242_, lean_object* v_x_1243_, lean_object* v_inst_1244_, lean_object* v_m_1245_, lean_object* v_a_1246_, lean_object* v_inst_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Std_ExtDHashMap_get_x21(v_00_u03b1_1240_, v_00_u03b2_1241_, v_x_1242_, v_x_1243_, v_inst_1244_, v_m_1245_, v_a_1246_, v_inst_1247_);
lean_dec(v_inst_1247_);
lean_dec(v_m_1245_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getD___redArg(lean_object* v_x_1249_, lean_object* v_x_1250_, lean_object* v_m_1251_, lean_object* v_a_1252_, lean_object* v_fallback_1253_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(v_x_1249_, v_x_1250_, v_m_1251_, v_a_1252_, v_fallback_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getD___redArg___boxed(lean_object* v_x_1255_, lean_object* v_x_1256_, lean_object* v_m_1257_, lean_object* v_a_1258_, lean_object* v_fallback_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Std_ExtDHashMap_getD___redArg(v_x_1255_, v_x_1256_, v_m_1257_, v_a_1258_, v_fallback_1259_);
lean_dec(v_fallback_1259_);
lean_dec(v_m_1257_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getD(lean_object* v_00_u03b1_1261_, lean_object* v_00_u03b2_1262_, lean_object* v_x_1263_, lean_object* v_x_1264_, lean_object* v_inst_1265_, lean_object* v_m_1266_, lean_object* v_a_1267_, lean_object* v_fallback_1268_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(v_x_1263_, v_x_1264_, v_m_1266_, v_a_1267_, v_fallback_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getD___boxed(lean_object* v_00_u03b1_1270_, lean_object* v_00_u03b2_1271_, lean_object* v_x_1272_, lean_object* v_x_1273_, lean_object* v_inst_1274_, lean_object* v_m_1275_, lean_object* v_a_1276_, lean_object* v_fallback_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Std_ExtDHashMap_getD(v_00_u03b1_1270_, v_00_u03b2_1271_, v_x_1272_, v_x_1273_, v_inst_1274_, v_m_1275_, v_a_1276_, v_fallback_1277_);
lean_dec(v_fallback_1277_);
lean_dec(v_m_1275_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_erase___redArg(lean_object* v_x_1279_, lean_object* v_x_1280_, lean_object* v_m_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_1279_, v_x_1280_, v_m_1281_, v_a_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_erase(lean_object* v_00_u03b1_1284_, lean_object* v_00_u03b2_1285_, lean_object* v_x_1286_, lean_object* v_x_1287_, lean_object* v_inst_1288_, lean_object* v_inst_1289_, lean_object* v_m_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_1286_, v_x_1287_, v_m_1290_, v_a_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x3f___redArg(lean_object* v_x_1293_, lean_object* v_x_1294_, lean_object* v_m_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_1293_, v_x_1294_, v_m_1295_, v_a_1296_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x3f___redArg___boxed(lean_object* v_x_1298_, lean_object* v_x_1299_, lean_object* v_m_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Std_ExtDHashMap_Const_get_x3f___redArg(v_x_1298_, v_x_1299_, v_m_1300_, v_a_1301_);
lean_dec(v_m_1300_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x3f(lean_object* v_00_u03b1_1303_, lean_object* v_x_1304_, lean_object* v_x_1305_, lean_object* v_00_u03b2_1306_, lean_object* v_inst_1307_, lean_object* v_inst_1308_, lean_object* v_m_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_1304_, v_x_1305_, v_m_1309_, v_a_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x3f___boxed(lean_object* v_00_u03b1_1312_, lean_object* v_x_1313_, lean_object* v_x_1314_, lean_object* v_00_u03b2_1315_, lean_object* v_inst_1316_, lean_object* v_inst_1317_, lean_object* v_m_1318_, lean_object* v_a_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Std_ExtDHashMap_Const_get_x3f(v_00_u03b1_1312_, v_x_1313_, v_x_1314_, v_00_u03b2_1315_, v_inst_1316_, v_inst_1317_, v_m_1318_, v_a_1319_);
lean_dec(v_m_1318_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get___redArg(lean_object* v_x_1321_, lean_object* v_x_1322_, lean_object* v_m_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v___x_1325_; lean_object* v_val_1326_; 
v___x_1325_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_1321_, v_x_1322_, v_m_1323_, v_a_1324_);
v_val_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_val_1326_);
lean_dec(v___x_1325_);
return v_val_1326_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get___redArg___boxed(lean_object* v_x_1327_, lean_object* v_x_1328_, lean_object* v_m_1329_, lean_object* v_a_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Std_ExtDHashMap_Const_get___redArg(v_x_1327_, v_x_1328_, v_m_1329_, v_a_1330_);
lean_dec(v_m_1329_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get(lean_object* v_00_u03b1_1332_, lean_object* v_x_1333_, lean_object* v_x_1334_, lean_object* v_00_u03b2_1335_, lean_object* v_inst_1336_, lean_object* v_inst_1337_, lean_object* v_m_1338_, lean_object* v_a_1339_, lean_object* v_h_1340_){
_start:
{
lean_object* v___x_1341_; lean_object* v_val_1342_; 
v___x_1341_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_1333_, v_x_1334_, v_m_1338_, v_a_1339_);
v_val_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_val_1342_);
lean_dec(v___x_1341_);
return v_val_1342_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get___boxed(lean_object* v_00_u03b1_1343_, lean_object* v_x_1344_, lean_object* v_x_1345_, lean_object* v_00_u03b2_1346_, lean_object* v_inst_1347_, lean_object* v_inst_1348_, lean_object* v_m_1349_, lean_object* v_a_1350_, lean_object* v_h_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Std_ExtDHashMap_Const_get(v_00_u03b1_1343_, v_x_1344_, v_x_1345_, v_00_u03b2_1346_, v_inst_1347_, v_inst_1348_, v_m_1349_, v_a_1350_, v_h_1351_);
lean_dec(v_m_1349_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getD___redArg(lean_object* v_x_1353_, lean_object* v_x_1354_, lean_object* v_m_1355_, lean_object* v_a_1356_, lean_object* v_fallback_1357_){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_x_1353_, v_x_1354_, v_m_1355_, v_a_1356_, v_fallback_1357_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getD___redArg___boxed(lean_object* v_x_1359_, lean_object* v_x_1360_, lean_object* v_m_1361_, lean_object* v_a_1362_, lean_object* v_fallback_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Std_ExtDHashMap_Const_getD___redArg(v_x_1359_, v_x_1360_, v_m_1361_, v_a_1362_, v_fallback_1363_);
lean_dec(v_fallback_1363_);
lean_dec(v_m_1361_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getD(lean_object* v_00_u03b1_1365_, lean_object* v_x_1366_, lean_object* v_x_1367_, lean_object* v_00_u03b2_1368_, lean_object* v_inst_1369_, lean_object* v_inst_1370_, lean_object* v_m_1371_, lean_object* v_a_1372_, lean_object* v_fallback_1373_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_x_1366_, v_x_1367_, v_m_1371_, v_a_1372_, v_fallback_1373_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getD___boxed(lean_object* v_00_u03b1_1375_, lean_object* v_x_1376_, lean_object* v_x_1377_, lean_object* v_00_u03b2_1378_, lean_object* v_inst_1379_, lean_object* v_inst_1380_, lean_object* v_m_1381_, lean_object* v_a_1382_, lean_object* v_fallback_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Std_ExtDHashMap_Const_getD(v_00_u03b1_1375_, v_x_1376_, v_x_1377_, v_00_u03b2_1378_, v_inst_1379_, v_inst_1380_, v_m_1381_, v_a_1382_, v_fallback_1383_);
lean_dec(v_fallback_1383_);
lean_dec(v_m_1381_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x21___redArg(lean_object* v_x_1385_, lean_object* v_x_1386_, lean_object* v_inst_1387_, lean_object* v_m_1388_, lean_object* v_a_1389_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_x_1385_, v_x_1386_, v_inst_1387_, v_m_1388_, v_a_1389_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x21___redArg___boxed(lean_object* v_x_1391_, lean_object* v_x_1392_, lean_object* v_inst_1393_, lean_object* v_m_1394_, lean_object* v_a_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Std_ExtDHashMap_Const_get_x21___redArg(v_x_1391_, v_x_1392_, v_inst_1393_, v_m_1394_, v_a_1395_);
lean_dec(v_m_1394_);
lean_dec(v_inst_1393_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x21(lean_object* v_00_u03b1_1397_, lean_object* v_x_1398_, lean_object* v_x_1399_, lean_object* v_00_u03b2_1400_, lean_object* v_inst_1401_, lean_object* v_inst_1402_, lean_object* v_inst_1403_, lean_object* v_m_1404_, lean_object* v_a_1405_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_x_1398_, v_x_1399_, v_inst_1403_, v_m_1404_, v_a_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x21___boxed(lean_object* v_00_u03b1_1407_, lean_object* v_x_1408_, lean_object* v_x_1409_, lean_object* v_00_u03b2_1410_, lean_object* v_inst_1411_, lean_object* v_inst_1412_, lean_object* v_inst_1413_, lean_object* v_m_1414_, lean_object* v_a_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Std_ExtDHashMap_Const_get_x21(v_00_u03b1_1407_, v_x_1408_, v_x_1409_, v_00_u03b2_1410_, v_inst_1411_, v_inst_1412_, v_inst_1413_, v_m_1414_, v_a_1415_);
lean_dec(v_m_1414_);
lean_dec(v_inst_1413_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getThenInsertIfNew_x3f___redArg(lean_object* v_x_1417_, lean_object* v_x_1418_, lean_object* v_m_1419_, lean_object* v_a_1420_, lean_object* v_b_1421_){
_start:
{
lean_object* v___x_1422_; 
lean_inc(v_a_1420_);
lean_inc_ref(v_x_1418_);
lean_inc_ref(v_x_1417_);
v___x_1422_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1417_, v_x_1418_, v_m_1419_, v_a_1420_);
switch(lean_obj_tag(v___x_1422_))
{
case 0:
{
lean_object* v_value_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
lean_dec(v_b_1421_);
lean_dec(v_a_1420_);
lean_dec_ref(v_x_1418_);
lean_dec_ref(v_x_1417_);
v_value_1423_ = lean_ctor_get(v___x_1422_, 2);
lean_inc(v_value_1423_);
lean_dec_ref_known(v___x_1422_, 3);
v___x_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1424_, 0, v_value_1423_);
v___x_1425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
lean_ctor_set(v___x_1425_, 1, v_m_1419_);
return v___x_1425_;
}
case 1:
{
lean_object* v_index_1426_; lean_object* v_size_1427_; lean_object* v_keyArray_1428_; lean_object* v___x_1429_; lean_object* v___y_1431_; lean_object* v_i_1432_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; uint8_t v___x_1453_; 
v_index_1426_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_index_1426_);
lean_dec_ref_known(v___x_1422_, 1);
v_size_1427_ = lean_ctor_get(v_m_1419_, 0);
v_keyArray_1428_ = lean_ctor_get(v_m_1419_, 1);
v___x_1429_ = lean_box(0);
v___x_1450_ = lean_unsigned_to_nat(1u);
v___x_1451_ = lean_nat_add(v_size_1427_, v___x_1450_);
v___x_1452_ = lean_array_get_size(v_keyArray_1428_);
v___x_1453_ = lean_nat_dec_lt(v___x_1451_, v___x_1452_);
if (v___x_1453_ == 0)
{
lean_dec(v___x_1451_);
lean_dec(v_index_1426_);
goto v___jp_1438_;
}
else
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; 
v___x_1454_ = lean_unsigned_to_nat(4u);
v___x_1455_ = lean_nat_mul(v___x_1451_, v___x_1454_);
v___x_1456_ = lean_unsigned_to_nat(3u);
v___x_1457_ = lean_nat_mul(v___x_1452_, v___x_1456_);
v___x_1458_ = lean_nat_dec_le(v___x_1455_, v___x_1457_);
lean_dec(v___x_1457_);
lean_dec(v___x_1455_);
if (v___x_1458_ == 0)
{
lean_dec(v___x_1451_);
lean_dec(v_index_1426_);
goto v___jp_1438_;
}
else
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
lean_dec_ref(v_x_1418_);
lean_dec_ref(v_x_1417_);
v___x_1459_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1419_, v___x_1451_, v_index_1426_, v_a_1420_, v_b_1421_);
lean_dec(v_index_1426_);
v___x_1460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1429_);
lean_ctor_set(v___x_1460_, 1, v___x_1459_);
return v___x_1460_;
}
}
v___jp_1430_:
{
lean_object* v_size_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v_size_1433_ = lean_ctor_get(v___y_1431_, 0);
v___x_1434_ = lean_unsigned_to_nat(1u);
v___x_1435_ = lean_nat_add(v_size_1433_, v___x_1434_);
v___x_1436_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1431_, v___x_1435_, v_i_1432_, v_a_1420_, v_b_1421_);
lean_dec(v_i_1432_);
v___x_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1429_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
return v___x_1437_;
}
v___jp_1438_:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
lean_inc_ref(v_x_1418_);
lean_inc_ref(v_x_1417_);
v___x_1439_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1417_, v_x_1418_, v_m_1419_);
lean_inc(v_a_1420_);
v___x_1440_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1417_, v_x_1418_, v___x_1439_, v_a_1420_);
switch(lean_obj_tag(v___x_1440_))
{
case 0:
{
lean_object* v_index_1441_; lean_object* v_size_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v_index_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_index_1441_);
lean_dec_ref_known(v___x_1440_, 3);
v_size_1442_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_size_1442_);
v___x_1443_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1439_, v_size_1442_, v_index_1441_, v_a_1420_, v_b_1421_);
lean_dec(v_index_1441_);
v___x_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1429_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
return v___x_1444_;
}
case 1:
{
lean_object* v_index_1445_; 
v_index_1445_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_index_1445_);
lean_dec_ref_known(v___x_1440_, 1);
v___y_1431_ = v___x_1439_;
v_i_1432_ = v_index_1445_;
goto v___jp_1430_;
}
default: 
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = lean_unsigned_to_nat(0u);
v___x_1447_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1439_, v___x_1446_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_index_1448_; 
v_index_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_index_1448_);
lean_dec_ref_known(v___x_1447_, 1);
v___y_1431_ = v___x_1439_;
v_i_1432_ = v_index_1448_;
goto v___jp_1430_;
}
else
{
lean_object* v___x_1449_; 
lean_dec(v_b_1421_);
lean_dec(v_a_1420_);
v___x_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1429_);
lean_ctor_set(v___x_1449_, 1, v___x_1439_);
return v___x_1449_;
}
}
}
}
}
default: 
{
lean_object* v_size_1461_; lean_object* v_keyArray_1462_; lean_object* v___x_1463_; lean_object* v___y_1465_; lean_object* v_i_1466_; lean_object* v___y_1473_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; uint8_t v___x_1487_; 
v_size_1461_ = lean_ctor_get(v_m_1419_, 0);
v_keyArray_1462_ = lean_ctor_get(v_m_1419_, 1);
v___x_1463_ = lean_box(0);
v___x_1484_ = lean_unsigned_to_nat(1u);
v___x_1485_ = lean_nat_add(v_size_1461_, v___x_1484_);
v___x_1486_ = lean_array_get_size(v_keyArray_1462_);
v___x_1487_ = lean_nat_dec_lt(v___x_1485_, v___x_1486_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; 
lean_dec(v___x_1485_);
lean_inc_ref(v_x_1418_);
lean_inc_ref(v_x_1417_);
v___x_1488_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1417_, v_x_1418_, v_m_1419_);
v___y_1473_ = v___x_1488_;
goto v___jp_1472_;
}
else
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; uint8_t v___x_1493_; 
v___x_1489_ = lean_unsigned_to_nat(4u);
v___x_1490_ = lean_nat_mul(v___x_1485_, v___x_1489_);
lean_dec(v___x_1485_);
v___x_1491_ = lean_unsigned_to_nat(3u);
v___x_1492_ = lean_nat_mul(v___x_1486_, v___x_1491_);
v___x_1493_ = lean_nat_dec_le(v___x_1490_, v___x_1492_);
lean_dec(v___x_1492_);
lean_dec(v___x_1490_);
if (v___x_1493_ == 0)
{
lean_object* v___x_1494_; 
lean_inc_ref(v_x_1418_);
lean_inc_ref(v_x_1417_);
v___x_1494_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1417_, v_x_1418_, v_m_1419_);
v___y_1473_ = v___x_1494_;
goto v___jp_1472_;
}
else
{
v___y_1473_ = v_m_1419_;
goto v___jp_1472_;
}
}
v___jp_1464_:
{
lean_object* v_size_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v_size_1467_ = lean_ctor_get(v___y_1465_, 0);
v___x_1468_ = lean_unsigned_to_nat(1u);
v___x_1469_ = lean_nat_add(v_size_1467_, v___x_1468_);
v___x_1470_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1465_, v___x_1469_, v_i_1466_, v_a_1420_, v_b_1421_);
lean_dec(v_i_1466_);
v___x_1471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1463_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
return v___x_1471_;
}
v___jp_1472_:
{
lean_object* v___x_1474_; 
lean_inc(v_a_1420_);
v___x_1474_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1417_, v_x_1418_, v___y_1473_, v_a_1420_);
switch(lean_obj_tag(v___x_1474_))
{
case 0:
{
lean_object* v_index_1475_; lean_object* v_size_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v_index_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_index_1475_);
lean_dec_ref_known(v___x_1474_, 3);
v_size_1476_ = lean_ctor_get(v___y_1473_, 0);
lean_inc(v_size_1476_);
v___x_1477_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1473_, v_size_1476_, v_index_1475_, v_a_1420_, v_b_1421_);
lean_dec(v_index_1475_);
v___x_1478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1463_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
return v___x_1478_;
}
case 1:
{
lean_object* v_index_1479_; 
v_index_1479_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_index_1479_);
lean_dec_ref_known(v___x_1474_, 1);
v___y_1465_ = v___y_1473_;
v_i_1466_ = v_index_1479_;
goto v___jp_1464_;
}
default: 
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1480_ = lean_unsigned_to_nat(0u);
v___x_1481_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1473_, v___x_1480_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_index_1482_; 
v_index_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_index_1482_);
lean_dec_ref_known(v___x_1481_, 1);
v___y_1465_ = v___y_1473_;
v_i_1466_ = v_index_1482_;
goto v___jp_1464_;
}
else
{
lean_object* v___x_1483_; 
lean_dec(v_b_1421_);
lean_dec(v_a_1420_);
v___x_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1463_);
lean_ctor_set(v___x_1483_, 1, v___y_1473_);
return v___x_1483_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_1495_, lean_object* v_x_1496_, lean_object* v_x_1497_, lean_object* v_00_u03b2_1498_, lean_object* v_inst_1499_, lean_object* v_inst_1500_, lean_object* v_m_1501_, lean_object* v_a_1502_, lean_object* v_b_1503_){
_start:
{
lean_object* v___x_1504_; 
lean_inc(v_a_1502_);
lean_inc_ref(v_x_1497_);
lean_inc_ref(v_x_1496_);
v___x_1504_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1496_, v_x_1497_, v_m_1501_, v_a_1502_);
switch(lean_obj_tag(v___x_1504_))
{
case 0:
{
lean_object* v_value_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
lean_dec(v_b_1503_);
lean_dec(v_a_1502_);
lean_dec_ref(v_x_1497_);
lean_dec_ref(v_x_1496_);
v_value_1505_ = lean_ctor_get(v___x_1504_, 2);
lean_inc(v_value_1505_);
lean_dec_ref_known(v___x_1504_, 3);
v___x_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1506_, 0, v_value_1505_);
v___x_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
lean_ctor_set(v___x_1507_, 1, v_m_1501_);
return v___x_1507_;
}
case 1:
{
lean_object* v_index_1508_; lean_object* v_size_1509_; lean_object* v_keyArray_1510_; lean_object* v___x_1511_; lean_object* v___y_1513_; lean_object* v_i_1514_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; uint8_t v___x_1535_; 
v_index_1508_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_index_1508_);
lean_dec_ref_known(v___x_1504_, 1);
v_size_1509_ = lean_ctor_get(v_m_1501_, 0);
v_keyArray_1510_ = lean_ctor_get(v_m_1501_, 1);
v___x_1511_ = lean_box(0);
v___x_1532_ = lean_unsigned_to_nat(1u);
v___x_1533_ = lean_nat_add(v_size_1509_, v___x_1532_);
v___x_1534_ = lean_array_get_size(v_keyArray_1510_);
v___x_1535_ = lean_nat_dec_lt(v___x_1533_, v___x_1534_);
if (v___x_1535_ == 0)
{
lean_dec(v___x_1533_);
lean_dec(v_index_1508_);
goto v___jp_1520_;
}
else
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; 
v___x_1536_ = lean_unsigned_to_nat(4u);
v___x_1537_ = lean_nat_mul(v___x_1533_, v___x_1536_);
v___x_1538_ = lean_unsigned_to_nat(3u);
v___x_1539_ = lean_nat_mul(v___x_1534_, v___x_1538_);
v___x_1540_ = lean_nat_dec_le(v___x_1537_, v___x_1539_);
lean_dec(v___x_1539_);
lean_dec(v___x_1537_);
if (v___x_1540_ == 0)
{
lean_dec(v___x_1533_);
lean_dec(v_index_1508_);
goto v___jp_1520_;
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
lean_dec_ref(v_x_1497_);
lean_dec_ref(v_x_1496_);
v___x_1541_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1501_, v___x_1533_, v_index_1508_, v_a_1502_, v_b_1503_);
lean_dec(v_index_1508_);
v___x_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1511_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
return v___x_1542_;
}
}
v___jp_1512_:
{
lean_object* v_size_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v_size_1515_ = lean_ctor_get(v___y_1513_, 0);
v___x_1516_ = lean_unsigned_to_nat(1u);
v___x_1517_ = lean_nat_add(v_size_1515_, v___x_1516_);
v___x_1518_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1513_, v___x_1517_, v_i_1514_, v_a_1502_, v_b_1503_);
lean_dec(v_i_1514_);
v___x_1519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1511_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
return v___x_1519_;
}
v___jp_1520_:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
lean_inc_ref(v_x_1497_);
lean_inc_ref(v_x_1496_);
v___x_1521_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1496_, v_x_1497_, v_m_1501_);
lean_inc(v_a_1502_);
v___x_1522_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1496_, v_x_1497_, v___x_1521_, v_a_1502_);
switch(lean_obj_tag(v___x_1522_))
{
case 0:
{
lean_object* v_index_1523_; lean_object* v_size_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v_index_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_index_1523_);
lean_dec_ref_known(v___x_1522_, 3);
v_size_1524_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_size_1524_);
v___x_1525_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1521_, v_size_1524_, v_index_1523_, v_a_1502_, v_b_1503_);
lean_dec(v_index_1523_);
v___x_1526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1511_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
return v___x_1526_;
}
case 1:
{
lean_object* v_index_1527_; 
v_index_1527_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_index_1527_);
lean_dec_ref_known(v___x_1522_, 1);
v___y_1513_ = v___x_1521_;
v_i_1514_ = v_index_1527_;
goto v___jp_1512_;
}
default: 
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = lean_unsigned_to_nat(0u);
v___x_1529_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1521_, v___x_1528_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_index_1530_; 
v_index_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_index_1530_);
lean_dec_ref_known(v___x_1529_, 1);
v___y_1513_ = v___x_1521_;
v_i_1514_ = v_index_1530_;
goto v___jp_1512_;
}
else
{
lean_object* v___x_1531_; 
lean_dec(v_b_1503_);
lean_dec(v_a_1502_);
v___x_1531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1511_);
lean_ctor_set(v___x_1531_, 1, v___x_1521_);
return v___x_1531_;
}
}
}
}
}
default: 
{
lean_object* v_size_1543_; lean_object* v_keyArray_1544_; lean_object* v___x_1545_; lean_object* v___y_1547_; lean_object* v_i_1548_; lean_object* v___y_1555_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; 
v_size_1543_ = lean_ctor_get(v_m_1501_, 0);
v_keyArray_1544_ = lean_ctor_get(v_m_1501_, 1);
v___x_1545_ = lean_box(0);
v___x_1566_ = lean_unsigned_to_nat(1u);
v___x_1567_ = lean_nat_add(v_size_1543_, v___x_1566_);
v___x_1568_ = lean_array_get_size(v_keyArray_1544_);
v___x_1569_ = lean_nat_dec_lt(v___x_1567_, v___x_1568_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; 
lean_dec(v___x_1567_);
lean_inc_ref(v_x_1497_);
lean_inc_ref(v_x_1496_);
v___x_1570_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1496_, v_x_1497_, v_m_1501_);
v___y_1555_ = v___x_1570_;
goto v___jp_1554_;
}
else
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; 
v___x_1571_ = lean_unsigned_to_nat(4u);
v___x_1572_ = lean_nat_mul(v___x_1567_, v___x_1571_);
lean_dec(v___x_1567_);
v___x_1573_ = lean_unsigned_to_nat(3u);
v___x_1574_ = lean_nat_mul(v___x_1568_, v___x_1573_);
v___x_1575_ = lean_nat_dec_le(v___x_1572_, v___x_1574_);
lean_dec(v___x_1574_);
lean_dec(v___x_1572_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; 
lean_inc_ref(v_x_1497_);
lean_inc_ref(v_x_1496_);
v___x_1576_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1496_, v_x_1497_, v_m_1501_);
v___y_1555_ = v___x_1576_;
goto v___jp_1554_;
}
else
{
v___y_1555_ = v_m_1501_;
goto v___jp_1554_;
}
}
v___jp_1546_:
{
lean_object* v_size_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v_size_1549_ = lean_ctor_get(v___y_1547_, 0);
v___x_1550_ = lean_unsigned_to_nat(1u);
v___x_1551_ = lean_nat_add(v_size_1549_, v___x_1550_);
v___x_1552_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1547_, v___x_1551_, v_i_1548_, v_a_1502_, v_b_1503_);
lean_dec(v_i_1548_);
v___x_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1545_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
return v___x_1553_;
}
v___jp_1554_:
{
lean_object* v___x_1556_; 
lean_inc(v_a_1502_);
v___x_1556_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1496_, v_x_1497_, v___y_1555_, v_a_1502_);
switch(lean_obj_tag(v___x_1556_))
{
case 0:
{
lean_object* v_index_1557_; lean_object* v_size_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v_index_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_index_1557_);
lean_dec_ref_known(v___x_1556_, 3);
v_size_1558_ = lean_ctor_get(v___y_1555_, 0);
lean_inc(v_size_1558_);
v___x_1559_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1555_, v_size_1558_, v_index_1557_, v_a_1502_, v_b_1503_);
lean_dec(v_index_1557_);
v___x_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1545_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
return v___x_1560_;
}
case 1:
{
lean_object* v_index_1561_; 
v_index_1561_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_index_1561_);
lean_dec_ref_known(v___x_1556_, 1);
v___y_1547_ = v___y_1555_;
v_i_1548_ = v_index_1561_;
goto v___jp_1546_;
}
default: 
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = lean_unsigned_to_nat(0u);
v___x_1563_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1555_, v___x_1562_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_index_1564_; 
v_index_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_index_1564_);
lean_dec_ref_known(v___x_1563_, 1);
v___y_1547_ = v___y_1555_;
v_i_1548_ = v_index_1564_;
goto v___jp_1546_;
}
else
{
lean_object* v___x_1565_; 
lean_dec(v_b_1503_);
lean_dec(v_a_1502_);
v___x_1565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1545_);
lean_ctor_set(v___x_1565_, 1, v___y_1555_);
return v___x_1565_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x3f___redArg(lean_object* v_x_1577_, lean_object* v_x_1578_, lean_object* v_m_1579_, lean_object* v_a_1580_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_1577_, v_x_1578_, v_m_1579_, v_a_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x3f___redArg___boxed(lean_object* v_x_1582_, lean_object* v_x_1583_, lean_object* v_m_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_Std_ExtDHashMap_getKey_x3f___redArg(v_x_1582_, v_x_1583_, v_m_1584_, v_a_1585_);
lean_dec(v_m_1584_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x3f(lean_object* v_00_u03b1_1587_, lean_object* v_00_u03b2_1588_, lean_object* v_x_1589_, lean_object* v_x_1590_, lean_object* v_inst_1591_, lean_object* v_inst_1592_, lean_object* v_m_1593_, lean_object* v_a_1594_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_1589_, v_x_1590_, v_m_1593_, v_a_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x3f___boxed(lean_object* v_00_u03b1_1596_, lean_object* v_00_u03b2_1597_, lean_object* v_x_1598_, lean_object* v_x_1599_, lean_object* v_inst_1600_, lean_object* v_inst_1601_, lean_object* v_m_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Std_ExtDHashMap_getKey_x3f(v_00_u03b1_1596_, v_00_u03b2_1597_, v_x_1598_, v_x_1599_, v_inst_1600_, v_inst_1601_, v_m_1602_, v_a_1603_);
lean_dec(v_m_1602_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey___redArg(lean_object* v_x_1605_, lean_object* v_x_1606_, lean_object* v_m_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v___x_1609_; lean_object* v_val_1610_; 
v___x_1609_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_1605_, v_x_1606_, v_m_1607_, v_a_1608_);
v_val_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_val_1610_);
lean_dec(v___x_1609_);
return v_val_1610_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey___redArg___boxed(lean_object* v_x_1611_, lean_object* v_x_1612_, lean_object* v_m_1613_, lean_object* v_a_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Std_ExtDHashMap_getKey___redArg(v_x_1611_, v_x_1612_, v_m_1613_, v_a_1614_);
lean_dec(v_m_1613_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey(lean_object* v_00_u03b1_1616_, lean_object* v_00_u03b2_1617_, lean_object* v_x_1618_, lean_object* v_x_1619_, lean_object* v_inst_1620_, lean_object* v_inst_1621_, lean_object* v_m_1622_, lean_object* v_a_1623_, lean_object* v_h_1624_){
_start:
{
lean_object* v___x_1625_; lean_object* v_val_1626_; 
v___x_1625_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_1618_, v_x_1619_, v_m_1622_, v_a_1623_);
v_val_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_val_1626_);
lean_dec(v___x_1625_);
return v_val_1626_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey___boxed(lean_object* v_00_u03b1_1627_, lean_object* v_00_u03b2_1628_, lean_object* v_x_1629_, lean_object* v_x_1630_, lean_object* v_inst_1631_, lean_object* v_inst_1632_, lean_object* v_m_1633_, lean_object* v_a_1634_, lean_object* v_h_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Std_ExtDHashMap_getKey(v_00_u03b1_1627_, v_00_u03b2_1628_, v_x_1629_, v_x_1630_, v_inst_1631_, v_inst_1632_, v_m_1633_, v_a_1634_, v_h_1635_);
lean_dec(v_m_1633_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x21___redArg(lean_object* v_x_1637_, lean_object* v_x_1638_, lean_object* v_inst_1639_, lean_object* v_m_1640_, lean_object* v_a_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_1637_, v_x_1638_, v_inst_1639_, v_m_1640_, v_a_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x21___redArg___boxed(lean_object* v_x_1643_, lean_object* v_x_1644_, lean_object* v_inst_1645_, lean_object* v_m_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Std_ExtDHashMap_getKey_x21___redArg(v_x_1643_, v_x_1644_, v_inst_1645_, v_m_1646_, v_a_1647_);
lean_dec(v_m_1646_);
lean_dec(v_inst_1645_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x21(lean_object* v_00_u03b1_1649_, lean_object* v_00_u03b2_1650_, lean_object* v_x_1651_, lean_object* v_x_1652_, lean_object* v_inst_1653_, lean_object* v_inst_1654_, lean_object* v_inst_1655_, lean_object* v_m_1656_, lean_object* v_a_1657_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_1651_, v_x_1652_, v_inst_1655_, v_m_1656_, v_a_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x21___boxed(lean_object* v_00_u03b1_1659_, lean_object* v_00_u03b2_1660_, lean_object* v_x_1661_, lean_object* v_x_1662_, lean_object* v_inst_1663_, lean_object* v_inst_1664_, lean_object* v_inst_1665_, lean_object* v_m_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Std_ExtDHashMap_getKey_x21(v_00_u03b1_1659_, v_00_u03b2_1660_, v_x_1661_, v_x_1662_, v_inst_1663_, v_inst_1664_, v_inst_1665_, v_m_1666_, v_a_1667_);
lean_dec(v_m_1666_);
lean_dec(v_inst_1665_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKeyD___redArg(lean_object* v_x_1669_, lean_object* v_x_1670_, lean_object* v_m_1671_, lean_object* v_a_1672_, lean_object* v_fallback_1673_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_1669_, v_x_1670_, v_m_1671_, v_a_1672_, v_fallback_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKeyD___redArg___boxed(lean_object* v_x_1675_, lean_object* v_x_1676_, lean_object* v_m_1677_, lean_object* v_a_1678_, lean_object* v_fallback_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Std_ExtDHashMap_getKeyD___redArg(v_x_1675_, v_x_1676_, v_m_1677_, v_a_1678_, v_fallback_1679_);
lean_dec(v_fallback_1679_);
lean_dec(v_m_1677_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKeyD(lean_object* v_00_u03b1_1681_, lean_object* v_00_u03b2_1682_, lean_object* v_x_1683_, lean_object* v_x_1684_, lean_object* v_inst_1685_, lean_object* v_inst_1686_, lean_object* v_m_1687_, lean_object* v_a_1688_, lean_object* v_fallback_1689_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_1683_, v_x_1684_, v_m_1687_, v_a_1688_, v_fallback_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKeyD___boxed(lean_object* v_00_u03b1_1691_, lean_object* v_00_u03b2_1692_, lean_object* v_x_1693_, lean_object* v_x_1694_, lean_object* v_inst_1695_, lean_object* v_inst_1696_, lean_object* v_m_1697_, lean_object* v_a_1698_, lean_object* v_fallback_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Std_ExtDHashMap_getKeyD(v_00_u03b1_1691_, v_00_u03b2_1692_, v_x_1693_, v_x_1694_, v_inst_1695_, v_inst_1696_, v_m_1697_, v_a_1698_, v_fallback_1699_);
lean_dec(v_fallback_1699_);
lean_dec(v_m_1697_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_size___redArg(lean_object* v_m_1701_){
_start:
{
lean_object* v_size_1702_; 
v_size_1702_ = lean_ctor_get(v_m_1701_, 0);
lean_inc(v_size_1702_);
return v_size_1702_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_size___redArg___boxed(lean_object* v_m_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Std_ExtDHashMap_size___redArg(v_m_1703_);
lean_dec(v_m_1703_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_size(lean_object* v_00_u03b1_1705_, lean_object* v_00_u03b2_1706_, lean_object* v_x_1707_, lean_object* v_x_1708_, lean_object* v_inst_1709_, lean_object* v_inst_1710_, lean_object* v_m_1711_){
_start:
{
lean_object* v_size_1712_; 
v_size_1712_ = lean_ctor_get(v_m_1711_, 0);
lean_inc(v_size_1712_);
return v_size_1712_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_size___boxed(lean_object* v_00_u03b1_1713_, lean_object* v_00_u03b2_1714_, lean_object* v_x_1715_, lean_object* v_x_1716_, lean_object* v_inst_1717_, lean_object* v_inst_1718_, lean_object* v_m_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Std_ExtDHashMap_size(v_00_u03b1_1713_, v_00_u03b2_1714_, v_x_1715_, v_x_1716_, v_inst_1717_, v_inst_1718_, v_m_1719_);
lean_dec(v_m_1719_);
lean_dec_ref(v_x_1716_);
lean_dec_ref(v_x_1715_);
return v_res_1720_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_isEmpty___redArg(lean_object* v_m_1721_){
_start:
{
lean_object* v_size_1722_; lean_object* v___x_1723_; uint8_t v___x_1724_; 
v_size_1722_ = lean_ctor_get(v_m_1721_, 0);
v___x_1723_ = lean_unsigned_to_nat(0u);
v___x_1724_ = lean_nat_dec_eq(v_size_1722_, v___x_1723_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_isEmpty___redArg___boxed(lean_object* v_m_1725_){
_start:
{
uint8_t v_res_1726_; lean_object* v_r_1727_; 
v_res_1726_ = l_Std_ExtDHashMap_isEmpty___redArg(v_m_1725_);
lean_dec(v_m_1725_);
v_r_1727_ = lean_box(v_res_1726_);
return v_r_1727_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_isEmpty(lean_object* v_00_u03b1_1728_, lean_object* v_00_u03b2_1729_, lean_object* v_x_1730_, lean_object* v_x_1731_, lean_object* v_inst_1732_, lean_object* v_inst_1733_, lean_object* v_m_1734_){
_start:
{
lean_object* v_size_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; 
v_size_1735_ = lean_ctor_get(v_m_1734_, 0);
v___x_1736_ = lean_unsigned_to_nat(0u);
v___x_1737_ = lean_nat_dec_eq(v_size_1735_, v___x_1736_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_isEmpty___boxed(lean_object* v_00_u03b1_1738_, lean_object* v_00_u03b2_1739_, lean_object* v_x_1740_, lean_object* v_x_1741_, lean_object* v_inst_1742_, lean_object* v_inst_1743_, lean_object* v_m_1744_){
_start:
{
uint8_t v_res_1745_; lean_object* v_r_1746_; 
v_res_1745_ = l_Std_ExtDHashMap_isEmpty(v_00_u03b1_1738_, v_00_u03b2_1739_, v_x_1740_, v_x_1741_, v_inst_1742_, v_inst_1743_, v_m_1744_);
lean_dec(v_m_1744_);
lean_dec_ref(v_x_1741_);
lean_dec_ref(v_x_1740_);
v_r_1746_ = lean_box(v_res_1745_);
return v_r_1746_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filter___redArg(lean_object* v_f_1747_, lean_object* v_m_1748_){
_start:
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1747_, v_m_1748_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filter___redArg___boxed(lean_object* v_f_1750_, lean_object* v_m_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Std_ExtDHashMap_filter___redArg(v_f_1750_, v_m_1751_);
lean_dec(v_m_1751_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filter(lean_object* v_00_u03b1_1753_, lean_object* v_00_u03b2_1754_, lean_object* v_x_1755_, lean_object* v_x_1756_, lean_object* v_inst_1757_, lean_object* v_inst_1758_, lean_object* v_f_1759_, lean_object* v_m_1760_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1759_, v_m_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filter___boxed(lean_object* v_00_u03b1_1762_, lean_object* v_00_u03b2_1763_, lean_object* v_x_1764_, lean_object* v_x_1765_, lean_object* v_inst_1766_, lean_object* v_inst_1767_, lean_object* v_f_1768_, lean_object* v_m_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Std_ExtDHashMap_filter(v_00_u03b1_1762_, v_00_u03b2_1763_, v_x_1764_, v_x_1765_, v_inst_1766_, v_inst_1767_, v_f_1768_, v_m_1769_);
lean_dec(v_m_1769_);
lean_dec_ref(v_x_1765_);
lean_dec_ref(v_x_1764_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_map___redArg(lean_object* v_f_1771_, lean_object* v_m_1772_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1771_, v_m_1772_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_map___redArg___boxed(lean_object* v_f_1774_, lean_object* v_m_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Std_ExtDHashMap_map___redArg(v_f_1774_, v_m_1775_);
lean_dec(v_m_1775_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_map(lean_object* v_00_u03b1_1777_, lean_object* v_00_u03b2_1778_, lean_object* v_00_u03b3_1779_, lean_object* v_x_1780_, lean_object* v_x_1781_, lean_object* v_inst_1782_, lean_object* v_inst_1783_, lean_object* v_f_1784_, lean_object* v_m_1785_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1784_, v_m_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_map___boxed(lean_object* v_00_u03b1_1787_, lean_object* v_00_u03b2_1788_, lean_object* v_00_u03b3_1789_, lean_object* v_x_1790_, lean_object* v_x_1791_, lean_object* v_inst_1792_, lean_object* v_inst_1793_, lean_object* v_f_1794_, lean_object* v_m_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Std_ExtDHashMap_map(v_00_u03b1_1787_, v_00_u03b2_1788_, v_00_u03b3_1789_, v_x_1790_, v_x_1791_, v_inst_1792_, v_inst_1793_, v_f_1794_, v_m_1795_);
lean_dec(v_m_1795_);
lean_dec_ref(v_x_1791_);
lean_dec_ref(v_x_1790_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filterMap___redArg(lean_object* v_f_1797_, lean_object* v_m_1798_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1797_, v_m_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filterMap___redArg___boxed(lean_object* v_f_1800_, lean_object* v_m_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l_Std_ExtDHashMap_filterMap___redArg(v_f_1800_, v_m_1801_);
lean_dec(v_m_1801_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filterMap(lean_object* v_00_u03b1_1803_, lean_object* v_00_u03b2_1804_, lean_object* v_00_u03b3_1805_, lean_object* v_x_1806_, lean_object* v_x_1807_, lean_object* v_inst_1808_, lean_object* v_inst_1809_, lean_object* v_f_1810_, lean_object* v_m_1811_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1810_, v_m_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filterMap___boxed(lean_object* v_00_u03b1_1813_, lean_object* v_00_u03b2_1814_, lean_object* v_00_u03b3_1815_, lean_object* v_x_1816_, lean_object* v_x_1817_, lean_object* v_inst_1818_, lean_object* v_inst_1819_, lean_object* v_f_1820_, lean_object* v_m_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Std_ExtDHashMap_filterMap(v_00_u03b1_1813_, v_00_u03b2_1814_, v_00_u03b3_1815_, v_x_1816_, v_x_1817_, v_inst_1818_, v_inst_1819_, v_f_1820_, v_m_1821_);
lean_dec(v_m_1821_);
lean_dec_ref(v_x_1817_);
lean_dec_ref(v_x_1816_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_modify___redArg(lean_object* v_x_1823_, lean_object* v_x_1824_, lean_object* v_m_1825_, lean_object* v_a_1826_, lean_object* v_f_1827_){
_start:
{
lean_object* v___x_1828_; 
lean_inc(v_a_1826_);
v___x_1828_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1823_, v_x_1824_, v_m_1825_, v_a_1826_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_index_1829_; lean_object* v_value_1830_; lean_object* v_size_1831_; lean_object* v_v_x27_1832_; lean_object* v___x_1833_; 
v_index_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_index_1829_);
v_value_1830_ = lean_ctor_get(v___x_1828_, 2);
lean_inc(v_value_1830_);
lean_dec_ref_known(v___x_1828_, 3);
v_size_1831_ = lean_ctor_get(v_m_1825_, 0);
lean_inc(v_size_1831_);
v_v_x27_1832_ = lean_apply_1(v_f_1827_, v_value_1830_);
v___x_1833_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1825_, v_size_1831_, v_index_1829_, v_a_1826_, v_v_x27_1832_);
lean_dec(v_index_1829_);
return v___x_1833_;
}
else
{
lean_dec(v___x_1828_);
lean_dec(v_f_1827_);
lean_dec(v_a_1826_);
return v_m_1825_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_modify(lean_object* v_00_u03b1_1834_, lean_object* v_00_u03b2_1835_, lean_object* v_x_1836_, lean_object* v_x_1837_, lean_object* v_inst_1838_, lean_object* v_m_1839_, lean_object* v_a_1840_, lean_object* v_f_1841_){
_start:
{
lean_object* v___x_1842_; 
lean_inc(v_a_1840_);
v___x_1842_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1836_, v_x_1837_, v_m_1839_, v_a_1840_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_index_1843_; lean_object* v_value_1844_; lean_object* v_size_1845_; lean_object* v_v_x27_1846_; lean_object* v___x_1847_; 
v_index_1843_ = lean_ctor_get(v___x_1842_, 0);
lean_inc(v_index_1843_);
v_value_1844_ = lean_ctor_get(v___x_1842_, 2);
lean_inc(v_value_1844_);
lean_dec_ref_known(v___x_1842_, 3);
v_size_1845_ = lean_ctor_get(v_m_1839_, 0);
lean_inc(v_size_1845_);
v_v_x27_1846_ = lean_apply_1(v_f_1841_, v_value_1844_);
v___x_1847_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1839_, v_size_1845_, v_index_1843_, v_a_1840_, v_v_x27_1846_);
lean_dec(v_index_1843_);
return v___x_1847_;
}
else
{
lean_dec(v___x_1842_);
lean_dec(v_f_1841_);
lean_dec(v_a_1840_);
return v_m_1839_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_modify___redArg(lean_object* v_x_1848_, lean_object* v_x_1849_, lean_object* v_m_1850_, lean_object* v_a_1851_, lean_object* v_f_1852_){
_start:
{
lean_object* v___x_1853_; 
lean_inc(v_a_1851_);
v___x_1853_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1848_, v_x_1849_, v_m_1850_, v_a_1851_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_index_1854_; lean_object* v_value_1855_; lean_object* v_size_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v_index_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_index_1854_);
v_value_1855_ = lean_ctor_get(v___x_1853_, 2);
lean_inc(v_value_1855_);
lean_dec_ref_known(v___x_1853_, 3);
v_size_1856_ = lean_ctor_get(v_m_1850_, 0);
lean_inc(v_size_1856_);
v___x_1857_ = lean_apply_1(v_f_1852_, v_value_1855_);
v___x_1858_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1850_, v_size_1856_, v_index_1854_, v_a_1851_, v___x_1857_);
lean_dec(v_index_1854_);
return v___x_1858_;
}
else
{
lean_dec(v___x_1853_);
lean_dec(v_f_1852_);
lean_dec(v_a_1851_);
return v_m_1850_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_modify(lean_object* v_00_u03b1_1859_, lean_object* v_x_1860_, lean_object* v_x_1861_, lean_object* v_inst_1862_, lean_object* v_inst_1863_, lean_object* v_00_u03b2_1864_, lean_object* v_m_1865_, lean_object* v_a_1866_, lean_object* v_f_1867_){
_start:
{
lean_object* v___x_1868_; 
lean_inc(v_a_1866_);
v___x_1868_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1860_, v_x_1861_, v_m_1865_, v_a_1866_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_index_1869_; lean_object* v_value_1870_; lean_object* v_size_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v_index_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_index_1869_);
v_value_1870_ = lean_ctor_get(v___x_1868_, 2);
lean_inc(v_value_1870_);
lean_dec_ref_known(v___x_1868_, 3);
v_size_1871_ = lean_ctor_get(v_m_1865_, 0);
lean_inc(v_size_1871_);
v___x_1872_ = lean_apply_1(v_f_1867_, v_value_1870_);
v___x_1873_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1865_, v_size_1871_, v_index_1869_, v_a_1866_, v___x_1872_);
lean_dec(v_index_1869_);
return v___x_1873_;
}
else
{
lean_dec(v___x_1868_);
lean_dec(v_f_1867_);
lean_dec(v_a_1866_);
return v_m_1865_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_alter___redArg(lean_object* v_x_1874_, lean_object* v_x_1875_, lean_object* v_m_1876_, lean_object* v_a_1877_, lean_object* v_f_1878_){
_start:
{
lean_object* v___x_1879_; 
lean_inc(v_a_1877_);
lean_inc_ref(v_x_1875_);
lean_inc_ref(v_x_1874_);
v___x_1879_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1874_, v_x_1875_, v_m_1876_, v_a_1877_);
switch(lean_obj_tag(v___x_1879_))
{
case 0:
{
lean_object* v_index_1880_; lean_object* v_value_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
lean_dec_ref(v_x_1875_);
lean_dec_ref(v_x_1874_);
v_index_1880_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_index_1880_);
v_value_1881_ = lean_ctor_get(v___x_1879_, 2);
lean_inc(v_value_1881_);
lean_dec_ref_known(v___x_1879_, 3);
v___x_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1882_, 0, v_value_1881_);
v___x_1883_ = lean_apply_1(v_f_1878_, v___x_1882_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_size_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
lean_dec(v_a_1877_);
v_size_1884_ = lean_ctor_get(v_m_1876_, 0);
v___x_1885_ = lean_unsigned_to_nat(1u);
v___x_1886_ = lean_nat_sub(v_size_1884_, v___x_1885_);
v___x_1887_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_1876_, v___x_1886_, v_index_1880_);
lean_dec(v_index_1880_);
return v___x_1887_;
}
else
{
lean_object* v_val_1888_; lean_object* v_size_1889_; lean_object* v___x_1890_; 
v_val_1888_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_val_1888_);
lean_dec_ref_known(v___x_1883_, 1);
v_size_1889_ = lean_ctor_get(v_m_1876_, 0);
lean_inc(v_size_1889_);
v___x_1890_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1876_, v_size_1889_, v_index_1880_, v_a_1877_, v_val_1888_);
lean_dec(v_index_1880_);
return v___x_1890_;
}
}
case 1:
{
lean_object* v_index_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v_index_1891_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_index_1891_);
lean_dec_ref_known(v___x_1879_, 1);
v___x_1892_ = lean_box(0);
v___x_1893_ = lean_apply_1(v_f_1878_, v___x_1892_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_dec(v_index_1891_);
lean_dec(v_a_1877_);
lean_dec_ref(v_x_1875_);
lean_dec_ref(v_x_1874_);
return v_m_1876_;
}
else
{
lean_object* v_val_1894_; lean_object* v___y_1896_; lean_object* v_i_1897_; lean_object* v_size_1912_; lean_object* v_keyArray_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; uint8_t v___x_1917_; 
v_val_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc(v_val_1894_);
lean_dec_ref_known(v___x_1893_, 1);
v_size_1912_ = lean_ctor_get(v_m_1876_, 0);
v_keyArray_1913_ = lean_ctor_get(v_m_1876_, 1);
v___x_1914_ = lean_unsigned_to_nat(1u);
v___x_1915_ = lean_nat_add(v_size_1912_, v___x_1914_);
v___x_1916_ = lean_array_get_size(v_keyArray_1913_);
v___x_1917_ = lean_nat_dec_lt(v___x_1915_, v___x_1916_);
if (v___x_1917_ == 0)
{
lean_dec(v___x_1915_);
lean_dec(v_index_1891_);
goto v___jp_1902_;
}
else
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; uint8_t v___x_1922_; 
v___x_1918_ = lean_unsigned_to_nat(4u);
v___x_1919_ = lean_nat_mul(v___x_1915_, v___x_1918_);
v___x_1920_ = lean_unsigned_to_nat(3u);
v___x_1921_ = lean_nat_mul(v___x_1916_, v___x_1920_);
v___x_1922_ = lean_nat_dec_le(v___x_1919_, v___x_1921_);
lean_dec(v___x_1921_);
lean_dec(v___x_1919_);
if (v___x_1922_ == 0)
{
lean_dec(v___x_1915_);
lean_dec(v_index_1891_);
goto v___jp_1902_;
}
else
{
lean_object* v___x_1923_; 
lean_dec_ref(v_x_1875_);
lean_dec_ref(v_x_1874_);
v___x_1923_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1876_, v___x_1915_, v_index_1891_, v_a_1877_, v_val_1894_);
lean_dec(v_index_1891_);
return v___x_1923_;
}
}
v___jp_1895_:
{
lean_object* v_size_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v_size_1898_ = lean_ctor_get(v___y_1896_, 0);
v___x_1899_ = lean_unsigned_to_nat(1u);
v___x_1900_ = lean_nat_add(v_size_1898_, v___x_1899_);
v___x_1901_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1896_, v___x_1900_, v_i_1897_, v_a_1877_, v_val_1894_);
lean_dec(v_i_1897_);
return v___x_1901_;
}
v___jp_1902_:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
lean_inc_ref(v_x_1875_);
lean_inc_ref(v_x_1874_);
v___x_1903_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1874_, v_x_1875_, v_m_1876_);
lean_inc(v_a_1877_);
v___x_1904_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1874_, v_x_1875_, v___x_1903_, v_a_1877_);
switch(lean_obj_tag(v___x_1904_))
{
case 0:
{
lean_object* v_index_1905_; lean_object* v_size_1906_; lean_object* v___x_1907_; 
v_index_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_index_1905_);
lean_dec_ref_known(v___x_1904_, 3);
v_size_1906_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_size_1906_);
v___x_1907_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1903_, v_size_1906_, v_index_1905_, v_a_1877_, v_val_1894_);
lean_dec(v_index_1905_);
return v___x_1907_;
}
case 1:
{
lean_object* v_index_1908_; 
v_index_1908_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_index_1908_);
lean_dec_ref_known(v___x_1904_, 1);
v___y_1896_ = v___x_1903_;
v_i_1897_ = v_index_1908_;
goto v___jp_1895_;
}
default: 
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = lean_unsigned_to_nat(0u);
v___x_1910_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1903_, v___x_1909_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_index_1911_; 
v_index_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_index_1911_);
lean_dec_ref_known(v___x_1910_, 1);
v___y_1896_ = v___x_1903_;
v_i_1897_ = v_index_1911_;
goto v___jp_1895_;
}
else
{
lean_dec(v_val_1894_);
lean_dec(v_a_1877_);
return v___x_1903_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = lean_box(0);
v___x_1925_ = lean_apply_1(v_f_1878_, v___x_1924_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_dec(v_a_1877_);
lean_dec_ref(v_x_1875_);
lean_dec_ref(v_x_1874_);
return v_m_1876_;
}
else
{
lean_object* v_val_1926_; lean_object* v___y_1928_; lean_object* v_i_1929_; lean_object* v___y_1935_; lean_object* v_size_1944_; lean_object* v_keyArray_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; uint8_t v___x_1949_; 
v_val_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_val_1926_);
lean_dec_ref_known(v___x_1925_, 1);
v_size_1944_ = lean_ctor_get(v_m_1876_, 0);
v_keyArray_1945_ = lean_ctor_get(v_m_1876_, 1);
v___x_1946_ = lean_unsigned_to_nat(1u);
v___x_1947_ = lean_nat_add(v_size_1944_, v___x_1946_);
v___x_1948_ = lean_array_get_size(v_keyArray_1945_);
v___x_1949_ = lean_nat_dec_lt(v___x_1947_, v___x_1948_);
if (v___x_1949_ == 0)
{
lean_object* v___x_1950_; 
lean_dec(v___x_1947_);
lean_inc_ref(v_x_1875_);
lean_inc_ref(v_x_1874_);
v___x_1950_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1874_, v_x_1875_, v_m_1876_);
v___y_1935_ = v___x_1950_;
goto v___jp_1934_;
}
else
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; uint8_t v___x_1955_; 
v___x_1951_ = lean_unsigned_to_nat(4u);
v___x_1952_ = lean_nat_mul(v___x_1947_, v___x_1951_);
lean_dec(v___x_1947_);
v___x_1953_ = lean_unsigned_to_nat(3u);
v___x_1954_ = lean_nat_mul(v___x_1948_, v___x_1953_);
v___x_1955_ = lean_nat_dec_le(v___x_1952_, v___x_1954_);
lean_dec(v___x_1954_);
lean_dec(v___x_1952_);
if (v___x_1955_ == 0)
{
lean_object* v___x_1956_; 
lean_inc_ref(v_x_1875_);
lean_inc_ref(v_x_1874_);
v___x_1956_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1874_, v_x_1875_, v_m_1876_);
v___y_1935_ = v___x_1956_;
goto v___jp_1934_;
}
else
{
v___y_1935_ = v_m_1876_;
goto v___jp_1934_;
}
}
v___jp_1927_:
{
lean_object* v_size_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v_size_1930_ = lean_ctor_get(v___y_1928_, 0);
v___x_1931_ = lean_unsigned_to_nat(1u);
v___x_1932_ = lean_nat_add(v_size_1930_, v___x_1931_);
v___x_1933_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1928_, v___x_1932_, v_i_1929_, v_a_1877_, v_val_1926_);
lean_dec(v_i_1929_);
return v___x_1933_;
}
v___jp_1934_:
{
lean_object* v___x_1936_; 
lean_inc(v_a_1877_);
v___x_1936_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1874_, v_x_1875_, v___y_1935_, v_a_1877_);
switch(lean_obj_tag(v___x_1936_))
{
case 0:
{
lean_object* v_index_1937_; lean_object* v_size_1938_; lean_object* v___x_1939_; 
v_index_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_index_1937_);
lean_dec_ref_known(v___x_1936_, 3);
v_size_1938_ = lean_ctor_get(v___y_1935_, 0);
lean_inc(v_size_1938_);
v___x_1939_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1935_, v_size_1938_, v_index_1937_, v_a_1877_, v_val_1926_);
lean_dec(v_index_1937_);
return v___x_1939_;
}
case 1:
{
lean_object* v_index_1940_; 
v_index_1940_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_index_1940_);
lean_dec_ref_known(v___x_1936_, 1);
v___y_1928_ = v___y_1935_;
v_i_1929_ = v_index_1940_;
goto v___jp_1927_;
}
default: 
{
lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1941_ = lean_unsigned_to_nat(0u);
v___x_1942_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1935_, v___x_1941_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_index_1943_; 
v_index_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_index_1943_);
lean_dec_ref_known(v___x_1942_, 1);
v___y_1928_ = v___y_1935_;
v_i_1929_ = v_index_1943_;
goto v___jp_1927_;
}
else
{
lean_dec(v_val_1926_);
lean_dec(v_a_1877_);
return v___y_1935_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_alter(lean_object* v_00_u03b1_1957_, lean_object* v_00_u03b2_1958_, lean_object* v_x_1959_, lean_object* v_x_1960_, lean_object* v_inst_1961_, lean_object* v_m_1962_, lean_object* v_a_1963_, lean_object* v_f_1964_){
_start:
{
lean_object* v___x_1965_; 
lean_inc(v_a_1963_);
lean_inc_ref(v_x_1960_);
lean_inc_ref(v_x_1959_);
v___x_1965_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1959_, v_x_1960_, v_m_1962_, v_a_1963_);
switch(lean_obj_tag(v___x_1965_))
{
case 0:
{
lean_object* v_index_1966_; lean_object* v_value_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
lean_dec_ref(v_x_1960_);
lean_dec_ref(v_x_1959_);
v_index_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_index_1966_);
v_value_1967_ = lean_ctor_get(v___x_1965_, 2);
lean_inc(v_value_1967_);
lean_dec_ref_known(v___x_1965_, 3);
v___x_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1968_, 0, v_value_1967_);
v___x_1969_ = lean_apply_1(v_f_1964_, v___x_1968_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_size_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
lean_dec(v_a_1963_);
v_size_1970_ = lean_ctor_get(v_m_1962_, 0);
v___x_1971_ = lean_unsigned_to_nat(1u);
v___x_1972_ = lean_nat_sub(v_size_1970_, v___x_1971_);
v___x_1973_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_1962_, v___x_1972_, v_index_1966_);
lean_dec(v_index_1966_);
return v___x_1973_;
}
else
{
lean_object* v_val_1974_; lean_object* v_size_1975_; lean_object* v___x_1976_; 
v_val_1974_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_val_1974_);
lean_dec_ref_known(v___x_1969_, 1);
v_size_1975_ = lean_ctor_get(v_m_1962_, 0);
lean_inc(v_size_1975_);
v___x_1976_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1962_, v_size_1975_, v_index_1966_, v_a_1963_, v_val_1974_);
lean_dec(v_index_1966_);
return v___x_1976_;
}
}
case 1:
{
lean_object* v_index_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v_index_1977_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_index_1977_);
lean_dec_ref_known(v___x_1965_, 1);
v___x_1978_ = lean_box(0);
v___x_1979_ = lean_apply_1(v_f_1964_, v___x_1978_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_dec(v_index_1977_);
lean_dec(v_a_1963_);
lean_dec_ref(v_x_1960_);
lean_dec_ref(v_x_1959_);
return v_m_1962_;
}
else
{
lean_object* v_val_1980_; lean_object* v___y_1982_; lean_object* v_i_1983_; lean_object* v_size_1998_; lean_object* v_keyArray_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; 
v_val_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_val_1980_);
lean_dec_ref_known(v___x_1979_, 1);
v_size_1998_ = lean_ctor_get(v_m_1962_, 0);
v_keyArray_1999_ = lean_ctor_get(v_m_1962_, 1);
v___x_2000_ = lean_unsigned_to_nat(1u);
v___x_2001_ = lean_nat_add(v_size_1998_, v___x_2000_);
v___x_2002_ = lean_array_get_size(v_keyArray_1999_);
v___x_2003_ = lean_nat_dec_lt(v___x_2001_, v___x_2002_);
if (v___x_2003_ == 0)
{
lean_dec(v___x_2001_);
lean_dec(v_index_1977_);
goto v___jp_1988_;
}
else
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; uint8_t v___x_2008_; 
v___x_2004_ = lean_unsigned_to_nat(4u);
v___x_2005_ = lean_nat_mul(v___x_2001_, v___x_2004_);
v___x_2006_ = lean_unsigned_to_nat(3u);
v___x_2007_ = lean_nat_mul(v___x_2002_, v___x_2006_);
v___x_2008_ = lean_nat_dec_le(v___x_2005_, v___x_2007_);
lean_dec(v___x_2007_);
lean_dec(v___x_2005_);
if (v___x_2008_ == 0)
{
lean_dec(v___x_2001_);
lean_dec(v_index_1977_);
goto v___jp_1988_;
}
else
{
lean_object* v___x_2009_; 
lean_dec_ref(v_x_1960_);
lean_dec_ref(v_x_1959_);
v___x_2009_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1962_, v___x_2001_, v_index_1977_, v_a_1963_, v_val_1980_);
lean_dec(v_index_1977_);
return v___x_2009_;
}
}
v___jp_1981_:
{
lean_object* v_size_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v_size_1984_ = lean_ctor_get(v___y_1982_, 0);
v___x_1985_ = lean_unsigned_to_nat(1u);
v___x_1986_ = lean_nat_add(v_size_1984_, v___x_1985_);
v___x_1987_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1982_, v___x_1986_, v_i_1983_, v_a_1963_, v_val_1980_);
lean_dec(v_i_1983_);
return v___x_1987_;
}
v___jp_1988_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
lean_inc_ref(v_x_1960_);
lean_inc_ref(v_x_1959_);
v___x_1989_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1959_, v_x_1960_, v_m_1962_);
lean_inc(v_a_1963_);
v___x_1990_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1959_, v_x_1960_, v___x_1989_, v_a_1963_);
switch(lean_obj_tag(v___x_1990_))
{
case 0:
{
lean_object* v_index_1991_; lean_object* v_size_1992_; lean_object* v___x_1993_; 
v_index_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_index_1991_);
lean_dec_ref_known(v___x_1990_, 3);
v_size_1992_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_size_1992_);
v___x_1993_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1989_, v_size_1992_, v_index_1991_, v_a_1963_, v_val_1980_);
lean_dec(v_index_1991_);
return v___x_1993_;
}
case 1:
{
lean_object* v_index_1994_; 
v_index_1994_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_index_1994_);
lean_dec_ref_known(v___x_1990_, 1);
v___y_1982_ = v___x_1989_;
v_i_1983_ = v_index_1994_;
goto v___jp_1981_;
}
default: 
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1995_ = lean_unsigned_to_nat(0u);
v___x_1996_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1989_, v___x_1995_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_index_1997_; 
v_index_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_index_1997_);
lean_dec_ref_known(v___x_1996_, 1);
v___y_1982_ = v___x_1989_;
v_i_1983_ = v_index_1997_;
goto v___jp_1981_;
}
else
{
lean_dec(v_val_1980_);
lean_dec(v_a_1963_);
return v___x_1989_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = lean_box(0);
v___x_2011_ = lean_apply_1(v_f_1964_, v___x_2010_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_dec(v_a_1963_);
lean_dec_ref(v_x_1960_);
lean_dec_ref(v_x_1959_);
return v_m_1962_;
}
else
{
lean_object* v_val_2012_; lean_object* v___y_2014_; lean_object* v_i_2015_; lean_object* v___y_2021_; lean_object* v_size_2030_; lean_object* v_keyArray_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; 
v_val_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_val_2012_);
lean_dec_ref_known(v___x_2011_, 1);
v_size_2030_ = lean_ctor_get(v_m_1962_, 0);
v_keyArray_2031_ = lean_ctor_get(v_m_1962_, 1);
v___x_2032_ = lean_unsigned_to_nat(1u);
v___x_2033_ = lean_nat_add(v_size_2030_, v___x_2032_);
v___x_2034_ = lean_array_get_size(v_keyArray_2031_);
v___x_2035_ = lean_nat_dec_lt(v___x_2033_, v___x_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; 
lean_dec(v___x_2033_);
lean_inc_ref(v_x_1960_);
lean_inc_ref(v_x_1959_);
v___x_2036_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1959_, v_x_1960_, v_m_1962_);
v___y_2021_ = v___x_2036_;
goto v___jp_2020_;
}
else
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; uint8_t v___x_2041_; 
v___x_2037_ = lean_unsigned_to_nat(4u);
v___x_2038_ = lean_nat_mul(v___x_2033_, v___x_2037_);
lean_dec(v___x_2033_);
v___x_2039_ = lean_unsigned_to_nat(3u);
v___x_2040_ = lean_nat_mul(v___x_2034_, v___x_2039_);
v___x_2041_ = lean_nat_dec_le(v___x_2038_, v___x_2040_);
lean_dec(v___x_2040_);
lean_dec(v___x_2038_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; 
lean_inc_ref(v_x_1960_);
lean_inc_ref(v_x_1959_);
v___x_2042_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1959_, v_x_1960_, v_m_1962_);
v___y_2021_ = v___x_2042_;
goto v___jp_2020_;
}
else
{
v___y_2021_ = v_m_1962_;
goto v___jp_2020_;
}
}
v___jp_2013_:
{
lean_object* v_size_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v_size_2016_ = lean_ctor_get(v___y_2014_, 0);
v___x_2017_ = lean_unsigned_to_nat(1u);
v___x_2018_ = lean_nat_add(v_size_2016_, v___x_2017_);
v___x_2019_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2014_, v___x_2018_, v_i_2015_, v_a_1963_, v_val_2012_);
lean_dec(v_i_2015_);
return v___x_2019_;
}
v___jp_2020_:
{
lean_object* v___x_2022_; 
lean_inc(v_a_1963_);
v___x_2022_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1959_, v_x_1960_, v___y_2021_, v_a_1963_);
switch(lean_obj_tag(v___x_2022_))
{
case 0:
{
lean_object* v_index_2023_; lean_object* v_size_2024_; lean_object* v___x_2025_; 
v_index_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_index_2023_);
lean_dec_ref_known(v___x_2022_, 3);
v_size_2024_ = lean_ctor_get(v___y_2021_, 0);
lean_inc(v_size_2024_);
v___x_2025_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2021_, v_size_2024_, v_index_2023_, v_a_1963_, v_val_2012_);
lean_dec(v_index_2023_);
return v___x_2025_;
}
case 1:
{
lean_object* v_index_2026_; 
v_index_2026_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_index_2026_);
lean_dec_ref_known(v___x_2022_, 1);
v___y_2014_ = v___y_2021_;
v_i_2015_ = v_index_2026_;
goto v___jp_2013_;
}
default: 
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = lean_unsigned_to_nat(0u);
v___x_2028_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2021_, v___x_2027_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_index_2029_; 
v_index_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc(v_index_2029_);
lean_dec_ref_known(v___x_2028_, 1);
v___y_2014_ = v___y_2021_;
v_i_2015_ = v_index_2029_;
goto v___jp_2013_;
}
else
{
lean_dec(v_val_2012_);
lean_dec(v_a_1963_);
return v___y_2021_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_alter___redArg(lean_object* v_x_2043_, lean_object* v_x_2044_, lean_object* v_m_2045_, lean_object* v_a_2046_, lean_object* v_f_2047_){
_start:
{
lean_object* v___x_2048_; 
lean_inc(v_a_2046_);
lean_inc_ref(v_x_2044_);
lean_inc_ref(v_x_2043_);
v___x_2048_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_2043_, v_x_2044_, v_m_2045_, v_a_2046_);
switch(lean_obj_tag(v___x_2048_))
{
case 0:
{
lean_object* v_index_2049_; lean_object* v_value_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
lean_dec_ref(v_x_2044_);
lean_dec_ref(v_x_2043_);
v_index_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_index_2049_);
v_value_2050_ = lean_ctor_get(v___x_2048_, 2);
lean_inc(v_value_2050_);
lean_dec_ref_known(v___x_2048_, 3);
v___x_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2051_, 0, v_value_2050_);
v___x_2052_ = lean_apply_1(v_f_2047_, v___x_2051_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_size_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
lean_dec(v_a_2046_);
v_size_2053_ = lean_ctor_get(v_m_2045_, 0);
v___x_2054_ = lean_unsigned_to_nat(1u);
v___x_2055_ = lean_nat_sub(v_size_2053_, v___x_2054_);
v___x_2056_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_2045_, v___x_2055_, v_index_2049_);
lean_dec(v_index_2049_);
return v___x_2056_;
}
else
{
lean_object* v_val_2057_; lean_object* v_size_2058_; lean_object* v___x_2059_; 
v_val_2057_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_val_2057_);
lean_dec_ref_known(v___x_2052_, 1);
v_size_2058_ = lean_ctor_get(v_m_2045_, 0);
lean_inc(v_size_2058_);
v___x_2059_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_2045_, v_size_2058_, v_index_2049_, v_a_2046_, v_val_2057_);
lean_dec(v_index_2049_);
return v___x_2059_;
}
}
case 1:
{
lean_object* v_index_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v_index_2060_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_index_2060_);
lean_dec_ref_known(v___x_2048_, 1);
v___x_2061_ = lean_box(0);
v___x_2062_ = lean_apply_1(v_f_2047_, v___x_2061_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_dec(v_index_2060_);
lean_dec(v_a_2046_);
lean_dec_ref(v_x_2044_);
lean_dec_ref(v_x_2043_);
return v_m_2045_;
}
else
{
lean_object* v_val_2063_; lean_object* v___y_2065_; lean_object* v_i_2066_; lean_object* v_size_2081_; lean_object* v_keyArray_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; uint8_t v___x_2086_; 
v_val_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_val_2063_);
lean_dec_ref_known(v___x_2062_, 1);
v_size_2081_ = lean_ctor_get(v_m_2045_, 0);
v_keyArray_2082_ = lean_ctor_get(v_m_2045_, 1);
v___x_2083_ = lean_unsigned_to_nat(1u);
v___x_2084_ = lean_nat_add(v_size_2081_, v___x_2083_);
v___x_2085_ = lean_array_get_size(v_keyArray_2082_);
v___x_2086_ = lean_nat_dec_lt(v___x_2084_, v___x_2085_);
if (v___x_2086_ == 0)
{
lean_dec(v___x_2084_);
lean_dec(v_index_2060_);
goto v___jp_2071_;
}
else
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; uint8_t v___x_2091_; 
v___x_2087_ = lean_unsigned_to_nat(4u);
v___x_2088_ = lean_nat_mul(v___x_2084_, v___x_2087_);
v___x_2089_ = lean_unsigned_to_nat(3u);
v___x_2090_ = lean_nat_mul(v___x_2085_, v___x_2089_);
v___x_2091_ = lean_nat_dec_le(v___x_2088_, v___x_2090_);
lean_dec(v___x_2090_);
lean_dec(v___x_2088_);
if (v___x_2091_ == 0)
{
lean_dec(v___x_2084_);
lean_dec(v_index_2060_);
goto v___jp_2071_;
}
else
{
lean_object* v___x_2092_; 
lean_dec_ref(v_x_2044_);
lean_dec_ref(v_x_2043_);
v___x_2092_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_2045_, v___x_2084_, v_index_2060_, v_a_2046_, v_val_2063_);
lean_dec(v_index_2060_);
return v___x_2092_;
}
}
v___jp_2064_:
{
lean_object* v_size_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v_size_2067_ = lean_ctor_get(v___y_2065_, 0);
v___x_2068_ = lean_unsigned_to_nat(1u);
v___x_2069_ = lean_nat_add(v_size_2067_, v___x_2068_);
v___x_2070_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2065_, v___x_2069_, v_i_2066_, v_a_2046_, v_val_2063_);
lean_dec(v_i_2066_);
return v___x_2070_;
}
v___jp_2071_:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
lean_inc_ref(v_x_2044_);
lean_inc_ref(v_x_2043_);
v___x_2072_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_2043_, v_x_2044_, v_m_2045_);
lean_inc(v_a_2046_);
v___x_2073_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_2043_, v_x_2044_, v___x_2072_, v_a_2046_);
switch(lean_obj_tag(v___x_2073_))
{
case 0:
{
lean_object* v_index_2074_; lean_object* v_size_2075_; lean_object* v___x_2076_; 
v_index_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_index_2074_);
lean_dec_ref_known(v___x_2073_, 3);
v_size_2075_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_size_2075_);
v___x_2076_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2072_, v_size_2075_, v_index_2074_, v_a_2046_, v_val_2063_);
lean_dec(v_index_2074_);
return v___x_2076_;
}
case 1:
{
lean_object* v_index_2077_; 
v_index_2077_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_index_2077_);
lean_dec_ref_known(v___x_2073_, 1);
v___y_2065_ = v___x_2072_;
v_i_2066_ = v_index_2077_;
goto v___jp_2064_;
}
default: 
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = lean_unsigned_to_nat(0u);
v___x_2079_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2072_, v___x_2078_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_index_2080_; 
v_index_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_index_2080_);
lean_dec_ref_known(v___x_2079_, 1);
v___y_2065_ = v___x_2072_;
v_i_2066_ = v_index_2080_;
goto v___jp_2064_;
}
else
{
lean_dec(v_val_2063_);
lean_dec(v_a_2046_);
return v___x_2072_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = lean_box(0);
v___x_2094_ = lean_apply_1(v_f_2047_, v___x_2093_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_dec(v_a_2046_);
lean_dec_ref(v_x_2044_);
lean_dec_ref(v_x_2043_);
return v_m_2045_;
}
else
{
lean_object* v_val_2095_; lean_object* v___y_2097_; lean_object* v_i_2098_; lean_object* v___y_2104_; lean_object* v_size_2113_; lean_object* v_keyArray_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; uint8_t v___x_2118_; 
v_val_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_val_2095_);
lean_dec_ref_known(v___x_2094_, 1);
v_size_2113_ = lean_ctor_get(v_m_2045_, 0);
v_keyArray_2114_ = lean_ctor_get(v_m_2045_, 1);
v___x_2115_ = lean_unsigned_to_nat(1u);
v___x_2116_ = lean_nat_add(v_size_2113_, v___x_2115_);
v___x_2117_ = lean_array_get_size(v_keyArray_2114_);
v___x_2118_ = lean_nat_dec_lt(v___x_2116_, v___x_2117_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; 
lean_dec(v___x_2116_);
lean_inc_ref(v_x_2044_);
lean_inc_ref(v_x_2043_);
v___x_2119_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_2043_, v_x_2044_, v_m_2045_);
v___y_2104_ = v___x_2119_;
goto v___jp_2103_;
}
else
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; uint8_t v___x_2124_; 
v___x_2120_ = lean_unsigned_to_nat(4u);
v___x_2121_ = lean_nat_mul(v___x_2116_, v___x_2120_);
lean_dec(v___x_2116_);
v___x_2122_ = lean_unsigned_to_nat(3u);
v___x_2123_ = lean_nat_mul(v___x_2117_, v___x_2122_);
v___x_2124_ = lean_nat_dec_le(v___x_2121_, v___x_2123_);
lean_dec(v___x_2123_);
lean_dec(v___x_2121_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; 
lean_inc_ref(v_x_2044_);
lean_inc_ref(v_x_2043_);
v___x_2125_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_2043_, v_x_2044_, v_m_2045_);
v___y_2104_ = v___x_2125_;
goto v___jp_2103_;
}
else
{
v___y_2104_ = v_m_2045_;
goto v___jp_2103_;
}
}
v___jp_2096_:
{
lean_object* v_size_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v_size_2099_ = lean_ctor_get(v___y_2097_, 0);
v___x_2100_ = lean_unsigned_to_nat(1u);
v___x_2101_ = lean_nat_add(v_size_2099_, v___x_2100_);
v___x_2102_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2097_, v___x_2101_, v_i_2098_, v_a_2046_, v_val_2095_);
lean_dec(v_i_2098_);
return v___x_2102_;
}
v___jp_2103_:
{
lean_object* v___x_2105_; 
lean_inc(v_a_2046_);
v___x_2105_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_2043_, v_x_2044_, v___y_2104_, v_a_2046_);
switch(lean_obj_tag(v___x_2105_))
{
case 0:
{
lean_object* v_index_2106_; lean_object* v_size_2107_; lean_object* v___x_2108_; 
v_index_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_index_2106_);
lean_dec_ref_known(v___x_2105_, 3);
v_size_2107_ = lean_ctor_get(v___y_2104_, 0);
lean_inc(v_size_2107_);
v___x_2108_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2104_, v_size_2107_, v_index_2106_, v_a_2046_, v_val_2095_);
lean_dec(v_index_2106_);
return v___x_2108_;
}
case 1:
{
lean_object* v_index_2109_; 
v_index_2109_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_index_2109_);
lean_dec_ref_known(v___x_2105_, 1);
v___y_2097_ = v___y_2104_;
v_i_2098_ = v_index_2109_;
goto v___jp_2096_;
}
default: 
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = lean_unsigned_to_nat(0u);
v___x_2111_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2104_, v___x_2110_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_index_2112_; 
v_index_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_index_2112_);
lean_dec_ref_known(v___x_2111_, 1);
v___y_2097_ = v___y_2104_;
v_i_2098_ = v_index_2112_;
goto v___jp_2096_;
}
else
{
lean_dec(v_val_2095_);
lean_dec(v_a_2046_);
return v___y_2104_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_alter(lean_object* v_00_u03b1_2126_, lean_object* v_x_2127_, lean_object* v_x_2128_, lean_object* v_inst_2129_, lean_object* v_inst_2130_, lean_object* v_00_u03b2_2131_, lean_object* v_m_2132_, lean_object* v_a_2133_, lean_object* v_f_2134_){
_start:
{
lean_object* v___x_2135_; 
lean_inc(v_a_2133_);
lean_inc_ref(v_x_2128_);
lean_inc_ref(v_x_2127_);
v___x_2135_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_2127_, v_x_2128_, v_m_2132_, v_a_2133_);
switch(lean_obj_tag(v___x_2135_))
{
case 0:
{
lean_object* v_index_2136_; lean_object* v_value_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
lean_dec_ref(v_x_2128_);
lean_dec_ref(v_x_2127_);
v_index_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_index_2136_);
v_value_2137_ = lean_ctor_get(v___x_2135_, 2);
lean_inc(v_value_2137_);
lean_dec_ref_known(v___x_2135_, 3);
v___x_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2138_, 0, v_value_2137_);
v___x_2139_ = lean_apply_1(v_f_2134_, v___x_2138_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_size_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
lean_dec(v_a_2133_);
v_size_2140_ = lean_ctor_get(v_m_2132_, 0);
v___x_2141_ = lean_unsigned_to_nat(1u);
v___x_2142_ = lean_nat_sub(v_size_2140_, v___x_2141_);
v___x_2143_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_2132_, v___x_2142_, v_index_2136_);
lean_dec(v_index_2136_);
return v___x_2143_;
}
else
{
lean_object* v_val_2144_; lean_object* v_size_2145_; lean_object* v___x_2146_; 
v_val_2144_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_val_2144_);
lean_dec_ref_known(v___x_2139_, 1);
v_size_2145_ = lean_ctor_get(v_m_2132_, 0);
lean_inc(v_size_2145_);
v___x_2146_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_2132_, v_size_2145_, v_index_2136_, v_a_2133_, v_val_2144_);
lean_dec(v_index_2136_);
return v___x_2146_;
}
}
case 1:
{
lean_object* v_index_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v_index_2147_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_index_2147_);
lean_dec_ref_known(v___x_2135_, 1);
v___x_2148_ = lean_box(0);
v___x_2149_ = lean_apply_1(v_f_2134_, v___x_2148_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_dec(v_index_2147_);
lean_dec(v_a_2133_);
lean_dec_ref(v_x_2128_);
lean_dec_ref(v_x_2127_);
return v_m_2132_;
}
else
{
lean_object* v_val_2150_; lean_object* v___y_2152_; lean_object* v_i_2153_; lean_object* v_size_2168_; lean_object* v_keyArray_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; 
v_val_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_val_2150_);
lean_dec_ref_known(v___x_2149_, 1);
v_size_2168_ = lean_ctor_get(v_m_2132_, 0);
v_keyArray_2169_ = lean_ctor_get(v_m_2132_, 1);
v___x_2170_ = lean_unsigned_to_nat(1u);
v___x_2171_ = lean_nat_add(v_size_2168_, v___x_2170_);
v___x_2172_ = lean_array_get_size(v_keyArray_2169_);
v___x_2173_ = lean_nat_dec_lt(v___x_2171_, v___x_2172_);
if (v___x_2173_ == 0)
{
lean_dec(v___x_2171_);
lean_dec(v_index_2147_);
goto v___jp_2158_;
}
else
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; uint8_t v___x_2178_; 
v___x_2174_ = lean_unsigned_to_nat(4u);
v___x_2175_ = lean_nat_mul(v___x_2171_, v___x_2174_);
v___x_2176_ = lean_unsigned_to_nat(3u);
v___x_2177_ = lean_nat_mul(v___x_2172_, v___x_2176_);
v___x_2178_ = lean_nat_dec_le(v___x_2175_, v___x_2177_);
lean_dec(v___x_2177_);
lean_dec(v___x_2175_);
if (v___x_2178_ == 0)
{
lean_dec(v___x_2171_);
lean_dec(v_index_2147_);
goto v___jp_2158_;
}
else
{
lean_object* v___x_2179_; 
lean_dec_ref(v_x_2128_);
lean_dec_ref(v_x_2127_);
v___x_2179_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_2132_, v___x_2171_, v_index_2147_, v_a_2133_, v_val_2150_);
lean_dec(v_index_2147_);
return v___x_2179_;
}
}
v___jp_2151_:
{
lean_object* v_size_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v_size_2154_ = lean_ctor_get(v___y_2152_, 0);
v___x_2155_ = lean_unsigned_to_nat(1u);
v___x_2156_ = lean_nat_add(v_size_2154_, v___x_2155_);
v___x_2157_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2152_, v___x_2156_, v_i_2153_, v_a_2133_, v_val_2150_);
lean_dec(v_i_2153_);
return v___x_2157_;
}
v___jp_2158_:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
lean_inc_ref(v_x_2128_);
lean_inc_ref(v_x_2127_);
v___x_2159_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_2127_, v_x_2128_, v_m_2132_);
lean_inc(v_a_2133_);
v___x_2160_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_2127_, v_x_2128_, v___x_2159_, v_a_2133_);
switch(lean_obj_tag(v___x_2160_))
{
case 0:
{
lean_object* v_index_2161_; lean_object* v_size_2162_; lean_object* v___x_2163_; 
v_index_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_index_2161_);
lean_dec_ref_known(v___x_2160_, 3);
v_size_2162_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_size_2162_);
v___x_2163_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2159_, v_size_2162_, v_index_2161_, v_a_2133_, v_val_2150_);
lean_dec(v_index_2161_);
return v___x_2163_;
}
case 1:
{
lean_object* v_index_2164_; 
v_index_2164_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_index_2164_);
lean_dec_ref_known(v___x_2160_, 1);
v___y_2152_ = v___x_2159_;
v_i_2153_ = v_index_2164_;
goto v___jp_2151_;
}
default: 
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = lean_unsigned_to_nat(0u);
v___x_2166_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2159_, v___x_2165_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_index_2167_; 
v_index_2167_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_index_2167_);
lean_dec_ref_known(v___x_2166_, 1);
v___y_2152_ = v___x_2159_;
v_i_2153_ = v_index_2167_;
goto v___jp_2151_;
}
else
{
lean_dec(v_val_2150_);
lean_dec(v_a_2133_);
return v___x_2159_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = lean_box(0);
v___x_2181_ = lean_apply_1(v_f_2134_, v___x_2180_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_dec(v_a_2133_);
lean_dec_ref(v_x_2128_);
lean_dec_ref(v_x_2127_);
return v_m_2132_;
}
else
{
lean_object* v_val_2182_; lean_object* v___y_2184_; lean_object* v_i_2185_; lean_object* v___y_2191_; lean_object* v_size_2200_; lean_object* v_keyArray_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; uint8_t v___x_2205_; 
v_val_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_val_2182_);
lean_dec_ref_known(v___x_2181_, 1);
v_size_2200_ = lean_ctor_get(v_m_2132_, 0);
v_keyArray_2201_ = lean_ctor_get(v_m_2132_, 1);
v___x_2202_ = lean_unsigned_to_nat(1u);
v___x_2203_ = lean_nat_add(v_size_2200_, v___x_2202_);
v___x_2204_ = lean_array_get_size(v_keyArray_2201_);
v___x_2205_ = lean_nat_dec_lt(v___x_2203_, v___x_2204_);
if (v___x_2205_ == 0)
{
lean_object* v___x_2206_; 
lean_dec(v___x_2203_);
lean_inc_ref(v_x_2128_);
lean_inc_ref(v_x_2127_);
v___x_2206_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_2127_, v_x_2128_, v_m_2132_);
v___y_2191_ = v___x_2206_;
goto v___jp_2190_;
}
else
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; uint8_t v___x_2211_; 
v___x_2207_ = lean_unsigned_to_nat(4u);
v___x_2208_ = lean_nat_mul(v___x_2203_, v___x_2207_);
lean_dec(v___x_2203_);
v___x_2209_ = lean_unsigned_to_nat(3u);
v___x_2210_ = lean_nat_mul(v___x_2204_, v___x_2209_);
v___x_2211_ = lean_nat_dec_le(v___x_2208_, v___x_2210_);
lean_dec(v___x_2210_);
lean_dec(v___x_2208_);
if (v___x_2211_ == 0)
{
lean_object* v___x_2212_; 
lean_inc_ref(v_x_2128_);
lean_inc_ref(v_x_2127_);
v___x_2212_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_2127_, v_x_2128_, v_m_2132_);
v___y_2191_ = v___x_2212_;
goto v___jp_2190_;
}
else
{
v___y_2191_ = v_m_2132_;
goto v___jp_2190_;
}
}
v___jp_2183_:
{
lean_object* v_size_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v_size_2186_ = lean_ctor_get(v___y_2184_, 0);
v___x_2187_ = lean_unsigned_to_nat(1u);
v___x_2188_ = lean_nat_add(v_size_2186_, v___x_2187_);
v___x_2189_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2184_, v___x_2188_, v_i_2185_, v_a_2133_, v_val_2182_);
lean_dec(v_i_2185_);
return v___x_2189_;
}
v___jp_2190_:
{
lean_object* v___x_2192_; 
lean_inc(v_a_2133_);
v___x_2192_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_2127_, v_x_2128_, v___y_2191_, v_a_2133_);
switch(lean_obj_tag(v___x_2192_))
{
case 0:
{
lean_object* v_index_2193_; lean_object* v_size_2194_; lean_object* v___x_2195_; 
v_index_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_index_2193_);
lean_dec_ref_known(v___x_2192_, 3);
v_size_2194_ = lean_ctor_get(v___y_2191_, 0);
lean_inc(v_size_2194_);
v___x_2195_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2191_, v_size_2194_, v_index_2193_, v_a_2133_, v_val_2182_);
lean_dec(v_index_2193_);
return v___x_2195_;
}
case 1:
{
lean_object* v_index_2196_; 
v_index_2196_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_index_2196_);
lean_dec_ref_known(v___x_2192_, 1);
v___y_2184_ = v___y_2191_;
v_i_2185_ = v_index_2196_;
goto v___jp_2183_;
}
default: 
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = lean_unsigned_to_nat(0u);
v___x_2198_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2191_, v___x_2197_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_index_2199_; 
v_index_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_index_2199_);
lean_dec_ref_known(v___x_2198_, 1);
v___y_2184_ = v___y_2191_;
v_i_2185_ = v_index_2199_;
goto v___jp_2183_;
}
else
{
lean_dec(v_val_2182_);
lean_dec(v_a_2133_);
return v___y_2191_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insertMany___redArg___lam__0(lean_object* v_x_2213_, lean_object* v_x_2214_, lean_object* v_x_2215_, lean_object* v_____s_2216_){
_start:
{
lean_object* v_fst_2217_; lean_object* v_snd_2218_; lean_object* v___y_2220_; lean_object* v_i_2221_; lean_object* v___y_2228_; lean_object* v___y_2240_; lean_object* v_i_2241_; lean_object* v___x_2259_; 
v_fst_2217_ = lean_ctor_get(v_x_2215_, 0);
lean_inc_n(v_fst_2217_, 2);
v_snd_2218_ = lean_ctor_get(v_x_2215_, 1);
lean_inc(v_snd_2218_);
lean_dec_ref(v_x_2215_);
lean_inc_ref(v_x_2214_);
lean_inc_ref(v_x_2213_);
v___x_2259_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_2213_, v_x_2214_, v_____s_2216_, v_fst_2217_);
switch(lean_obj_tag(v___x_2259_))
{
case 0:
{
lean_object* v_index_2260_; lean_object* v_size_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
lean_dec_ref(v_x_2214_);
lean_dec_ref(v_x_2213_);
v_index_2260_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_index_2260_);
lean_dec_ref_known(v___x_2259_, 3);
v_size_2261_ = lean_ctor_get(v_____s_2216_, 0);
lean_inc(v_size_2261_);
v___x_2262_ = l_Std_DHashMap_Raw_setEntry___redArg(v_____s_2216_, v_size_2261_, v_index_2260_, v_fst_2217_, v_snd_2218_);
lean_dec(v_index_2260_);
v___x_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
return v___x_2263_;
}
case 1:
{
lean_object* v_index_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2283_; 
v_index_2264_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2266_ = v___x_2259_;
v_isShared_2267_ = v_isSharedCheck_2283_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_index_2264_);
lean_dec(v___x_2259_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2283_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v_size_2268_; lean_object* v_keyArray_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; uint8_t v___x_2273_; 
v_size_2268_ = lean_ctor_get(v_____s_2216_, 0);
v_keyArray_2269_ = lean_ctor_get(v_____s_2216_, 1);
v___x_2270_ = lean_unsigned_to_nat(1u);
v___x_2271_ = lean_nat_add(v_size_2268_, v___x_2270_);
v___x_2272_ = lean_array_get_size(v_keyArray_2269_);
v___x_2273_ = lean_nat_dec_lt(v___x_2271_, v___x_2272_);
if (v___x_2273_ == 0)
{
lean_dec(v___x_2271_);
lean_del_object(v___x_2266_);
lean_dec(v_index_2264_);
goto v___jp_2247_;
}
else
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; 
v___x_2274_ = lean_unsigned_to_nat(4u);
v___x_2275_ = lean_nat_mul(v___x_2271_, v___x_2274_);
v___x_2276_ = lean_unsigned_to_nat(3u);
v___x_2277_ = lean_nat_mul(v___x_2272_, v___x_2276_);
v___x_2278_ = lean_nat_dec_le(v___x_2275_, v___x_2277_);
lean_dec(v___x_2277_);
lean_dec(v___x_2275_);
if (v___x_2278_ == 0)
{
lean_dec(v___x_2271_);
lean_del_object(v___x_2266_);
lean_dec(v_index_2264_);
goto v___jp_2247_;
}
else
{
lean_object* v___x_2279_; lean_object* v___x_2281_; 
lean_dec_ref(v_x_2214_);
lean_dec_ref(v_x_2213_);
v___x_2279_ = l_Std_DHashMap_Raw_setEntry___redArg(v_____s_2216_, v___x_2271_, v_index_2264_, v_fst_2217_, v_snd_2218_);
lean_dec(v_index_2264_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 0, v___x_2279_);
v___x_2281_ = v___x_2266_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2279_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
}
default: 
{
lean_object* v_size_2284_; lean_object* v_keyArray_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; uint8_t v___x_2289_; 
v_size_2284_ = lean_ctor_get(v_____s_2216_, 0);
v_keyArray_2285_ = lean_ctor_get(v_____s_2216_, 1);
v___x_2286_ = lean_unsigned_to_nat(1u);
v___x_2287_ = lean_nat_add(v_size_2284_, v___x_2286_);
v___x_2288_ = lean_array_get_size(v_keyArray_2285_);
v___x_2289_ = lean_nat_dec_lt(v___x_2287_, v___x_2288_);
if (v___x_2289_ == 0)
{
lean_object* v___x_2290_; 
lean_dec(v___x_2287_);
lean_inc_ref(v_x_2214_);
lean_inc_ref(v_x_2213_);
v___x_2290_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_2213_, v_x_2214_, v_____s_2216_);
v___y_2228_ = v___x_2290_;
goto v___jp_2227_;
}
else
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; uint8_t v___x_2295_; 
v___x_2291_ = lean_unsigned_to_nat(4u);
v___x_2292_ = lean_nat_mul(v___x_2287_, v___x_2291_);
lean_dec(v___x_2287_);
v___x_2293_ = lean_unsigned_to_nat(3u);
v___x_2294_ = lean_nat_mul(v___x_2288_, v___x_2293_);
v___x_2295_ = lean_nat_dec_le(v___x_2292_, v___x_2294_);
lean_dec(v___x_2294_);
lean_dec(v___x_2292_);
if (v___x_2295_ == 0)
{
lean_object* v___x_2296_; 
lean_inc_ref(v_x_2214_);
lean_inc_ref(v_x_2213_);
v___x_2296_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_2213_, v_x_2214_, v_____s_2216_);
v___y_2228_ = v___x_2296_;
goto v___jp_2227_;
}
else
{
v___y_2228_ = v_____s_2216_;
goto v___jp_2227_;
}
}
}
}
v___jp_2219_:
{
lean_object* v_size_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v_size_2222_ = lean_ctor_get(v___y_2220_, 0);
v___x_2223_ = lean_unsigned_to_nat(1u);
v___x_2224_ = lean_nat_add(v_size_2222_, v___x_2223_);
v___x_2225_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2220_, v___x_2224_, v_i_2221_, v_fst_2217_, v_snd_2218_);
lean_dec(v_i_2221_);
v___x_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2225_);
return v___x_2226_;
}
v___jp_2227_:
{
lean_object* v___x_2229_; 
lean_inc(v_fst_2217_);
v___x_2229_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_2213_, v_x_2214_, v___y_2228_, v_fst_2217_);
switch(lean_obj_tag(v___x_2229_))
{
case 0:
{
lean_object* v_index_2230_; lean_object* v_size_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v_index_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_index_2230_);
lean_dec_ref_known(v___x_2229_, 3);
v_size_2231_ = lean_ctor_get(v___y_2228_, 0);
lean_inc(v_size_2231_);
v___x_2232_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2228_, v_size_2231_, v_index_2230_, v_fst_2217_, v_snd_2218_);
lean_dec(v_index_2230_);
v___x_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2232_);
return v___x_2233_;
}
case 1:
{
lean_object* v_index_2234_; 
v_index_2234_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_index_2234_);
lean_dec_ref_known(v___x_2229_, 1);
v___y_2220_ = v___y_2228_;
v_i_2221_ = v_index_2234_;
goto v___jp_2219_;
}
default: 
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2235_ = lean_unsigned_to_nat(0u);
v___x_2236_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2228_, v___x_2235_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_index_2237_; 
v_index_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_index_2237_);
lean_dec_ref_known(v___x_2236_, 1);
v___y_2220_ = v___y_2228_;
v_i_2221_ = v_index_2237_;
goto v___jp_2219_;
}
else
{
lean_object* v___x_2238_; 
lean_dec(v_snd_2218_);
lean_dec(v_fst_2217_);
v___x_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2238_, 0, v___y_2228_);
return v___x_2238_;
}
}
}
}
v___jp_2239_:
{
lean_object* v_size_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v_size_2242_ = lean_ctor_get(v___y_2240_, 0);
v___x_2243_ = lean_unsigned_to_nat(1u);
v___x_2244_ = lean_nat_add(v_size_2242_, v___x_2243_);
v___x_2245_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2240_, v___x_2244_, v_i_2241_, v_fst_2217_, v_snd_2218_);
lean_dec(v_i_2241_);
v___x_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
return v___x_2246_;
}
v___jp_2247_:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
lean_inc_ref(v_x_2214_);
lean_inc_ref(v_x_2213_);
v___x_2248_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_2213_, v_x_2214_, v_____s_2216_);
lean_inc(v_fst_2217_);
v___x_2249_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_2213_, v_x_2214_, v___x_2248_, v_fst_2217_);
switch(lean_obj_tag(v___x_2249_))
{
case 0:
{
lean_object* v_index_2250_; lean_object* v_size_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v_index_2250_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_index_2250_);
lean_dec_ref_known(v___x_2249_, 3);
v_size_2251_ = lean_ctor_get(v___x_2248_, 0);
lean_inc(v_size_2251_);
v___x_2252_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2248_, v_size_2251_, v_index_2250_, v_fst_2217_, v_snd_2218_);
lean_dec(v_index_2250_);
v___x_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
return v___x_2253_;
}
case 1:
{
lean_object* v_index_2254_; 
v_index_2254_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_index_2254_);
lean_dec_ref_known(v___x_2249_, 1);
v___y_2240_ = v___x_2248_;
v_i_2241_ = v_index_2254_;
goto v___jp_2239_;
}
default: 
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = lean_unsigned_to_nat(0u);
v___x_2256_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2248_, v___x_2255_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_index_2257_; 
v_index_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_index_2257_);
lean_dec_ref_known(v___x_2256_, 1);
v___y_2240_ = v___x_2248_;
v_i_2241_ = v_index_2257_;
goto v___jp_2239_;
}
else
{
lean_object* v___x_2258_; 
lean_dec(v_snd_2218_);
lean_dec(v_fst_2217_);
v___x_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2248_);
return v___x_2258_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insertMany___redArg(lean_object* v_x_2297_, lean_object* v_x_2298_, lean_object* v_inst_2299_, lean_object* v_m_2300_, lean_object* v_l_2301_){
_start:
{
lean_object* v___f_2302_; lean_object* v___x_2303_; 
v___f_2302_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2302_, 0, v_x_2297_);
lean_closure_set(v___f_2302_, 1, v_x_2298_);
v___x_2303_ = lean_apply_4(v_inst_2299_, lean_box(0), v_l_2301_, v_m_2300_, v___f_2302_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insertMany(lean_object* v_00_u03b1_2304_, lean_object* v_00_u03b2_2305_, lean_object* v_x_2306_, lean_object* v_x_2307_, lean_object* v_inst_2308_, lean_object* v_inst_2309_, lean_object* v_00_u03c1_2310_, lean_object* v_inst_2311_, lean_object* v_m_2312_, lean_object* v_l_2313_){
_start:
{
lean_object* v___f_2314_; lean_object* v___x_2315_; 
v___f_2314_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2314_, 0, v_x_2306_);
lean_closure_set(v___f_2314_, 1, v_x_2307_);
v___x_2315_ = lean_apply_4(v_inst_2311_, lean_box(0), v_l_2313_, v_m_2312_, v___f_2314_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertMany___redArg___lam__0(lean_object* v_x_2316_, lean_object* v_x_2317_, lean_object* v_x_2318_, lean_object* v_____s_2319_){
_start:
{
lean_object* v_fst_2320_; lean_object* v_snd_2321_; lean_object* v___y_2323_; lean_object* v_i_2324_; lean_object* v___y_2331_; lean_object* v___y_2343_; lean_object* v_i_2344_; lean_object* v___x_2362_; 
v_fst_2320_ = lean_ctor_get(v_x_2318_, 0);
lean_inc_n(v_fst_2320_, 2);
v_snd_2321_ = lean_ctor_get(v_x_2318_, 1);
lean_inc(v_snd_2321_);
lean_dec_ref(v_x_2318_);
lean_inc_ref(v_x_2317_);
lean_inc_ref(v_x_2316_);
v___x_2362_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_2316_, v_x_2317_, v_____s_2319_, v_fst_2320_);
switch(lean_obj_tag(v___x_2362_))
{
case 0:
{
lean_object* v_index_2363_; lean_object* v_size_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
lean_dec_ref(v_x_2317_);
lean_dec_ref(v_x_2316_);
v_index_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_index_2363_);
lean_dec_ref_known(v___x_2362_, 3);
v_size_2364_ = lean_ctor_get(v_____s_2319_, 0);
lean_inc(v_size_2364_);
v___x_2365_ = l_Std_DHashMap_Raw_setEntry___redArg(v_____s_2319_, v_size_2364_, v_index_2363_, v_fst_2320_, v_snd_2321_);
lean_dec(v_index_2363_);
v___x_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2365_);
return v___x_2366_;
}
case 1:
{
lean_object* v_index_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2386_; 
v_index_2367_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2369_ = v___x_2362_;
v_isShared_2370_ = v_isSharedCheck_2386_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_index_2367_);
lean_dec(v___x_2362_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2386_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v_size_2371_; lean_object* v_keyArray_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; uint8_t v___x_2376_; 
v_size_2371_ = lean_ctor_get(v_____s_2319_, 0);
v_keyArray_2372_ = lean_ctor_get(v_____s_2319_, 1);
v___x_2373_ = lean_unsigned_to_nat(1u);
v___x_2374_ = lean_nat_add(v_size_2371_, v___x_2373_);
v___x_2375_ = lean_array_get_size(v_keyArray_2372_);
v___x_2376_ = lean_nat_dec_lt(v___x_2374_, v___x_2375_);
if (v___x_2376_ == 0)
{
lean_dec(v___x_2374_);
lean_del_object(v___x_2369_);
lean_dec(v_index_2367_);
goto v___jp_2350_;
}
else
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; uint8_t v___x_2381_; 
v___x_2377_ = lean_unsigned_to_nat(4u);
v___x_2378_ = lean_nat_mul(v___x_2374_, v___x_2377_);
v___x_2379_ = lean_unsigned_to_nat(3u);
v___x_2380_ = lean_nat_mul(v___x_2375_, v___x_2379_);
v___x_2381_ = lean_nat_dec_le(v___x_2378_, v___x_2380_);
lean_dec(v___x_2380_);
lean_dec(v___x_2378_);
if (v___x_2381_ == 0)
{
lean_dec(v___x_2374_);
lean_del_object(v___x_2369_);
lean_dec(v_index_2367_);
goto v___jp_2350_;
}
else
{
lean_object* v___x_2382_; lean_object* v___x_2384_; 
lean_dec_ref(v_x_2317_);
lean_dec_ref(v_x_2316_);
v___x_2382_ = l_Std_DHashMap_Raw_setEntry___redArg(v_____s_2319_, v___x_2374_, v_index_2367_, v_fst_2320_, v_snd_2321_);
lean_dec(v_index_2367_);
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 0, v___x_2382_);
v___x_2384_ = v___x_2369_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2382_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
}
default: 
{
lean_object* v_size_2387_; lean_object* v_keyArray_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; uint8_t v___x_2392_; 
v_size_2387_ = lean_ctor_get(v_____s_2319_, 0);
v_keyArray_2388_ = lean_ctor_get(v_____s_2319_, 1);
v___x_2389_ = lean_unsigned_to_nat(1u);
v___x_2390_ = lean_nat_add(v_size_2387_, v___x_2389_);
v___x_2391_ = lean_array_get_size(v_keyArray_2388_);
v___x_2392_ = lean_nat_dec_lt(v___x_2390_, v___x_2391_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; 
lean_dec(v___x_2390_);
lean_inc_ref(v_x_2317_);
lean_inc_ref(v_x_2316_);
v___x_2393_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_2316_, v_x_2317_, v_____s_2319_);
v___y_2331_ = v___x_2393_;
goto v___jp_2330_;
}
else
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; uint8_t v___x_2398_; 
v___x_2394_ = lean_unsigned_to_nat(4u);
v___x_2395_ = lean_nat_mul(v___x_2390_, v___x_2394_);
lean_dec(v___x_2390_);
v___x_2396_ = lean_unsigned_to_nat(3u);
v___x_2397_ = lean_nat_mul(v___x_2391_, v___x_2396_);
v___x_2398_ = lean_nat_dec_le(v___x_2395_, v___x_2397_);
lean_dec(v___x_2397_);
lean_dec(v___x_2395_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; 
lean_inc_ref(v_x_2317_);
lean_inc_ref(v_x_2316_);
v___x_2399_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_2316_, v_x_2317_, v_____s_2319_);
v___y_2331_ = v___x_2399_;
goto v___jp_2330_;
}
else
{
v___y_2331_ = v_____s_2319_;
goto v___jp_2330_;
}
}
}
}
v___jp_2322_:
{
lean_object* v_size_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v_size_2325_ = lean_ctor_get(v___y_2323_, 0);
v___x_2326_ = lean_unsigned_to_nat(1u);
v___x_2327_ = lean_nat_add(v_size_2325_, v___x_2326_);
v___x_2328_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2323_, v___x_2327_, v_i_2324_, v_fst_2320_, v_snd_2321_);
lean_dec(v_i_2324_);
v___x_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
return v___x_2329_;
}
v___jp_2330_:
{
lean_object* v___x_2332_; 
lean_inc(v_fst_2320_);
v___x_2332_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_2316_, v_x_2317_, v___y_2331_, v_fst_2320_);
switch(lean_obj_tag(v___x_2332_))
{
case 0:
{
lean_object* v_index_2333_; lean_object* v_size_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v_index_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_index_2333_);
lean_dec_ref_known(v___x_2332_, 3);
v_size_2334_ = lean_ctor_get(v___y_2331_, 0);
lean_inc(v_size_2334_);
v___x_2335_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2331_, v_size_2334_, v_index_2333_, v_fst_2320_, v_snd_2321_);
lean_dec(v_index_2333_);
v___x_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2335_);
return v___x_2336_;
}
case 1:
{
lean_object* v_index_2337_; 
v_index_2337_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_index_2337_);
lean_dec_ref_known(v___x_2332_, 1);
v___y_2323_ = v___y_2331_;
v_i_2324_ = v_index_2337_;
goto v___jp_2322_;
}
default: 
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = lean_unsigned_to_nat(0u);
v___x_2339_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2331_, v___x_2338_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_index_2340_; 
v_index_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_index_2340_);
lean_dec_ref_known(v___x_2339_, 1);
v___y_2323_ = v___y_2331_;
v_i_2324_ = v_index_2340_;
goto v___jp_2322_;
}
else
{
lean_object* v___x_2341_; 
lean_dec(v_snd_2321_);
lean_dec(v_fst_2320_);
v___x_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2341_, 0, v___y_2331_);
return v___x_2341_;
}
}
}
}
v___jp_2342_:
{
lean_object* v_size_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v_size_2345_ = lean_ctor_get(v___y_2343_, 0);
v___x_2346_ = lean_unsigned_to_nat(1u);
v___x_2347_ = lean_nat_add(v_size_2345_, v___x_2346_);
v___x_2348_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2343_, v___x_2347_, v_i_2344_, v_fst_2320_, v_snd_2321_);
lean_dec(v_i_2344_);
v___x_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2348_);
return v___x_2349_;
}
v___jp_2350_:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
lean_inc_ref(v_x_2317_);
lean_inc_ref(v_x_2316_);
v___x_2351_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_2316_, v_x_2317_, v_____s_2319_);
lean_inc(v_fst_2320_);
v___x_2352_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_2316_, v_x_2317_, v___x_2351_, v_fst_2320_);
switch(lean_obj_tag(v___x_2352_))
{
case 0:
{
lean_object* v_index_2353_; lean_object* v_size_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v_index_2353_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_index_2353_);
lean_dec_ref_known(v___x_2352_, 3);
v_size_2354_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_size_2354_);
v___x_2355_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2351_, v_size_2354_, v_index_2353_, v_fst_2320_, v_snd_2321_);
lean_dec(v_index_2353_);
v___x_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
return v___x_2356_;
}
case 1:
{
lean_object* v_index_2357_; 
v_index_2357_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_index_2357_);
lean_dec_ref_known(v___x_2352_, 1);
v___y_2343_ = v___x_2351_;
v_i_2344_ = v_index_2357_;
goto v___jp_2342_;
}
default: 
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = lean_unsigned_to_nat(0u);
v___x_2359_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2351_, v___x_2358_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_index_2360_; 
v_index_2360_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_index_2360_);
lean_dec_ref_known(v___x_2359_, 1);
v___y_2343_ = v___x_2351_;
v_i_2344_ = v_index_2360_;
goto v___jp_2342_;
}
else
{
lean_object* v___x_2361_; 
lean_dec(v_snd_2321_);
lean_dec(v_fst_2320_);
v___x_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2351_);
return v___x_2361_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertMany___redArg(lean_object* v_x_2400_, lean_object* v_x_2401_, lean_object* v_inst_2402_, lean_object* v_m_2403_, lean_object* v_l_2404_){
_start:
{
lean_object* v___f_2405_; lean_object* v___x_2406_; 
v___f_2405_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_Const_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2405_, 0, v_x_2400_);
lean_closure_set(v___f_2405_, 1, v_x_2401_);
v___x_2406_ = lean_apply_4(v_inst_2402_, lean_box(0), v_l_2404_, v_m_2403_, v___f_2405_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertMany(lean_object* v_00_u03b1_2407_, lean_object* v_x_2408_, lean_object* v_x_2409_, lean_object* v_inst_2410_, lean_object* v_inst_2411_, lean_object* v_00_u03b2_2412_, lean_object* v_00_u03c1_2413_, lean_object* v_inst_2414_, lean_object* v_m_2415_, lean_object* v_l_2416_){
_start:
{
lean_object* v___f_2417_; lean_object* v___x_2418_; 
v___f_2417_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_Const_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2417_, 0, v_x_2408_);
lean_closure_set(v___f_2417_, 1, v_x_2409_);
v___x_2418_ = lean_apply_4(v_inst_2414_, lean_box(0), v_l_2416_, v_m_2415_, v___f_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg___lam__0(lean_object* v_x_2419_, lean_object* v_x_2420_, lean_object* v_a_2421_, lean_object* v_____s_2422_){
_start:
{
lean_object* v___x_2423_; lean_object* v___y_2425_; lean_object* v_i_2426_; lean_object* v___y_2433_; lean_object* v___y_2445_; lean_object* v_i_2446_; lean_object* v___x_2464_; 
v___x_2423_ = lean_box(0);
lean_inc(v_a_2421_);
lean_inc_ref(v_x_2420_);
lean_inc_ref(v_x_2419_);
v___x_2464_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_2419_, v_x_2420_, v_____s_2422_, v_a_2421_);
switch(lean_obj_tag(v___x_2464_))
{
case 0:
{
lean_object* v___x_2465_; 
lean_dec_ref_known(v___x_2464_, 3);
lean_dec(v_a_2421_);
lean_dec_ref(v_x_2420_);
lean_dec_ref(v_x_2419_);
v___x_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2465_, 0, v_____s_2422_);
return v___x_2465_;
}
case 1:
{
lean_object* v_index_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2485_; 
v_index_2466_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2468_ = v___x_2464_;
v_isShared_2469_ = v_isSharedCheck_2485_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_index_2466_);
lean_dec(v___x_2464_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2485_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v_size_2470_; lean_object* v_keyArray_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; uint8_t v___x_2475_; 
v_size_2470_ = lean_ctor_get(v_____s_2422_, 0);
v_keyArray_2471_ = lean_ctor_get(v_____s_2422_, 1);
v___x_2472_ = lean_unsigned_to_nat(1u);
v___x_2473_ = lean_nat_add(v_size_2470_, v___x_2472_);
v___x_2474_ = lean_array_get_size(v_keyArray_2471_);
v___x_2475_ = lean_nat_dec_lt(v___x_2473_, v___x_2474_);
if (v___x_2475_ == 0)
{
lean_dec(v___x_2473_);
lean_del_object(v___x_2468_);
lean_dec(v_index_2466_);
goto v___jp_2452_;
}
else
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; uint8_t v___x_2480_; 
v___x_2476_ = lean_unsigned_to_nat(4u);
v___x_2477_ = lean_nat_mul(v___x_2473_, v___x_2476_);
v___x_2478_ = lean_unsigned_to_nat(3u);
v___x_2479_ = lean_nat_mul(v___x_2474_, v___x_2478_);
v___x_2480_ = lean_nat_dec_le(v___x_2477_, v___x_2479_);
lean_dec(v___x_2479_);
lean_dec(v___x_2477_);
if (v___x_2480_ == 0)
{
lean_dec(v___x_2473_);
lean_del_object(v___x_2468_);
lean_dec(v_index_2466_);
goto v___jp_2452_;
}
else
{
lean_object* v___x_2481_; lean_object* v___x_2483_; 
lean_dec_ref(v_x_2420_);
lean_dec_ref(v_x_2419_);
v___x_2481_ = l_Std_DHashMap_Raw_setEntry___redArg(v_____s_2422_, v___x_2473_, v_index_2466_, v_a_2421_, v___x_2423_);
lean_dec(v_index_2466_);
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 0, v___x_2481_);
v___x_2483_ = v___x_2468_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2481_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
}
default: 
{
lean_object* v_size_2486_; lean_object* v_keyArray_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; uint8_t v___x_2491_; 
v_size_2486_ = lean_ctor_get(v_____s_2422_, 0);
v_keyArray_2487_ = lean_ctor_get(v_____s_2422_, 1);
v___x_2488_ = lean_unsigned_to_nat(1u);
v___x_2489_ = lean_nat_add(v_size_2486_, v___x_2488_);
v___x_2490_ = lean_array_get_size(v_keyArray_2487_);
v___x_2491_ = lean_nat_dec_lt(v___x_2489_, v___x_2490_);
if (v___x_2491_ == 0)
{
lean_object* v___x_2492_; 
lean_dec(v___x_2489_);
lean_inc_ref(v_x_2420_);
lean_inc_ref(v_x_2419_);
v___x_2492_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_2419_, v_x_2420_, v_____s_2422_);
v___y_2433_ = v___x_2492_;
goto v___jp_2432_;
}
else
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; uint8_t v___x_2497_; 
v___x_2493_ = lean_unsigned_to_nat(4u);
v___x_2494_ = lean_nat_mul(v___x_2489_, v___x_2493_);
lean_dec(v___x_2489_);
v___x_2495_ = lean_unsigned_to_nat(3u);
v___x_2496_ = lean_nat_mul(v___x_2490_, v___x_2495_);
v___x_2497_ = lean_nat_dec_le(v___x_2494_, v___x_2496_);
lean_dec(v___x_2496_);
lean_dec(v___x_2494_);
if (v___x_2497_ == 0)
{
lean_object* v___x_2498_; 
lean_inc_ref(v_x_2420_);
lean_inc_ref(v_x_2419_);
v___x_2498_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_2419_, v_x_2420_, v_____s_2422_);
v___y_2433_ = v___x_2498_;
goto v___jp_2432_;
}
else
{
v___y_2433_ = v_____s_2422_;
goto v___jp_2432_;
}
}
}
}
v___jp_2424_:
{
lean_object* v_size_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v_size_2427_ = lean_ctor_get(v___y_2425_, 0);
v___x_2428_ = lean_unsigned_to_nat(1u);
v___x_2429_ = lean_nat_add(v_size_2427_, v___x_2428_);
v___x_2430_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2425_, v___x_2429_, v_i_2426_, v_a_2421_, v___x_2423_);
lean_dec(v_i_2426_);
v___x_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2430_);
return v___x_2431_;
}
v___jp_2432_:
{
lean_object* v___x_2434_; 
lean_inc(v_a_2421_);
v___x_2434_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_2419_, v_x_2420_, v___y_2433_, v_a_2421_);
switch(lean_obj_tag(v___x_2434_))
{
case 0:
{
lean_object* v_index_2435_; lean_object* v_size_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v_index_2435_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_index_2435_);
lean_dec_ref_known(v___x_2434_, 3);
v_size_2436_ = lean_ctor_get(v___y_2433_, 0);
lean_inc(v_size_2436_);
v___x_2437_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2433_, v_size_2436_, v_index_2435_, v_a_2421_, v___x_2423_);
lean_dec(v_index_2435_);
v___x_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2437_);
return v___x_2438_;
}
case 1:
{
lean_object* v_index_2439_; 
v_index_2439_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_index_2439_);
lean_dec_ref_known(v___x_2434_, 1);
v___y_2425_ = v___y_2433_;
v_i_2426_ = v_index_2439_;
goto v___jp_2424_;
}
default: 
{
lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2440_ = lean_unsigned_to_nat(0u);
v___x_2441_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2433_, v___x_2440_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v_index_2442_; 
v_index_2442_ = lean_ctor_get(v___x_2441_, 0);
lean_inc(v_index_2442_);
lean_dec_ref_known(v___x_2441_, 1);
v___y_2425_ = v___y_2433_;
v_i_2426_ = v_index_2442_;
goto v___jp_2424_;
}
else
{
lean_object* v___x_2443_; 
lean_dec(v_a_2421_);
v___x_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2443_, 0, v___y_2433_);
return v___x_2443_;
}
}
}
}
v___jp_2444_:
{
lean_object* v_size_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v_size_2447_ = lean_ctor_get(v___y_2445_, 0);
v___x_2448_ = lean_unsigned_to_nat(1u);
v___x_2449_ = lean_nat_add(v_size_2447_, v___x_2448_);
v___x_2450_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2445_, v___x_2449_, v_i_2446_, v_a_2421_, v___x_2423_);
lean_dec(v_i_2446_);
v___x_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2450_);
return v___x_2451_;
}
v___jp_2452_:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
lean_inc_ref(v_x_2420_);
lean_inc_ref(v_x_2419_);
v___x_2453_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_2419_, v_x_2420_, v_____s_2422_);
lean_inc(v_a_2421_);
v___x_2454_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_2419_, v_x_2420_, v___x_2453_, v_a_2421_);
switch(lean_obj_tag(v___x_2454_))
{
case 0:
{
lean_object* v_index_2455_; lean_object* v_size_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v_index_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_index_2455_);
lean_dec_ref_known(v___x_2454_, 3);
v_size_2456_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_size_2456_);
v___x_2457_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2453_, v_size_2456_, v_index_2455_, v_a_2421_, v___x_2423_);
lean_dec(v_index_2455_);
v___x_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
return v___x_2458_;
}
case 1:
{
lean_object* v_index_2459_; 
v_index_2459_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_index_2459_);
lean_dec_ref_known(v___x_2454_, 1);
v___y_2445_ = v___x_2453_;
v_i_2446_ = v_index_2459_;
goto v___jp_2444_;
}
default: 
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2460_ = lean_unsigned_to_nat(0u);
v___x_2461_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2453_, v___x_2460_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_index_2462_; 
v_index_2462_ = lean_ctor_get(v___x_2461_, 0);
lean_inc(v_index_2462_);
lean_dec_ref_known(v___x_2461_, 1);
v___y_2445_ = v___x_2453_;
v_i_2446_ = v_index_2462_;
goto v___jp_2444_;
}
else
{
lean_object* v___x_2463_; 
lean_dec(v_a_2421_);
v___x_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2453_);
return v___x_2463_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg(lean_object* v_x_2499_, lean_object* v_x_2500_, lean_object* v_inst_2501_, lean_object* v_m_2502_, lean_object* v_l_2503_){
_start:
{
lean_object* v___f_2504_; lean_object* v___x_2505_; 
v___f_2504_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2504_, 0, v_x_2499_);
lean_closure_set(v___f_2504_, 1, v_x_2500_);
v___x_2505_ = lean_apply_4(v_inst_2501_, lean_box(0), v_l_2503_, v_m_2502_, v___f_2504_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertManyIfNewUnit(lean_object* v_00_u03b1_2506_, lean_object* v_x_2507_, lean_object* v_x_2508_, lean_object* v_inst_2509_, lean_object* v_inst_2510_, lean_object* v_00_u03c1_2511_, lean_object* v_inst_2512_, lean_object* v_m_2513_, lean_object* v_l_2514_){
_start:
{
lean_object* v___f_2515_; lean_object* v___x_2516_; 
v___f_2515_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2515_, 0, v_x_2507_);
lean_closure_set(v___f_2515_, 1, v_x_2508_);
v___x_2516_ = lean_apply_4(v_inst_2512_, lean_box(0), v_l_2514_, v_m_2513_, v___f_2515_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_union___redArg___lam__0(lean_object* v_x_2517_, lean_object* v_x_2518_, lean_object* v_a_2519_, lean_object* v_b_2520_, lean_object* v_acc_2521_){
_start:
{
lean_object* v___y_2523_; lean_object* v_i_2524_; lean_object* v___y_2543_; lean_object* v_i_2544_; lean_object* v___y_2551_; lean_object* v___x_2562_; 
lean_inc(v_a_2519_);
lean_inc_ref(v_x_2518_);
lean_inc_ref(v_x_2517_);
v___x_2562_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_2517_, v_x_2518_, v_acc_2521_, v_a_2519_);
switch(lean_obj_tag(v___x_2562_))
{
case 0:
{
lean_object* v___x_2563_; 
lean_dec_ref_known(v___x_2562_, 3);
lean_dec(v_b_2520_);
lean_dec(v_a_2519_);
lean_dec_ref(v_x_2518_);
lean_dec_ref(v_x_2517_);
v___x_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2563_, 0, v_acc_2521_);
return v___x_2563_;
}
case 1:
{
lean_object* v_index_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2583_; 
v_index_2564_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2566_ = v___x_2562_;
v_isShared_2567_ = v_isSharedCheck_2583_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_index_2564_);
lean_dec(v___x_2562_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2583_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v_size_2568_; lean_object* v_keyArray_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; 
v_size_2568_ = lean_ctor_get(v_acc_2521_, 0);
v_keyArray_2569_ = lean_ctor_get(v_acc_2521_, 1);
v___x_2570_ = lean_unsigned_to_nat(1u);
v___x_2571_ = lean_nat_add(v_size_2568_, v___x_2570_);
v___x_2572_ = lean_array_get_size(v_keyArray_2569_);
v___x_2573_ = lean_nat_dec_lt(v___x_2571_, v___x_2572_);
if (v___x_2573_ == 0)
{
lean_dec(v___x_2571_);
lean_del_object(v___x_2566_);
lean_dec(v_index_2564_);
goto v___jp_2530_;
}
else
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; uint8_t v___x_2578_; 
v___x_2574_ = lean_unsigned_to_nat(4u);
v___x_2575_ = lean_nat_mul(v___x_2571_, v___x_2574_);
v___x_2576_ = lean_unsigned_to_nat(3u);
v___x_2577_ = lean_nat_mul(v___x_2572_, v___x_2576_);
v___x_2578_ = lean_nat_dec_le(v___x_2575_, v___x_2577_);
lean_dec(v___x_2577_);
lean_dec(v___x_2575_);
if (v___x_2578_ == 0)
{
lean_dec(v___x_2571_);
lean_del_object(v___x_2566_);
lean_dec(v_index_2564_);
goto v___jp_2530_;
}
else
{
lean_object* v___x_2579_; lean_object* v___x_2581_; 
lean_dec_ref(v_x_2518_);
lean_dec_ref(v_x_2517_);
v___x_2579_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2521_, v___x_2571_, v_index_2564_, v_a_2519_, v_b_2520_);
lean_dec(v_index_2564_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v___x_2579_);
v___x_2581_ = v___x_2566_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2579_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
}
default: 
{
lean_object* v_size_2584_; lean_object* v_keyArray_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; 
v_size_2584_ = lean_ctor_get(v_acc_2521_, 0);
v_keyArray_2585_ = lean_ctor_get(v_acc_2521_, 1);
v___x_2586_ = lean_unsigned_to_nat(1u);
v___x_2587_ = lean_nat_add(v_size_2584_, v___x_2586_);
v___x_2588_ = lean_array_get_size(v_keyArray_2585_);
v___x_2589_ = lean_nat_dec_lt(v___x_2587_, v___x_2588_);
if (v___x_2589_ == 0)
{
lean_object* v___x_2590_; 
lean_dec(v___x_2587_);
lean_inc_ref(v_x_2518_);
lean_inc_ref(v_x_2517_);
v___x_2590_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_2517_, v_x_2518_, v_acc_2521_);
v___y_2551_ = v___x_2590_;
goto v___jp_2550_;
}
else
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; uint8_t v___x_2595_; 
v___x_2591_ = lean_unsigned_to_nat(4u);
v___x_2592_ = lean_nat_mul(v___x_2587_, v___x_2591_);
lean_dec(v___x_2587_);
v___x_2593_ = lean_unsigned_to_nat(3u);
v___x_2594_ = lean_nat_mul(v___x_2588_, v___x_2593_);
v___x_2595_ = lean_nat_dec_le(v___x_2592_, v___x_2594_);
lean_dec(v___x_2594_);
lean_dec(v___x_2592_);
if (v___x_2595_ == 0)
{
lean_object* v___x_2596_; 
lean_inc_ref(v_x_2518_);
lean_inc_ref(v_x_2517_);
v___x_2596_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_2517_, v_x_2518_, v_acc_2521_);
v___y_2551_ = v___x_2596_;
goto v___jp_2550_;
}
else
{
v___y_2551_ = v_acc_2521_;
goto v___jp_2550_;
}
}
}
}
v___jp_2522_:
{
lean_object* v_size_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v_size_2525_ = lean_ctor_get(v___y_2523_, 0);
v___x_2526_ = lean_unsigned_to_nat(1u);
v___x_2527_ = lean_nat_add(v_size_2525_, v___x_2526_);
v___x_2528_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2523_, v___x_2527_, v_i_2524_, v_a_2519_, v_b_2520_);
lean_dec(v_i_2524_);
v___x_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2528_);
return v___x_2529_;
}
v___jp_2530_:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
lean_inc_ref(v_x_2518_);
lean_inc_ref(v_x_2517_);
v___x_2531_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_2517_, v_x_2518_, v_acc_2521_);
lean_inc(v_a_2519_);
v___x_2532_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_2517_, v_x_2518_, v___x_2531_, v_a_2519_);
switch(lean_obj_tag(v___x_2532_))
{
case 0:
{
lean_object* v_index_2533_; lean_object* v_size_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v_index_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_index_2533_);
lean_dec_ref_known(v___x_2532_, 3);
v_size_2534_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_size_2534_);
v___x_2535_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2531_, v_size_2534_, v_index_2533_, v_a_2519_, v_b_2520_);
lean_dec(v_index_2533_);
v___x_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2535_);
return v___x_2536_;
}
case 1:
{
lean_object* v_index_2537_; 
v_index_2537_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_index_2537_);
lean_dec_ref_known(v___x_2532_, 1);
v___y_2523_ = v___x_2531_;
v_i_2524_ = v_index_2537_;
goto v___jp_2522_;
}
default: 
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = lean_unsigned_to_nat(0u);
v___x_2539_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2531_, v___x_2538_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v_index_2540_; 
v_index_2540_ = lean_ctor_get(v___x_2539_, 0);
lean_inc(v_index_2540_);
lean_dec_ref_known(v___x_2539_, 1);
v___y_2523_ = v___x_2531_;
v_i_2524_ = v_index_2540_;
goto v___jp_2522_;
}
else
{
lean_object* v___x_2541_; 
lean_dec(v_b_2520_);
lean_dec(v_a_2519_);
v___x_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2531_);
return v___x_2541_;
}
}
}
}
v___jp_2542_:
{
lean_object* v_size_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v_size_2545_ = lean_ctor_get(v___y_2543_, 0);
v___x_2546_ = lean_unsigned_to_nat(1u);
v___x_2547_ = lean_nat_add(v_size_2545_, v___x_2546_);
v___x_2548_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2543_, v___x_2547_, v_i_2544_, v_a_2519_, v_b_2520_);
lean_dec(v_i_2544_);
v___x_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2548_);
return v___x_2549_;
}
v___jp_2550_:
{
lean_object* v___x_2552_; 
lean_inc(v_a_2519_);
v___x_2552_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_2517_, v_x_2518_, v___y_2551_, v_a_2519_);
switch(lean_obj_tag(v___x_2552_))
{
case 0:
{
lean_object* v_index_2553_; lean_object* v_size_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v_index_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_index_2553_);
lean_dec_ref_known(v___x_2552_, 3);
v_size_2554_ = lean_ctor_get(v___y_2551_, 0);
lean_inc(v_size_2554_);
v___x_2555_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2551_, v_size_2554_, v_index_2553_, v_a_2519_, v_b_2520_);
lean_dec(v_index_2553_);
v___x_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2555_);
return v___x_2556_;
}
case 1:
{
lean_object* v_index_2557_; 
v_index_2557_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_index_2557_);
lean_dec_ref_known(v___x_2552_, 1);
v___y_2543_ = v___y_2551_;
v_i_2544_ = v_index_2557_;
goto v___jp_2542_;
}
default: 
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2558_ = lean_unsigned_to_nat(0u);
v___x_2559_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2551_, v___x_2558_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_index_2560_; 
v_index_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_index_2560_);
lean_dec_ref_known(v___x_2559_, 1);
v___y_2543_ = v___y_2551_;
v_i_2544_ = v_index_2560_;
goto v___jp_2542_;
}
else
{
lean_object* v___x_2561_; 
lean_dec(v_b_2520_);
lean_dec(v_a_2519_);
v___x_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2561_, 0, v___y_2551_);
return v___x_2561_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_union___redArg(lean_object* v_x_2618_, lean_object* v_x_2619_, lean_object* v_m_u2081_2620_, lean_object* v_m_u2082_2621_){
_start:
{
lean_object* v_size_2622_; lean_object* v_size_2623_; uint8_t v___x_2624_; 
v_size_2622_ = lean_ctor_get(v_m_u2081_2620_, 0);
v_size_2623_ = lean_ctor_get(v_m_u2082_2621_, 0);
v___x_2624_ = lean_nat_dec_le(v_size_2622_, v_size_2623_);
if (v___x_2624_ == 0)
{
lean_object* v___f_2625_; lean_object* v___x_2626_; 
v___f_2625_ = ((lean_object*)(l_Std_ExtDHashMap_union___redArg___closed__10));
v___x_2626_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_2625_, v_x_2618_, v_x_2619_, v_m_u2081_2620_, v_m_u2082_2621_);
return v___x_2626_;
}
else
{
lean_object* v___f_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___f_2627_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2627_, 0, v_x_2618_);
lean_closure_set(v___f_2627_, 1, v_x_2619_);
v___x_2628_ = ((lean_object*)(l_Std_ExtDHashMap_union___redArg___closed__9));
v___x_2629_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_2628_, v___f_2627_, v_m_u2082_2621_, v_m_u2081_2620_);
return v___x_2629_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_union(lean_object* v_00_u03b1_2630_, lean_object* v_00_u03b2_2631_, lean_object* v_x_2632_, lean_object* v_x_2633_, lean_object* v_inst_2634_, lean_object* v_inst_2635_, lean_object* v_m_u2081_2636_, lean_object* v_m_u2082_2637_){
_start:
{
lean_object* v_size_2638_; lean_object* v_size_2639_; uint8_t v___x_2640_; 
v_size_2638_ = lean_ctor_get(v_m_u2081_2636_, 0);
v_size_2639_ = lean_ctor_get(v_m_u2082_2637_, 0);
v___x_2640_ = lean_nat_dec_le(v_size_2638_, v_size_2639_);
if (v___x_2640_ == 0)
{
lean_object* v___f_2641_; lean_object* v___x_2642_; 
v___f_2641_ = ((lean_object*)(l_Std_ExtDHashMap_union___redArg___closed__10));
v___x_2642_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_2641_, v_x_2632_, v_x_2633_, v_m_u2081_2636_, v_m_u2082_2637_);
return v___x_2642_;
}
else
{
lean_object* v___f_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___f_2643_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2643_, 0, v_x_2632_);
lean_closure_set(v___f_2643_, 1, v_x_2633_);
v___x_2644_ = ((lean_object*)(l_Std_ExtDHashMap_union___redArg___closed__9));
v___x_2645_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_2644_, v___f_2643_, v_m_u2082_2637_, v_m_u2081_2636_);
return v___x_2645_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instUnionOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_2646_, lean_object* v_x_2647_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_union), 8, 6);
lean_closure_set(v___x_2648_, 0, lean_box(0));
lean_closure_set(v___x_2648_, 1, lean_box(0));
lean_closure_set(v___x_2648_, 2, v_x_2646_);
lean_closure_set(v___x_2648_, 3, v_x_2647_);
lean_closure_set(v___x_2648_, 4, lean_box(0));
lean_closure_set(v___x_2648_, 5, lean_box(0));
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instUnionOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_2649_, lean_object* v_00_u03b2_2650_, lean_object* v_x_2651_, lean_object* v_x_2652_, lean_object* v_inst_2653_, lean_object* v_inst_2654_){
_start:
{
lean_object* v___x_2655_; 
v___x_2655_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_union), 8, 6);
lean_closure_set(v___x_2655_, 0, lean_box(0));
lean_closure_set(v___x_2655_, 1, lean_box(0));
lean_closure_set(v___x_2655_, 2, v_x_2651_);
lean_closure_set(v___x_2655_, 3, v_x_2652_);
lean_closure_set(v___x_2655_, 4, lean_box(0));
lean_closure_set(v___x_2655_, 5, lean_box(0));
return v___x_2655_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0(lean_object* v_x_2656_, lean_object* v_x_2657_, lean_object* v_inst_2658_, lean_object* v_m_u2081_2659_, lean_object* v_m_u2082_2660_){
_start:
{
uint8_t v___x_2661_; 
v___x_2661_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_x_2656_, v_x_2657_, v_inst_2658_, v_m_u2081_2659_, v_m_u2082_2660_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0___boxed(lean_object* v_x_2662_, lean_object* v_x_2663_, lean_object* v_inst_2664_, lean_object* v_m_u2081_2665_, lean_object* v_m_u2082_2666_){
_start:
{
uint8_t v_res_2667_; lean_object* v_r_2668_; 
v_res_2667_ = l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0(v_x_2662_, v_x_2663_, v_inst_2664_, v_m_u2081_2665_, v_m_u2082_2666_);
v_r_2668_ = lean_box(v_res_2667_);
return v_r_2668_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg(lean_object* v_x_2669_, lean_object* v_x_2670_, lean_object* v_inst_2671_){
_start:
{
lean_object* v___f_2672_; 
v___f_2672_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2672_, 0, v_x_2669_);
lean_closure_set(v___f_2672_, 1, v_x_2670_);
lean_closure_set(v___f_2672_, 2, v_inst_2671_);
return v___f_2672_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instBEqOfLawfulBEq(lean_object* v_00_u03b1_2673_, lean_object* v_00_u03b2_2674_, lean_object* v_x_2675_, lean_object* v_x_2676_, lean_object* v_inst_2677_, lean_object* v_inst_2678_){
_start:
{
lean_object* v___f_2679_; 
v___f_2679_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2679_, 0, v_x_2675_);
lean_closure_set(v___f_2679_, 1, v_x_2676_);
lean_closure_set(v___f_2679_, 2, v_inst_2678_);
return v___f_2679_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___redArg(lean_object* v_inst_2680_, lean_object* v_inst_2681_, lean_object* v_inst_2682_, lean_object* v_x_2683_, lean_object* v_x_2684_){
_start:
{
uint8_t v___x_2685_; 
v___x_2685_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_inst_2680_, v_inst_2681_, v_inst_2682_, v_x_2683_, v_x_2684_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___redArg___boxed(lean_object* v_inst_2686_, lean_object* v_inst_2687_, lean_object* v_inst_2688_, lean_object* v_x_2689_, lean_object* v_x_2690_){
_start:
{
uint8_t v_res_2691_; lean_object* v_r_2692_; 
v_res_2691_ = l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___redArg(v_inst_2686_, v_inst_2687_, v_inst_2688_, v_x_2689_, v_x_2690_);
v_r_2692_ = lean_box(v_res_2691_);
return v_r_2692_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq(lean_object* v_00_u03b1_2693_, lean_object* v_00_u03b2_2694_, lean_object* v_inst_2695_, lean_object* v_inst_2696_, lean_object* v_inst_2697_, lean_object* v_inst_2698_, lean_object* v_inst_2699_, lean_object* v_x_2700_, lean_object* v_x_2701_){
_start:
{
uint8_t v___x_2702_; 
v___x_2702_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_inst_2695_, v_inst_2697_, v_inst_2698_, v_x_2700_, v_x_2701_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___boxed(lean_object* v_00_u03b1_2703_, lean_object* v_00_u03b2_2704_, lean_object* v_inst_2705_, lean_object* v_inst_2706_, lean_object* v_inst_2707_, lean_object* v_inst_2708_, lean_object* v_inst_2709_, lean_object* v_x_2710_, lean_object* v_x_2711_){
_start:
{
uint8_t v_res_2712_; lean_object* v_r_2713_; 
v_res_2712_ = l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq(v_00_u03b1_2703_, v_00_u03b2_2704_, v_inst_2705_, v_inst_2706_, v_inst_2707_, v_inst_2708_, v_inst_2709_, v_x_2710_, v_x_2711_);
v_r_2713_ = lean_box(v_res_2712_);
return v_r_2713_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_Const_beq___redArg(lean_object* v_x_2714_, lean_object* v_x_2715_, lean_object* v_inst_2716_, lean_object* v_m_u2081_2717_, lean_object* v_m_u2082_2718_){
_start:
{
uint8_t v___x_2719_; 
v___x_2719_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_x_2714_, v_x_2715_, v_inst_2716_, v_m_u2081_2717_, v_m_u2082_2718_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_beq___redArg___boxed(lean_object* v_x_2720_, lean_object* v_x_2721_, lean_object* v_inst_2722_, lean_object* v_m_u2081_2723_, lean_object* v_m_u2082_2724_){
_start:
{
uint8_t v_res_2725_; lean_object* v_r_2726_; 
v_res_2725_ = l_Std_ExtDHashMap_Const_beq___redArg(v_x_2720_, v_x_2721_, v_inst_2722_, v_m_u2081_2723_, v_m_u2082_2724_);
v_r_2726_ = lean_box(v_res_2725_);
return v_r_2726_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_Const_beq(lean_object* v_00_u03b1_2727_, lean_object* v_x_2728_, lean_object* v_x_2729_, lean_object* v_00_u03b2_2730_, lean_object* v_inst_2731_, lean_object* v_inst_2732_, lean_object* v_inst_2733_, lean_object* v_m_u2081_2734_, lean_object* v_m_u2082_2735_){
_start:
{
uint8_t v___x_2736_; 
v___x_2736_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_x_2728_, v_x_2729_, v_inst_2733_, v_m_u2081_2734_, v_m_u2082_2735_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_beq___boxed(lean_object* v_00_u03b1_2737_, lean_object* v_x_2738_, lean_object* v_x_2739_, lean_object* v_00_u03b2_2740_, lean_object* v_inst_2741_, lean_object* v_inst_2742_, lean_object* v_inst_2743_, lean_object* v_m_u2081_2744_, lean_object* v_m_u2082_2745_){
_start:
{
uint8_t v_res_2746_; lean_object* v_r_2747_; 
v_res_2746_ = l_Std_ExtDHashMap_Const_beq(v_00_u03b1_2737_, v_x_2738_, v_x_2739_, v_00_u03b2_2740_, v_inst_2741_, v_inst_2742_, v_inst_2743_, v_m_u2081_2744_, v_m_u2082_2745_);
v_r_2747_ = lean_box(v_res_2746_);
return v_r_2747_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_inter___redArg(lean_object* v_x_2748_, lean_object* v_x_2749_, lean_object* v_m_u2081_2750_, lean_object* v_m_u2082_2751_){
_start:
{
lean_object* v___x_2752_; 
v___x_2752_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_x_2748_, v_x_2749_, v_m_u2081_2750_, v_m_u2082_2751_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_inter(lean_object* v_00_u03b1_2753_, lean_object* v_00_u03b2_2754_, lean_object* v_x_2755_, lean_object* v_x_2756_, lean_object* v_inst_2757_, lean_object* v_inst_2758_, lean_object* v_m_u2081_2759_, lean_object* v_m_u2082_2760_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_x_2755_, v_x_2756_, v_m_u2081_2759_, v_m_u2082_2760_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInterOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_2762_, lean_object* v_x_2763_){
_start:
{
lean_object* v___x_2764_; 
v___x_2764_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_inter), 8, 6);
lean_closure_set(v___x_2764_, 0, lean_box(0));
lean_closure_set(v___x_2764_, 1, lean_box(0));
lean_closure_set(v___x_2764_, 2, v_x_2762_);
lean_closure_set(v___x_2764_, 3, v_x_2763_);
lean_closure_set(v___x_2764_, 4, lean_box(0));
lean_closure_set(v___x_2764_, 5, lean_box(0));
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInterOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_2765_, lean_object* v_00_u03b2_2766_, lean_object* v_x_2767_, lean_object* v_x_2768_, lean_object* v_inst_2769_, lean_object* v_inst_2770_){
_start:
{
lean_object* v___x_2771_; 
v___x_2771_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_inter), 8, 6);
lean_closure_set(v___x_2771_, 0, lean_box(0));
lean_closure_set(v___x_2771_, 1, lean_box(0));
lean_closure_set(v___x_2771_, 2, v_x_2767_);
lean_closure_set(v___x_2771_, 3, v_x_2768_);
lean_closure_set(v___x_2771_, 4, lean_box(0));
lean_closure_set(v___x_2771_, 5, lean_box(0));
return v___x_2771_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_diff___redArg___lam__0(lean_object* v_x_2772_, lean_object* v_x_2773_, lean_object* v_m_u2082_2774_, uint8_t v___x_2775_, lean_object* v_k_2776_, lean_object* v_x_2777_){
_start:
{
uint8_t v___x_2778_; 
v___x_2778_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_2772_, v_x_2773_, v_m_u2082_2774_, v_k_2776_);
if (v___x_2778_ == 0)
{
return v___x_2775_;
}
else
{
uint8_t v___x_2779_; 
v___x_2779_ = 0;
return v___x_2779_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_diff___redArg___lam__0___boxed(lean_object* v_x_2780_, lean_object* v_x_2781_, lean_object* v_m_u2082_2782_, lean_object* v___x_2783_, lean_object* v_k_2784_, lean_object* v_x_2785_){
_start:
{
uint8_t v___x_108__boxed_2786_; uint8_t v_res_2787_; lean_object* v_r_2788_; 
v___x_108__boxed_2786_ = lean_unbox(v___x_2783_);
v_res_2787_ = l_Std_ExtDHashMap_diff___redArg___lam__0(v_x_2780_, v_x_2781_, v_m_u2082_2782_, v___x_108__boxed_2786_, v_k_2784_, v_x_2785_);
lean_dec(v_x_2785_);
lean_dec(v_m_u2082_2782_);
v_r_2788_ = lean_box(v_res_2787_);
return v_r_2788_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_diff___redArg(lean_object* v_x_2789_, lean_object* v_x_2790_, lean_object* v_m_u2081_2791_, lean_object* v_m_u2082_2792_){
_start:
{
lean_object* v_size_2793_; lean_object* v_size_2794_; uint8_t v___x_2795_; 
v_size_2793_ = lean_ctor_get(v_m_u2081_2791_, 0);
v_size_2794_ = lean_ctor_get(v_m_u2082_2792_, 0);
v___x_2795_ = lean_nat_dec_le(v_size_2793_, v_size_2794_);
if (v___x_2795_ == 0)
{
lean_object* v___f_2796_; lean_object* v___x_2797_; 
v___f_2796_ = ((lean_object*)(l_Std_ExtDHashMap_union___redArg___closed__10));
v___x_2797_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_2796_, v_x_2789_, v_x_2790_, v_m_u2081_2791_, v_m_u2082_2792_);
return v___x_2797_;
}
else
{
lean_object* v___x_2798_; lean_object* v___f_2799_; lean_object* v___x_2800_; 
v___x_2798_ = lean_box(v___x_2795_);
v___f_2799_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_2799_, 0, v_x_2789_);
lean_closure_set(v___f_2799_, 1, v_x_2790_);
lean_closure_set(v___f_2799_, 2, v_m_u2082_2792_);
lean_closure_set(v___f_2799_, 3, v___x_2798_);
v___x_2800_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2799_, v_m_u2081_2791_);
lean_dec(v_m_u2081_2791_);
return v___x_2800_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_diff(lean_object* v_00_u03b1_2801_, lean_object* v_00_u03b2_2802_, lean_object* v_x_2803_, lean_object* v_x_2804_, lean_object* v_inst_2805_, lean_object* v_inst_2806_, lean_object* v_m_u2081_2807_, lean_object* v_m_u2082_2808_){
_start:
{
lean_object* v_size_2809_; lean_object* v_size_2810_; uint8_t v___x_2811_; 
v_size_2809_ = lean_ctor_get(v_m_u2081_2807_, 0);
v_size_2810_ = lean_ctor_get(v_m_u2082_2808_, 0);
v___x_2811_ = lean_nat_dec_le(v_size_2809_, v_size_2810_);
if (v___x_2811_ == 0)
{
lean_object* v___f_2812_; lean_object* v___x_2813_; 
v___f_2812_ = ((lean_object*)(l_Std_ExtDHashMap_union___redArg___closed__10));
v___x_2813_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_2812_, v_x_2803_, v_x_2804_, v_m_u2081_2807_, v_m_u2082_2808_);
return v___x_2813_;
}
else
{
lean_object* v___x_2814_; lean_object* v___f_2815_; lean_object* v___x_2816_; 
v___x_2814_ = lean_box(v___x_2811_);
v___f_2815_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_2815_, 0, v_x_2803_);
lean_closure_set(v___f_2815_, 1, v_x_2804_);
lean_closure_set(v___f_2815_, 2, v_m_u2082_2808_);
lean_closure_set(v___f_2815_, 3, v___x_2814_);
v___x_2816_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2815_, v_m_u2081_2807_);
lean_dec(v_m_u2081_2807_);
return v___x_2816_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instSDiffOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_2817_, lean_object* v_x_2818_){
_start:
{
lean_object* v___x_2819_; 
v___x_2819_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_diff), 8, 6);
lean_closure_set(v___x_2819_, 0, lean_box(0));
lean_closure_set(v___x_2819_, 1, lean_box(0));
lean_closure_set(v___x_2819_, 2, v_x_2817_);
lean_closure_set(v___x_2819_, 3, v_x_2818_);
lean_closure_set(v___x_2819_, 4, lean_box(0));
lean_closure_set(v___x_2819_, 5, lean_box(0));
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instSDiffOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_2820_, lean_object* v_00_u03b2_2821_, lean_object* v_x_2822_, lean_object* v_x_2823_, lean_object* v_inst_2824_, lean_object* v_inst_2825_){
_start:
{
lean_object* v___x_2826_; 
v___x_2826_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_diff), 8, 6);
lean_closure_set(v___x_2826_, 0, lean_box(0));
lean_closure_set(v___x_2826_, 1, lean_box(0));
lean_closure_set(v___x_2826_, 2, v_x_2822_);
lean_closure_set(v___x_2826_, 3, v_x_2823_);
lean_closure_set(v___x_2826_, 4, lean_box(0));
lean_closure_set(v___x_2826_, 5, lean_box(0));
return v___x_2826_;
}
}
static lean_object* _init_l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__2(void){
_start:
{
lean_object* v_cellCount_2831_; lean_object* v___x_2832_; 
v_cellCount_2831_ = lean_unsigned_to_nat(16u);
v___x_2832_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2831_);
return v___x_2832_;
}
}
static lean_object* _init_l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__3(void){
_start:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2833_ = lean_obj_once(&l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__2, &l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__2_once, _init_l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__2);
v___x_2834_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___closed__0, &l_Std_ExtDHashMap_instEmptyCollection___closed__0_once, _init_l_Std_ExtDHashMap_instEmptyCollection___closed__0);
v___x_2835_ = lean_unsigned_to_nat(0u);
v___x_2836_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2835_);
lean_ctor_set(v___x_2836_, 1, v___x_2834_);
lean_ctor_set(v___x_2836_, 2, v___x_2833_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_unitOfArray___redArg(lean_object* v_inst_2837_, lean_object* v_inst_2838_, lean_object* v_l_2839_){
_start:
{
lean_object* v___f_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___f_2840_ = ((lean_object*)(l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__1));
v___x_2841_ = lean_obj_once(&l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__3, &l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__3_once, _init_l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__3);
v___x_2842_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2840_, v_inst_2837_, v_inst_2838_, v___x_2841_, v_l_2839_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_unitOfArray(lean_object* v_00_u03b1_2843_, lean_object* v_inst_2844_, lean_object* v_inst_2845_, lean_object* v_l_2846_){
_start:
{
lean_object* v___f_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___f_2847_ = ((lean_object*)(l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__1));
v___x_2848_ = lean_obj_once(&l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__3, &l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__3_once, _init_l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__3);
v___x_2849_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2847_, v_inst_2844_, v_inst_2845_, v___x_2848_, v_l_2846_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_ofList___redArg(lean_object* v_inst_2854_, lean_object* v_inst_2855_, lean_object* v_l_2856_){
_start:
{
lean_object* v___f_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___f_2857_ = ((lean_object*)(l_Std_ExtDHashMap_ofList___redArg___closed__1));
v___x_2858_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___closed__2, &l_Std_ExtDHashMap_instEmptyCollection___closed__2_once, _init_l_Std_ExtDHashMap_instEmptyCollection___closed__2);
v___x_2859_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_2857_, v_inst_2854_, v_inst_2855_, v___x_2858_, v_l_2856_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_ofList(lean_object* v_00_u03b1_2860_, lean_object* v_00_u03b2_2861_, lean_object* v_inst_2862_, lean_object* v_inst_2863_, lean_object* v_l_2864_){
_start:
{
lean_object* v___f_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___f_2865_ = ((lean_object*)(l_Std_ExtDHashMap_ofList___redArg___closed__1));
v___x_2866_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___closed__2, &l_Std_ExtDHashMap_instEmptyCollection___closed__2_once, _init_l_Std_ExtDHashMap_instEmptyCollection___closed__2);
v___x_2867_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_2865_, v_inst_2862_, v_inst_2863_, v___x_2866_, v_l_2864_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_ofList___redArg(lean_object* v_inst_2868_, lean_object* v_inst_2869_, lean_object* v_l_2870_){
_start:
{
lean_object* v___f_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___f_2871_ = ((lean_object*)(l_Std_ExtDHashMap_ofList___redArg___closed__1));
v___x_2872_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___closed__2, &l_Std_ExtDHashMap_instEmptyCollection___closed__2_once, _init_l_Std_ExtDHashMap_instEmptyCollection___closed__2);
v___x_2873_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_2871_, v_inst_2868_, v_inst_2869_, v___x_2872_, v_l_2870_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_ofList(lean_object* v_00_u03b1_2874_, lean_object* v_00_u03b2_2875_, lean_object* v_inst_2876_, lean_object* v_inst_2877_, lean_object* v_l_2878_){
_start:
{
lean_object* v___f_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___f_2879_ = ((lean_object*)(l_Std_ExtDHashMap_ofList___redArg___closed__1));
v___x_2880_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___closed__2, &l_Std_ExtDHashMap_instEmptyCollection___closed__2_once, _init_l_Std_ExtDHashMap_instEmptyCollection___closed__2);
v___x_2881_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_2879_, v_inst_2876_, v_inst_2877_, v___x_2880_, v_l_2878_);
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_unitOfList___redArg(lean_object* v_inst_2882_, lean_object* v_inst_2883_, lean_object* v_l_2884_){
_start:
{
lean_object* v___f_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___f_2885_ = ((lean_object*)(l_Std_ExtDHashMap_ofList___redArg___closed__1));
v___x_2886_ = lean_obj_once(&l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__3, &l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__3_once, _init_l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__3);
v___x_2887_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2885_, v_inst_2882_, v_inst_2883_, v___x_2886_, v_l_2884_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_unitOfList(lean_object* v_00_u03b1_2888_, lean_object* v_inst_2889_, lean_object* v_inst_2890_, lean_object* v_l_2891_){
_start:
{
lean_object* v___f_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___f_2892_ = ((lean_object*)(l_Std_ExtDHashMap_ofList___redArg___closed__1));
v___x_2893_ = lean_obj_once(&l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__3, &l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__3_once, _init_l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__3);
v___x_2894_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2892_, v_inst_2889_, v_inst_2890_, v___x_2893_, v_l_2891_);
return v___x_2894_;
}
}
lean_object* runtime_initialize_Std_Data_DHashMap_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_ExtDHashMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_DHashMap_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_ExtDHashMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DHashMap_Lemmas(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_ExtDHashMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DHashMap_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_ExtDHashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_ExtDHashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_ExtDHashMap_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
