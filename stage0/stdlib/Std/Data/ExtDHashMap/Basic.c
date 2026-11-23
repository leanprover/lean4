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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
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
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instForInOfForIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__0;
static lean_once_cell_t l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instEmptyCollection___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_ExtDHashMap_instEmptyCollection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtDHashMap_instEmptyCollection___closed__0;
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instEmptyCollection(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInhabited___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_ExtDHashMap_instInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtDHashMap_instInhabited___closed__0;
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInhabited___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable___redArg();
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filterMap___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_union___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Std_ExtDHashMap_union___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_ExtDHashMap_union___redArg___closed__9_value)} };
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
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_82_ = lean_unsigned_to_nat(0u);
v___x_83_ = lean_unsigned_to_nat(4u);
v___x_84_ = lean_nat_mul(v_capacity_81_, v___x_83_);
v___x_85_ = lean_unsigned_to_nat(3u);
v___x_86_ = lean_nat_div(v___x_84_, v___x_85_);
lean_dec(v___x_84_);
v___x_87_ = l_Nat_nextPowerOfTwo(v___x_86_);
lean_dec(v___x_86_);
v___x_88_ = lean_box(0);
v___x_89_ = lean_mk_array(v___x_87_, v___x_88_);
v___x_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_82_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_emptyWithCapacity___redArg___boxed(lean_object* v_capacity_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Std_ExtDHashMap_emptyWithCapacity___redArg(v_capacity_91_);
lean_dec(v_capacity_91_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_emptyWithCapacity(lean_object* v_00_u03b1_93_, lean_object* v_00_u03b2_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_capacity_97_){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = lean_unsigned_to_nat(4u);
v___x_100_ = lean_nat_mul(v_capacity_97_, v___x_99_);
v___x_101_ = lean_unsigned_to_nat(3u);
v___x_102_ = lean_nat_div(v___x_100_, v___x_101_);
lean_dec(v___x_100_);
v___x_103_ = l_Nat_nextPowerOfTwo(v___x_102_);
lean_dec(v___x_102_);
v___x_104_ = lean_box(0);
v___x_105_ = lean_mk_array(v___x_103_, v___x_104_);
v___x_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_98_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_emptyWithCapacity___boxed(lean_object* v_00_u03b1_107_, lean_object* v_00_u03b2_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_capacity_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Std_ExtDHashMap_emptyWithCapacity(v_00_u03b1_107_, v_00_u03b2_108_, v_inst_109_, v_inst_110_, v_capacity_111_);
lean_dec(v_capacity_111_);
lean_dec_ref(v_inst_110_);
lean_dec_ref(v_inst_109_);
return v_res_112_;
}
}
static lean_object* _init_l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__0(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_113_ = lean_box(0);
v___x_114_ = lean_unsigned_to_nat(16u);
v___x_115_ = lean_mk_array(v___x_114_, v___x_113_);
return v___x_115_;
}
}
static lean_object* _init_l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_116_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__0, &l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__0_once, _init_l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__0);
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v___x_116_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instEmptyCollection___redArg___boxed(lean_object* v___dummy_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Std_ExtDHashMap_instEmptyCollection___redArg();
return v_res_122_;
}
}
static lean_object* _init_l_Std_ExtDHashMap_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Std_ExtDHashMap_instEmptyCollection___redArg();
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instEmptyCollection(lean_object* v_00_u03b1_124_, lean_object* v_00_u03b2_125_, lean_object* v_inst_126_, lean_object* v_inst_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___closed__0, &l_Std_ExtDHashMap_instEmptyCollection___closed__0_once, _init_l_Std_ExtDHashMap_instEmptyCollection___closed__0);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instEmptyCollection___boxed(lean_object* v_00_u03b1_129_, lean_object* v_00_u03b2_130_, lean_object* v_inst_131_, lean_object* v_inst_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Std_ExtDHashMap_instEmptyCollection(v_00_u03b1_129_, v_00_u03b2_130_, v_inst_131_, v_inst_132_);
lean_dec_ref(v_inst_132_);
lean_dec_ref(v_inst_131_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInhabited___redArg(){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInhabited___redArg___boxed(lean_object* v___dummy_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Std_ExtDHashMap_instInhabited___redArg();
return v_res_137_;
}
}
static lean_object* _init_l_Std_ExtDHashMap_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Std_ExtDHashMap_instInhabited___redArg();
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInhabited(lean_object* v_00_u03b1_139_, lean_object* v_00_u03b2_140_, lean_object* v_inst_141_, lean_object* v_inst_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lean_obj_once(&l_Std_ExtDHashMap_instInhabited___closed__0, &l_Std_ExtDHashMap_instInhabited___closed__0_once, _init_l_Std_ExtDHashMap_instInhabited___closed__0);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInhabited___boxed(lean_object* v_00_u03b1_144_, lean_object* v_00_u03b2_145_, lean_object* v_inst_146_, lean_object* v_inst_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Std_ExtDHashMap_instInhabited(v_00_u03b1_144_, v_00_u03b2_145_, v_inst_146_, v_inst_147_);
lean_dec_ref(v_inst_147_);
lean_dec_ref(v_inst_146_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insert___redArg(lean_object* v_x_149_, lean_object* v_x_150_, lean_object* v_m_151_, lean_object* v_a_152_, lean_object* v_b_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_149_, v_x_150_, v_m_151_, v_a_152_, v_b_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insert(lean_object* v_00_u03b1_155_, lean_object* v_00_u03b2_156_, lean_object* v_x_157_, lean_object* v_x_158_, lean_object* v_inst_159_, lean_object* v_inst_160_, lean_object* v_m_161_, lean_object* v_a_162_, lean_object* v_b_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_157_, v_x_158_, v_m_161_, v_a_162_, v_b_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_165_, lean_object* v_x_166_, lean_object* v_x_167_){
_start:
{
lean_object* v_fst_168_; lean_object* v_snd_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v_fst_168_ = lean_ctor_get(v_x_167_, 0);
lean_inc(v_fst_168_);
v_snd_169_ = lean_ctor_get(v_x_167_, 1);
lean_inc(v_snd_169_);
lean_dec_ref(v_x_167_);
v___x_170_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1);
v___x_171_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_165_, v_x_166_, v___x_170_, v_fst_168_, v_snd_169_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_172_, lean_object* v_x_173_){
_start:
{
lean_object* v___f_174_; 
v___f_174_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_174_, 0, v_x_172_);
lean_closure_set(v___f_174_, 1, v_x_173_);
return v___f_174_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_175_, lean_object* v_00_u03b2_176_, lean_object* v_x_177_, lean_object* v_x_178_, lean_object* v_inst_179_, lean_object* v_inst_180_){
_start:
{
lean_object* v___f_181_; 
v___f_181_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_181_, 0, v_x_177_);
lean_closure_set(v___f_181_, 1, v_x_178_);
return v___f_181_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_182_, lean_object* v_x_183_, lean_object* v_x_184_, lean_object* v_x_185_){
_start:
{
lean_object* v_fst_186_; lean_object* v_snd_187_; lean_object* v___x_188_; 
v_fst_186_ = lean_ctor_get(v_x_184_, 0);
lean_inc(v_fst_186_);
v_snd_187_ = lean_ctor_get(v_x_184_, 1);
lean_inc(v_snd_187_);
lean_dec_ref(v_x_184_);
v___x_188_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_182_, v_x_183_, v_x_185_, v_fst_186_, v_snd_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_189_, lean_object* v_x_190_){
_start:
{
lean_object* v___f_191_; 
v___f_191_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_191_, 0, v_x_189_);
lean_closure_set(v___f_191_, 1, v_x_190_);
return v___f_191_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_192_, lean_object* v_00_u03b2_193_, lean_object* v_x_194_, lean_object* v_x_195_, lean_object* v_inst_196_, lean_object* v_inst_197_){
_start:
{
lean_object* v___f_198_; 
v___f_198_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_198_, 0, v_x_194_);
lean_closure_set(v___f_198_, 1, v_x_195_);
return v___f_198_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insertIfNew___redArg(lean_object* v_x_199_, lean_object* v_x_200_, lean_object* v_m_201_, lean_object* v_a_202_, lean_object* v_b_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_199_, v_x_200_, v_m_201_, v_a_202_, v_b_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insertIfNew(lean_object* v_00_u03b1_205_, lean_object* v_00_u03b2_206_, lean_object* v_x_207_, lean_object* v_x_208_, lean_object* v_inst_209_, lean_object* v_inst_210_, lean_object* v_m_211_, lean_object* v_a_212_, lean_object* v_b_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_207_, v_x_208_, v_m_211_, v_a_212_, v_b_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_containsThenInsert___redArg(lean_object* v_x_215_, lean_object* v_x_216_, lean_object* v_m_217_, lean_object* v_a_218_, lean_object* v_b_219_){
_start:
{
lean_object* v_size_220_; lean_object* v_buckets_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_272_; 
v_size_220_ = lean_ctor_get(v_m_217_, 0);
v_buckets_221_ = lean_ctor_get(v_m_217_, 1);
v_isSharedCheck_272_ = !lean_is_exclusive(v_m_217_);
if (v_isSharedCheck_272_ == 0)
{
v___x_223_ = v_m_217_;
v_isShared_224_ = v_isSharedCheck_272_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_buckets_221_);
lean_inc(v_size_220_);
lean_dec(v_m_217_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_272_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_225_; lean_object* v___x_226_; uint64_t v___x_227_; uint64_t v___x_228_; uint64_t v___x_229_; uint64_t v___x_230_; uint64_t v_fold_231_; uint64_t v___x_232_; uint64_t v___x_233_; uint64_t v___x_234_; size_t v___x_235_; size_t v___x_236_; size_t v___x_237_; size_t v___x_238_; size_t v___x_239_; lean_object* v_bkt_240_; uint8_t v___x_241_; 
v___x_225_ = lean_array_get_size(v_buckets_221_);
lean_inc_ref(v_x_216_);
lean_inc_n(v_a_218_, 2);
v___x_226_ = lean_apply_1(v_x_216_, v_a_218_);
v___x_227_ = 32ULL;
v___x_228_ = lean_unbox_uint64(v___x_226_);
v___x_229_ = lean_uint64_shift_right(v___x_228_, v___x_227_);
v___x_230_ = lean_unbox_uint64(v___x_226_);
lean_dec_ref(v___x_226_);
v_fold_231_ = lean_uint64_xor(v___x_230_, v___x_229_);
v___x_232_ = 16ULL;
v___x_233_ = lean_uint64_shift_right(v_fold_231_, v___x_232_);
v___x_234_ = lean_uint64_xor(v_fold_231_, v___x_233_);
v___x_235_ = lean_uint64_to_usize(v___x_234_);
v___x_236_ = lean_usize_of_nat(v___x_225_);
v___x_237_ = ((size_t)1ULL);
v___x_238_ = lean_usize_sub(v___x_236_, v___x_237_);
v___x_239_ = lean_usize_land(v___x_235_, v___x_238_);
v_bkt_240_ = lean_array_uget_borrowed(v_buckets_221_, v___x_239_);
lean_inc(v_bkt_240_);
lean_inc_ref(v_x_215_);
v___x_241_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_215_, v_a_218_, v_bkt_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; lean_object* v_size_x27_243_; lean_object* v___x_244_; lean_object* v_buckets_x27_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
lean_dec_ref(v_x_215_);
v___x_242_ = lean_unsigned_to_nat(1u);
v_size_x27_243_ = lean_nat_add(v_size_220_, v___x_242_);
lean_dec(v_size_220_);
lean_inc(v_bkt_240_);
v___x_244_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_244_, 0, v_a_218_);
lean_ctor_set(v___x_244_, 1, v_b_219_);
lean_ctor_set(v___x_244_, 2, v_bkt_240_);
v_buckets_x27_245_ = lean_array_uset(v_buckets_221_, v___x_239_, v___x_244_);
v___x_246_ = lean_unsigned_to_nat(4u);
v___x_247_ = lean_nat_mul(v_size_x27_243_, v___x_246_);
v___x_248_ = lean_unsigned_to_nat(3u);
v___x_249_ = lean_nat_div(v___x_247_, v___x_248_);
lean_dec(v___x_247_);
v___x_250_ = lean_array_get_size(v_buckets_x27_245_);
v___x_251_ = lean_nat_dec_le(v___x_249_, v___x_250_);
lean_dec(v___x_249_);
if (v___x_251_ == 0)
{
lean_object* v_val_252_; lean_object* v___x_254_; 
v_val_252_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_216_, v_buckets_x27_245_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v_val_252_);
lean_ctor_set(v___x_223_, 0, v_size_x27_243_);
v___x_254_ = v___x_223_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_size_x27_243_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_val_252_);
v___x_254_ = v_reuseFailAlloc_257_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = lean_box(v___x_241_);
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
lean_ctor_set(v___x_256_, 1, v___x_254_);
return v___x_256_;
}
}
else
{
lean_object* v___x_259_; 
lean_dec_ref(v_x_216_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v_buckets_x27_245_);
lean_ctor_set(v___x_223_, 0, v_size_x27_243_);
v___x_259_ = v___x_223_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_size_x27_243_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_buckets_x27_245_);
v___x_259_ = v_reuseFailAlloc_262_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_box(v___x_241_);
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v___x_259_);
return v___x_261_;
}
}
}
else
{
lean_object* v___x_263_; lean_object* v_buckets_x27_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_268_; 
lean_inc(v_bkt_240_);
lean_dec_ref(v_x_216_);
v___x_263_ = lean_box(0);
v_buckets_x27_264_ = lean_array_uset(v_buckets_221_, v___x_239_, v___x_263_);
v___x_265_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_x_215_, v_a_218_, v_b_219_, v_bkt_240_);
v___x_266_ = lean_array_uset(v_buckets_x27_264_, v___x_239_, v___x_265_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v___x_266_);
v___x_268_ = v___x_223_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_size_220_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v___x_266_);
v___x_268_ = v_reuseFailAlloc_271_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = lean_box(v___x_241_);
v___x_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v___x_268_);
return v___x_270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_containsThenInsert(lean_object* v_00_u03b1_273_, lean_object* v_00_u03b2_274_, lean_object* v_x_275_, lean_object* v_x_276_, lean_object* v_inst_277_, lean_object* v_inst_278_, lean_object* v_m_279_, lean_object* v_a_280_, lean_object* v_b_281_){
_start:
{
lean_object* v_size_282_; lean_object* v_buckets_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_334_; 
v_size_282_ = lean_ctor_get(v_m_279_, 0);
v_buckets_283_ = lean_ctor_get(v_m_279_, 1);
v_isSharedCheck_334_ = !lean_is_exclusive(v_m_279_);
if (v_isSharedCheck_334_ == 0)
{
v___x_285_ = v_m_279_;
v_isShared_286_ = v_isSharedCheck_334_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_buckets_283_);
lean_inc(v_size_282_);
lean_dec(v_m_279_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_334_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_287_; lean_object* v___x_288_; uint64_t v___x_289_; uint64_t v___x_290_; uint64_t v___x_291_; uint64_t v___x_292_; uint64_t v_fold_293_; uint64_t v___x_294_; uint64_t v___x_295_; uint64_t v___x_296_; size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; size_t v___x_300_; size_t v___x_301_; lean_object* v_bkt_302_; uint8_t v___x_303_; 
v___x_287_ = lean_array_get_size(v_buckets_283_);
lean_inc_ref(v_x_276_);
lean_inc_n(v_a_280_, 2);
v___x_288_ = lean_apply_1(v_x_276_, v_a_280_);
v___x_289_ = 32ULL;
v___x_290_ = lean_unbox_uint64(v___x_288_);
v___x_291_ = lean_uint64_shift_right(v___x_290_, v___x_289_);
v___x_292_ = lean_unbox_uint64(v___x_288_);
lean_dec_ref(v___x_288_);
v_fold_293_ = lean_uint64_xor(v___x_292_, v___x_291_);
v___x_294_ = 16ULL;
v___x_295_ = lean_uint64_shift_right(v_fold_293_, v___x_294_);
v___x_296_ = lean_uint64_xor(v_fold_293_, v___x_295_);
v___x_297_ = lean_uint64_to_usize(v___x_296_);
v___x_298_ = lean_usize_of_nat(v___x_287_);
v___x_299_ = ((size_t)1ULL);
v___x_300_ = lean_usize_sub(v___x_298_, v___x_299_);
v___x_301_ = lean_usize_land(v___x_297_, v___x_300_);
v_bkt_302_ = lean_array_uget_borrowed(v_buckets_283_, v___x_301_);
lean_inc(v_bkt_302_);
lean_inc_ref(v_x_275_);
v___x_303_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_275_, v_a_280_, v_bkt_302_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; lean_object* v_size_x27_305_; lean_object* v___x_306_; lean_object* v_buckets_x27_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
lean_dec_ref(v_x_275_);
v___x_304_ = lean_unsigned_to_nat(1u);
v_size_x27_305_ = lean_nat_add(v_size_282_, v___x_304_);
lean_dec(v_size_282_);
lean_inc(v_bkt_302_);
v___x_306_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_306_, 0, v_a_280_);
lean_ctor_set(v___x_306_, 1, v_b_281_);
lean_ctor_set(v___x_306_, 2, v_bkt_302_);
v_buckets_x27_307_ = lean_array_uset(v_buckets_283_, v___x_301_, v___x_306_);
v___x_308_ = lean_unsigned_to_nat(4u);
v___x_309_ = lean_nat_mul(v_size_x27_305_, v___x_308_);
v___x_310_ = lean_unsigned_to_nat(3u);
v___x_311_ = lean_nat_div(v___x_309_, v___x_310_);
lean_dec(v___x_309_);
v___x_312_ = lean_array_get_size(v_buckets_x27_307_);
v___x_313_ = lean_nat_dec_le(v___x_311_, v___x_312_);
lean_dec(v___x_311_);
if (v___x_313_ == 0)
{
lean_object* v_val_314_; lean_object* v___x_316_; 
v_val_314_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_276_, v_buckets_x27_307_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 1, v_val_314_);
lean_ctor_set(v___x_285_, 0, v_size_x27_305_);
v___x_316_ = v___x_285_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_size_x27_305_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_val_314_);
v___x_316_ = v_reuseFailAlloc_319_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_box(v___x_303_);
v___x_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v___x_316_);
return v___x_318_;
}
}
else
{
lean_object* v___x_321_; 
lean_dec_ref(v_x_276_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 1, v_buckets_x27_307_);
lean_ctor_set(v___x_285_, 0, v_size_x27_305_);
v___x_321_ = v___x_285_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_size_x27_305_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_buckets_x27_307_);
v___x_321_ = v_reuseFailAlloc_324_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = lean_box(v___x_303_);
v___x_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v___x_321_);
return v___x_323_;
}
}
}
else
{
lean_object* v___x_325_; lean_object* v_buckets_x27_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_330_; 
lean_inc(v_bkt_302_);
lean_dec_ref(v_x_276_);
v___x_325_ = lean_box(0);
v_buckets_x27_326_ = lean_array_uset(v_buckets_283_, v___x_301_, v___x_325_);
v___x_327_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_x_275_, v_a_280_, v_b_281_, v_bkt_302_);
v___x_328_ = lean_array_uset(v_buckets_x27_326_, v___x_301_, v___x_327_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 1, v___x_328_);
v___x_330_ = v___x_285_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_size_282_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v___x_328_);
v___x_330_ = v_reuseFailAlloc_333_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_box(v___x_303_);
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v___x_330_);
return v___x_332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_containsThenInsertIfNew___redArg(lean_object* v_x_335_, lean_object* v_x_336_, lean_object* v_m_337_, lean_object* v_a_338_, lean_object* v_b_339_){
_start:
{
lean_object* v_size_340_; lean_object* v_buckets_341_; lean_object* v___x_342_; lean_object* v___x_343_; uint64_t v___x_344_; uint64_t v___x_345_; uint64_t v___x_346_; uint64_t v___x_347_; uint64_t v_fold_348_; uint64_t v___x_349_; uint64_t v___x_350_; uint64_t v___x_351_; size_t v___x_352_; size_t v___x_353_; size_t v___x_354_; size_t v___x_355_; size_t v___x_356_; lean_object* v_bkt_357_; uint8_t v___x_358_; 
v_size_340_ = lean_ctor_get(v_m_337_, 0);
v_buckets_341_ = lean_ctor_get(v_m_337_, 1);
v___x_342_ = lean_array_get_size(v_buckets_341_);
lean_inc_ref(v_x_336_);
lean_inc_n(v_a_338_, 2);
v___x_343_ = lean_apply_1(v_x_336_, v_a_338_);
v___x_344_ = 32ULL;
v___x_345_ = lean_unbox_uint64(v___x_343_);
v___x_346_ = lean_uint64_shift_right(v___x_345_, v___x_344_);
v___x_347_ = lean_unbox_uint64(v___x_343_);
lean_dec_ref(v___x_343_);
v_fold_348_ = lean_uint64_xor(v___x_347_, v___x_346_);
v___x_349_ = 16ULL;
v___x_350_ = lean_uint64_shift_right(v_fold_348_, v___x_349_);
v___x_351_ = lean_uint64_xor(v_fold_348_, v___x_350_);
v___x_352_ = lean_uint64_to_usize(v___x_351_);
v___x_353_ = lean_usize_of_nat(v___x_342_);
v___x_354_ = ((size_t)1ULL);
v___x_355_ = lean_usize_sub(v___x_353_, v___x_354_);
v___x_356_ = lean_usize_land(v___x_352_, v___x_355_);
v_bkt_357_ = lean_array_uget_borrowed(v_buckets_341_, v___x_356_);
lean_inc(v_bkt_357_);
v___x_358_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_335_, v_a_338_, v_bkt_357_);
if (v___x_358_ == 0)
{
lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_383_; 
lean_inc_ref(v_buckets_341_);
lean_inc(v_size_340_);
v_isSharedCheck_383_ = !lean_is_exclusive(v_m_337_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; lean_object* v_unused_385_; 
v_unused_384_ = lean_ctor_get(v_m_337_, 1);
lean_dec(v_unused_384_);
v_unused_385_ = lean_ctor_get(v_m_337_, 0);
lean_dec(v_unused_385_);
v___x_360_ = v_m_337_;
v_isShared_361_ = v_isSharedCheck_383_;
goto v_resetjp_359_;
}
else
{
lean_dec(v_m_337_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_383_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v_size_x27_363_; lean_object* v___x_364_; lean_object* v_buckets_x27_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_362_ = lean_unsigned_to_nat(1u);
v_size_x27_363_ = lean_nat_add(v_size_340_, v___x_362_);
lean_dec(v_size_340_);
lean_inc(v_bkt_357_);
v___x_364_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_364_, 0, v_a_338_);
lean_ctor_set(v___x_364_, 1, v_b_339_);
lean_ctor_set(v___x_364_, 2, v_bkt_357_);
v_buckets_x27_365_ = lean_array_uset(v_buckets_341_, v___x_356_, v___x_364_);
v___x_366_ = lean_unsigned_to_nat(4u);
v___x_367_ = lean_nat_mul(v_size_x27_363_, v___x_366_);
v___x_368_ = lean_unsigned_to_nat(3u);
v___x_369_ = lean_nat_div(v___x_367_, v___x_368_);
lean_dec(v___x_367_);
v___x_370_ = lean_array_get_size(v_buckets_x27_365_);
v___x_371_ = lean_nat_dec_le(v___x_369_, v___x_370_);
lean_dec(v___x_369_);
if (v___x_371_ == 0)
{
lean_object* v_val_372_; lean_object* v___x_374_; 
v_val_372_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_336_, v_buckets_x27_365_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 1, v_val_372_);
lean_ctor_set(v___x_360_, 0, v_size_x27_363_);
v___x_374_ = v___x_360_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_size_x27_363_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_val_372_);
v___x_374_ = v_reuseFailAlloc_377_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = lean_box(v___x_358_);
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v___x_374_);
return v___x_376_;
}
}
else
{
lean_object* v___x_379_; 
lean_dec_ref(v_x_336_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 1, v_buckets_x27_365_);
lean_ctor_set(v___x_360_, 0, v_size_x27_363_);
v___x_379_ = v___x_360_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_size_x27_363_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_buckets_x27_365_);
v___x_379_ = v_reuseFailAlloc_382_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_box(v___x_358_);
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v___x_379_);
return v___x_381_;
}
}
}
}
else
{
lean_object* v___x_386_; lean_object* v___x_387_; 
lean_dec(v_b_339_);
lean_dec(v_a_338_);
lean_dec_ref(v_x_336_);
v___x_386_ = lean_box(v___x_358_);
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
lean_ctor_set(v___x_387_, 1, v_m_337_);
return v___x_387_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_containsThenInsertIfNew(lean_object* v_00_u03b1_388_, lean_object* v_00_u03b2_389_, lean_object* v_x_390_, lean_object* v_x_391_, lean_object* v_inst_392_, lean_object* v_inst_393_, lean_object* v_m_394_, lean_object* v_a_395_, lean_object* v_b_396_){
_start:
{
lean_object* v_size_397_; lean_object* v_buckets_398_; lean_object* v___x_399_; lean_object* v___x_400_; uint64_t v___x_401_; uint64_t v___x_402_; uint64_t v___x_403_; uint64_t v___x_404_; uint64_t v_fold_405_; uint64_t v___x_406_; uint64_t v___x_407_; uint64_t v___x_408_; size_t v___x_409_; size_t v___x_410_; size_t v___x_411_; size_t v___x_412_; size_t v___x_413_; lean_object* v_bkt_414_; uint8_t v___x_415_; 
v_size_397_ = lean_ctor_get(v_m_394_, 0);
v_buckets_398_ = lean_ctor_get(v_m_394_, 1);
v___x_399_ = lean_array_get_size(v_buckets_398_);
lean_inc_ref(v_x_391_);
lean_inc_n(v_a_395_, 2);
v___x_400_ = lean_apply_1(v_x_391_, v_a_395_);
v___x_401_ = 32ULL;
v___x_402_ = lean_unbox_uint64(v___x_400_);
v___x_403_ = lean_uint64_shift_right(v___x_402_, v___x_401_);
v___x_404_ = lean_unbox_uint64(v___x_400_);
lean_dec_ref(v___x_400_);
v_fold_405_ = lean_uint64_xor(v___x_404_, v___x_403_);
v___x_406_ = 16ULL;
v___x_407_ = lean_uint64_shift_right(v_fold_405_, v___x_406_);
v___x_408_ = lean_uint64_xor(v_fold_405_, v___x_407_);
v___x_409_ = lean_uint64_to_usize(v___x_408_);
v___x_410_ = lean_usize_of_nat(v___x_399_);
v___x_411_ = ((size_t)1ULL);
v___x_412_ = lean_usize_sub(v___x_410_, v___x_411_);
v___x_413_ = lean_usize_land(v___x_409_, v___x_412_);
v_bkt_414_ = lean_array_uget_borrowed(v_buckets_398_, v___x_413_);
lean_inc(v_bkt_414_);
v___x_415_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_390_, v_a_395_, v_bkt_414_);
if (v___x_415_ == 0)
{
lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_440_; 
lean_inc_ref(v_buckets_398_);
lean_inc(v_size_397_);
v_isSharedCheck_440_ = !lean_is_exclusive(v_m_394_);
if (v_isSharedCheck_440_ == 0)
{
lean_object* v_unused_441_; lean_object* v_unused_442_; 
v_unused_441_ = lean_ctor_get(v_m_394_, 1);
lean_dec(v_unused_441_);
v_unused_442_ = lean_ctor_get(v_m_394_, 0);
lean_dec(v_unused_442_);
v___x_417_ = v_m_394_;
v_isShared_418_ = v_isSharedCheck_440_;
goto v_resetjp_416_;
}
else
{
lean_dec(v_m_394_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_440_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v_size_x27_420_; lean_object* v___x_421_; lean_object* v_buckets_x27_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_419_ = lean_unsigned_to_nat(1u);
v_size_x27_420_ = lean_nat_add(v_size_397_, v___x_419_);
lean_dec(v_size_397_);
lean_inc(v_bkt_414_);
v___x_421_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_421_, 0, v_a_395_);
lean_ctor_set(v___x_421_, 1, v_b_396_);
lean_ctor_set(v___x_421_, 2, v_bkt_414_);
v_buckets_x27_422_ = lean_array_uset(v_buckets_398_, v___x_413_, v___x_421_);
v___x_423_ = lean_unsigned_to_nat(4u);
v___x_424_ = lean_nat_mul(v_size_x27_420_, v___x_423_);
v___x_425_ = lean_unsigned_to_nat(3u);
v___x_426_ = lean_nat_div(v___x_424_, v___x_425_);
lean_dec(v___x_424_);
v___x_427_ = lean_array_get_size(v_buckets_x27_422_);
v___x_428_ = lean_nat_dec_le(v___x_426_, v___x_427_);
lean_dec(v___x_426_);
if (v___x_428_ == 0)
{
lean_object* v_val_429_; lean_object* v___x_431_; 
v_val_429_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_391_, v_buckets_x27_422_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 1, v_val_429_);
lean_ctor_set(v___x_417_, 0, v_size_x27_420_);
v___x_431_ = v___x_417_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_size_x27_420_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_val_429_);
v___x_431_ = v_reuseFailAlloc_434_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_box(v___x_415_);
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
lean_ctor_set(v___x_433_, 1, v___x_431_);
return v___x_433_;
}
}
else
{
lean_object* v___x_436_; 
lean_dec_ref(v_x_391_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 1, v_buckets_x27_422_);
lean_ctor_set(v___x_417_, 0, v_size_x27_420_);
v___x_436_ = v___x_417_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_size_x27_420_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_buckets_x27_422_);
v___x_436_ = v_reuseFailAlloc_439_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_box(v___x_415_);
v___x_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v___x_436_);
return v___x_438_;
}
}
}
}
else
{
lean_object* v___x_443_; lean_object* v___x_444_; 
lean_dec(v_b_396_);
lean_dec(v_a_395_);
lean_dec_ref(v_x_391_);
v___x_443_ = lean_box(v___x_415_);
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v_m_394_);
return v___x_444_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getThenInsertIfNew_x3f___redArg(lean_object* v_x_445_, lean_object* v_x_446_, lean_object* v_m_447_, lean_object* v_a_448_, lean_object* v_b_449_){
_start:
{
lean_object* v_size_450_; lean_object* v_buckets_451_; lean_object* v___x_452_; lean_object* v___x_453_; uint64_t v___x_454_; uint64_t v___x_455_; uint64_t v___x_456_; uint64_t v___x_457_; uint64_t v_fold_458_; uint64_t v___x_459_; uint64_t v___x_460_; uint64_t v___x_461_; size_t v___x_462_; size_t v___x_463_; size_t v___x_464_; size_t v___x_465_; size_t v___x_466_; lean_object* v_bkt_467_; lean_object* v___x_468_; 
v_size_450_ = lean_ctor_get(v_m_447_, 0);
v_buckets_451_ = lean_ctor_get(v_m_447_, 1);
v___x_452_ = lean_array_get_size(v_buckets_451_);
lean_inc_ref(v_x_446_);
lean_inc_n(v_a_448_, 2);
v___x_453_ = lean_apply_1(v_x_446_, v_a_448_);
v___x_454_ = 32ULL;
v___x_455_ = lean_unbox_uint64(v___x_453_);
v___x_456_ = lean_uint64_shift_right(v___x_455_, v___x_454_);
v___x_457_ = lean_unbox_uint64(v___x_453_);
lean_dec_ref(v___x_453_);
v_fold_458_ = lean_uint64_xor(v___x_457_, v___x_456_);
v___x_459_ = 16ULL;
v___x_460_ = lean_uint64_shift_right(v_fold_458_, v___x_459_);
v___x_461_ = lean_uint64_xor(v_fold_458_, v___x_460_);
v___x_462_ = lean_uint64_to_usize(v___x_461_);
v___x_463_ = lean_usize_of_nat(v___x_452_);
v___x_464_ = ((size_t)1ULL);
v___x_465_ = lean_usize_sub(v___x_463_, v___x_464_);
v___x_466_ = lean_usize_land(v___x_462_, v___x_465_);
v_bkt_467_ = lean_array_uget_borrowed(v_buckets_451_, v___x_466_);
lean_inc(v_bkt_467_);
v___x_468_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(v_x_445_, v_a_448_, v_bkt_467_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_491_; 
lean_inc_ref(v_buckets_451_);
lean_inc(v_size_450_);
v_isSharedCheck_491_ = !lean_is_exclusive(v_m_447_);
if (v_isSharedCheck_491_ == 0)
{
lean_object* v_unused_492_; lean_object* v_unused_493_; 
v_unused_492_ = lean_ctor_get(v_m_447_, 1);
lean_dec(v_unused_492_);
v_unused_493_ = lean_ctor_get(v_m_447_, 0);
lean_dec(v_unused_493_);
v___x_470_ = v_m_447_;
v_isShared_471_ = v_isSharedCheck_491_;
goto v_resetjp_469_;
}
else
{
lean_dec(v_m_447_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_491_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; lean_object* v_size_x27_473_; lean_object* v___x_474_; lean_object* v_buckets_x27_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_472_ = lean_unsigned_to_nat(1u);
v_size_x27_473_ = lean_nat_add(v_size_450_, v___x_472_);
lean_dec(v_size_450_);
lean_inc(v_bkt_467_);
v___x_474_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_474_, 0, v_a_448_);
lean_ctor_set(v___x_474_, 1, v_b_449_);
lean_ctor_set(v___x_474_, 2, v_bkt_467_);
v_buckets_x27_475_ = lean_array_uset(v_buckets_451_, v___x_466_, v___x_474_);
v___x_476_ = lean_unsigned_to_nat(4u);
v___x_477_ = lean_nat_mul(v_size_x27_473_, v___x_476_);
v___x_478_ = lean_unsigned_to_nat(3u);
v___x_479_ = lean_nat_div(v___x_477_, v___x_478_);
lean_dec(v___x_477_);
v___x_480_ = lean_array_get_size(v_buckets_x27_475_);
v___x_481_ = lean_nat_dec_le(v___x_479_, v___x_480_);
lean_dec(v___x_479_);
if (v___x_481_ == 0)
{
lean_object* v_val_482_; lean_object* v___x_484_; 
v_val_482_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_446_, v_buckets_x27_475_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 1, v_val_482_);
lean_ctor_set(v___x_470_, 0, v_size_x27_473_);
v___x_484_ = v___x_470_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_size_x27_473_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v_val_482_);
v___x_484_ = v_reuseFailAlloc_486_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
lean_object* v___x_485_; 
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_468_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
return v___x_485_;
}
}
else
{
lean_object* v___x_488_; 
lean_dec_ref(v_x_446_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 1, v_buckets_x27_475_);
lean_ctor_set(v___x_470_, 0, v_size_x27_473_);
v___x_488_ = v___x_470_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_size_x27_473_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_buckets_x27_475_);
v___x_488_ = v_reuseFailAlloc_490_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_489_; 
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_468_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
return v___x_489_;
}
}
}
}
else
{
lean_object* v___x_494_; 
lean_dec(v_b_449_);
lean_dec(v_a_448_);
lean_dec_ref(v_x_446_);
v___x_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_468_);
lean_ctor_set(v___x_494_, 1, v_m_447_);
return v___x_494_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_495_, lean_object* v_00_u03b2_496_, lean_object* v_x_497_, lean_object* v_x_498_, lean_object* v_inst_499_, lean_object* v_m_500_, lean_object* v_a_501_, lean_object* v_b_502_){
_start:
{
lean_object* v_size_503_; lean_object* v_buckets_504_; lean_object* v___x_505_; lean_object* v___x_506_; uint64_t v___x_507_; uint64_t v___x_508_; uint64_t v___x_509_; uint64_t v___x_510_; uint64_t v_fold_511_; uint64_t v___x_512_; uint64_t v___x_513_; uint64_t v___x_514_; size_t v___x_515_; size_t v___x_516_; size_t v___x_517_; size_t v___x_518_; size_t v___x_519_; lean_object* v_bkt_520_; lean_object* v___x_521_; 
v_size_503_ = lean_ctor_get(v_m_500_, 0);
v_buckets_504_ = lean_ctor_get(v_m_500_, 1);
v___x_505_ = lean_array_get_size(v_buckets_504_);
lean_inc_ref(v_x_498_);
lean_inc_n(v_a_501_, 2);
v___x_506_ = lean_apply_1(v_x_498_, v_a_501_);
v___x_507_ = 32ULL;
v___x_508_ = lean_unbox_uint64(v___x_506_);
v___x_509_ = lean_uint64_shift_right(v___x_508_, v___x_507_);
v___x_510_ = lean_unbox_uint64(v___x_506_);
lean_dec_ref(v___x_506_);
v_fold_511_ = lean_uint64_xor(v___x_510_, v___x_509_);
v___x_512_ = 16ULL;
v___x_513_ = lean_uint64_shift_right(v_fold_511_, v___x_512_);
v___x_514_ = lean_uint64_xor(v_fold_511_, v___x_513_);
v___x_515_ = lean_uint64_to_usize(v___x_514_);
v___x_516_ = lean_usize_of_nat(v___x_505_);
v___x_517_ = ((size_t)1ULL);
v___x_518_ = lean_usize_sub(v___x_516_, v___x_517_);
v___x_519_ = lean_usize_land(v___x_515_, v___x_518_);
v_bkt_520_ = lean_array_uget_borrowed(v_buckets_504_, v___x_519_);
lean_inc(v_bkt_520_);
v___x_521_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(v_x_497_, v_a_501_, v_bkt_520_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_544_; 
lean_inc_ref(v_buckets_504_);
lean_inc(v_size_503_);
v_isSharedCheck_544_ = !lean_is_exclusive(v_m_500_);
if (v_isSharedCheck_544_ == 0)
{
lean_object* v_unused_545_; lean_object* v_unused_546_; 
v_unused_545_ = lean_ctor_get(v_m_500_, 1);
lean_dec(v_unused_545_);
v_unused_546_ = lean_ctor_get(v_m_500_, 0);
lean_dec(v_unused_546_);
v___x_523_ = v_m_500_;
v_isShared_524_ = v_isSharedCheck_544_;
goto v_resetjp_522_;
}
else
{
lean_dec(v_m_500_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_544_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; lean_object* v_size_x27_526_; lean_object* v___x_527_; lean_object* v_buckets_x27_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_525_ = lean_unsigned_to_nat(1u);
v_size_x27_526_ = lean_nat_add(v_size_503_, v___x_525_);
lean_dec(v_size_503_);
lean_inc(v_bkt_520_);
v___x_527_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_527_, 0, v_a_501_);
lean_ctor_set(v___x_527_, 1, v_b_502_);
lean_ctor_set(v___x_527_, 2, v_bkt_520_);
v_buckets_x27_528_ = lean_array_uset(v_buckets_504_, v___x_519_, v___x_527_);
v___x_529_ = lean_unsigned_to_nat(4u);
v___x_530_ = lean_nat_mul(v_size_x27_526_, v___x_529_);
v___x_531_ = lean_unsigned_to_nat(3u);
v___x_532_ = lean_nat_div(v___x_530_, v___x_531_);
lean_dec(v___x_530_);
v___x_533_ = lean_array_get_size(v_buckets_x27_528_);
v___x_534_ = lean_nat_dec_le(v___x_532_, v___x_533_);
lean_dec(v___x_532_);
if (v___x_534_ == 0)
{
lean_object* v_val_535_; lean_object* v___x_537_; 
v_val_535_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_498_, v_buckets_x27_528_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 1, v_val_535_);
lean_ctor_set(v___x_523_, 0, v_size_x27_526_);
v___x_537_ = v___x_523_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_size_x27_526_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_val_535_);
v___x_537_ = v_reuseFailAlloc_539_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v___x_538_; 
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_521_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
return v___x_538_;
}
}
else
{
lean_object* v___x_541_; 
lean_dec_ref(v_x_498_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 1, v_buckets_x27_528_);
lean_ctor_set(v___x_523_, 0, v_size_x27_526_);
v___x_541_ = v___x_523_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_size_x27_526_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_buckets_x27_528_);
v___x_541_ = v_reuseFailAlloc_543_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_542_; 
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_521_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
return v___x_542_;
}
}
}
}
else
{
lean_object* v___x_547_; 
lean_dec(v_b_502_);
lean_dec(v_a_501_);
lean_dec_ref(v_x_498_);
v___x_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_521_);
lean_ctor_set(v___x_547_, 1, v_m_500_);
return v___x_547_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x3f___redArg(lean_object* v_x_548_, lean_object* v_x_549_, lean_object* v_m_550_, lean_object* v_a_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_x_548_, v_x_549_, v_m_550_, v_a_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x3f___redArg___boxed(lean_object* v_x_553_, lean_object* v_x_554_, lean_object* v_m_555_, lean_object* v_a_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Std_ExtDHashMap_get_x3f___redArg(v_x_553_, v_x_554_, v_m_555_, v_a_556_);
lean_dec(v_m_555_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x3f(lean_object* v_00_u03b1_558_, lean_object* v_00_u03b2_559_, lean_object* v_x_560_, lean_object* v_x_561_, lean_object* v_inst_562_, lean_object* v_m_563_, lean_object* v_a_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_x_560_, v_x_561_, v_m_563_, v_a_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x3f___boxed(lean_object* v_00_u03b1_566_, lean_object* v_00_u03b2_567_, lean_object* v_x_568_, lean_object* v_x_569_, lean_object* v_inst_570_, lean_object* v_m_571_, lean_object* v_a_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Std_ExtDHashMap_get_x3f(v_00_u03b1_566_, v_00_u03b2_567_, v_x_568_, v_x_569_, v_inst_570_, v_m_571_, v_a_572_);
lean_dec(v_m_571_);
return v_res_573_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_contains___redArg(lean_object* v_x_574_, lean_object* v_x_575_, lean_object* v_m_576_, lean_object* v_a_577_){
_start:
{
uint8_t v___x_578_; 
v___x_578_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_574_, v_x_575_, v_m_576_, v_a_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_contains___redArg___boxed(lean_object* v_x_579_, lean_object* v_x_580_, lean_object* v_m_581_, lean_object* v_a_582_){
_start:
{
uint8_t v_res_583_; lean_object* v_r_584_; 
v_res_583_ = l_Std_ExtDHashMap_contains___redArg(v_x_579_, v_x_580_, v_m_581_, v_a_582_);
lean_dec(v_m_581_);
v_r_584_ = lean_box(v_res_583_);
return v_r_584_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_contains(lean_object* v_00_u03b1_585_, lean_object* v_00_u03b2_586_, lean_object* v_x_587_, lean_object* v_x_588_, lean_object* v_inst_589_, lean_object* v_inst_590_, lean_object* v_m_591_, lean_object* v_a_592_){
_start:
{
uint8_t v___x_593_; 
v___x_593_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_587_, v_x_588_, v_m_591_, v_a_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_contains___boxed(lean_object* v_00_u03b1_594_, lean_object* v_00_u03b2_595_, lean_object* v_x_596_, lean_object* v_x_597_, lean_object* v_inst_598_, lean_object* v_inst_599_, lean_object* v_m_600_, lean_object* v_a_601_){
_start:
{
uint8_t v_res_602_; lean_object* v_r_603_; 
v_res_602_ = l_Std_ExtDHashMap_contains(v_00_u03b1_594_, v_00_u03b2_595_, v_x_596_, v_x_597_, v_inst_598_, v_inst_599_, v_m_600_, v_a_601_);
lean_dec(v_m_600_);
v_r_603_ = lean_box(v_res_602_);
return v_r_603_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable___redArg(){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = lean_box(0);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable___redArg___boxed(lean_object* v___dummy_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable___redArg();
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_608_, lean_object* v_00_u03b2_609_, lean_object* v_x_610_, lean_object* v_x_611_, lean_object* v_inst_612_, lean_object* v_inst_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = lean_box(0);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable___boxed(lean_object* v_00_u03b1_615_, lean_object* v_00_u03b2_616_, lean_object* v_x_617_, lean_object* v_x_618_, lean_object* v_inst_619_, lean_object* v_inst_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable(v_00_u03b1_615_, v_00_u03b2_616_, v_x_617_, v_x_618_, v_inst_619_, v_inst_620_);
lean_dec_ref(v_x_618_);
lean_dec_ref(v_x_617_);
return v_res_621_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_instDecidableMem___redArg(lean_object* v_x_622_, lean_object* v_x_623_, lean_object* v_m_624_, lean_object* v_a_625_){
_start:
{
uint8_t v___x_626_; 
v___x_626_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_622_, v_x_623_, v_m_624_, v_a_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instDecidableMem___redArg___boxed(lean_object* v_x_627_, lean_object* v_x_628_, lean_object* v_m_629_, lean_object* v_a_630_){
_start:
{
uint8_t v_res_631_; lean_object* v_r_632_; 
v_res_631_ = l_Std_ExtDHashMap_instDecidableMem___redArg(v_x_627_, v_x_628_, v_m_629_, v_a_630_);
lean_dec(v_m_629_);
v_r_632_ = lean_box(v_res_631_);
return v_r_632_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_instDecidableMem(lean_object* v_00_u03b1_633_, lean_object* v_00_u03b2_634_, lean_object* v_x_635_, lean_object* v_x_636_, lean_object* v_inst_637_, lean_object* v_inst_638_, lean_object* v_m_639_, lean_object* v_a_640_){
_start:
{
uint8_t v___x_641_; 
v___x_641_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_635_, v_x_636_, v_m_639_, v_a_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instDecidableMem___boxed(lean_object* v_00_u03b1_642_, lean_object* v_00_u03b2_643_, lean_object* v_x_644_, lean_object* v_x_645_, lean_object* v_inst_646_, lean_object* v_inst_647_, lean_object* v_m_648_, lean_object* v_a_649_){
_start:
{
uint8_t v_res_650_; lean_object* v_r_651_; 
v_res_650_ = l_Std_ExtDHashMap_instDecidableMem(v_00_u03b1_642_, v_00_u03b2_643_, v_x_644_, v_x_645_, v_inst_646_, v_inst_647_, v_m_648_, v_a_649_);
lean_dec(v_m_648_);
v_r_651_ = lean_box(v_res_650_);
return v_r_651_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get___redArg(lean_object* v_x_652_, lean_object* v_x_653_, lean_object* v_m_654_, lean_object* v_a_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_x_652_, v_x_653_, v_m_654_, v_a_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get___redArg___boxed(lean_object* v_x_657_, lean_object* v_x_658_, lean_object* v_m_659_, lean_object* v_a_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Std_ExtDHashMap_get___redArg(v_x_657_, v_x_658_, v_m_659_, v_a_660_);
lean_dec(v_m_659_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get(lean_object* v_00_u03b1_662_, lean_object* v_00_u03b2_663_, lean_object* v_x_664_, lean_object* v_x_665_, lean_object* v_inst_666_, lean_object* v_m_667_, lean_object* v_a_668_, lean_object* v_h_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_x_664_, v_x_665_, v_m_667_, v_a_668_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get___boxed(lean_object* v_00_u03b1_671_, lean_object* v_00_u03b2_672_, lean_object* v_x_673_, lean_object* v_x_674_, lean_object* v_inst_675_, lean_object* v_m_676_, lean_object* v_a_677_, lean_object* v_h_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Std_ExtDHashMap_get(v_00_u03b1_671_, v_00_u03b2_672_, v_x_673_, v_x_674_, v_inst_675_, v_m_676_, v_a_677_, v_h_678_);
lean_dec(v_m_676_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x21___redArg(lean_object* v_x_680_, lean_object* v_x_681_, lean_object* v_m_682_, lean_object* v_a_683_, lean_object* v_inst_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(v_x_680_, v_x_681_, v_m_682_, v_a_683_, v_inst_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x21___redArg___boxed(lean_object* v_x_686_, lean_object* v_x_687_, lean_object* v_m_688_, lean_object* v_a_689_, lean_object* v_inst_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Std_ExtDHashMap_get_x21___redArg(v_x_686_, v_x_687_, v_m_688_, v_a_689_, v_inst_690_);
lean_dec(v_inst_690_);
lean_dec(v_m_688_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x21(lean_object* v_00_u03b1_692_, lean_object* v_00_u03b2_693_, lean_object* v_x_694_, lean_object* v_x_695_, lean_object* v_inst_696_, lean_object* v_m_697_, lean_object* v_a_698_, lean_object* v_inst_699_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(v_x_694_, v_x_695_, v_m_697_, v_a_698_, v_inst_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x21___boxed(lean_object* v_00_u03b1_701_, lean_object* v_00_u03b2_702_, lean_object* v_x_703_, lean_object* v_x_704_, lean_object* v_inst_705_, lean_object* v_m_706_, lean_object* v_a_707_, lean_object* v_inst_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Std_ExtDHashMap_get_x21(v_00_u03b1_701_, v_00_u03b2_702_, v_x_703_, v_x_704_, v_inst_705_, v_m_706_, v_a_707_, v_inst_708_);
lean_dec(v_inst_708_);
lean_dec(v_m_706_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getD___redArg(lean_object* v_x_710_, lean_object* v_x_711_, lean_object* v_m_712_, lean_object* v_a_713_, lean_object* v_fallback_714_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(v_x_710_, v_x_711_, v_m_712_, v_a_713_, v_fallback_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getD___redArg___boxed(lean_object* v_x_716_, lean_object* v_x_717_, lean_object* v_m_718_, lean_object* v_a_719_, lean_object* v_fallback_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Std_ExtDHashMap_getD___redArg(v_x_716_, v_x_717_, v_m_718_, v_a_719_, v_fallback_720_);
lean_dec(v_fallback_720_);
lean_dec(v_m_718_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getD(lean_object* v_00_u03b1_722_, lean_object* v_00_u03b2_723_, lean_object* v_x_724_, lean_object* v_x_725_, lean_object* v_inst_726_, lean_object* v_m_727_, lean_object* v_a_728_, lean_object* v_fallback_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(v_x_724_, v_x_725_, v_m_727_, v_a_728_, v_fallback_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getD___boxed(lean_object* v_00_u03b1_731_, lean_object* v_00_u03b2_732_, lean_object* v_x_733_, lean_object* v_x_734_, lean_object* v_inst_735_, lean_object* v_m_736_, lean_object* v_a_737_, lean_object* v_fallback_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Std_ExtDHashMap_getD(v_00_u03b1_731_, v_00_u03b2_732_, v_x_733_, v_x_734_, v_inst_735_, v_m_736_, v_a_737_, v_fallback_738_);
lean_dec(v_fallback_738_);
lean_dec(v_m_736_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_erase___redArg(lean_object* v_x_740_, lean_object* v_x_741_, lean_object* v_m_742_, lean_object* v_a_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_740_, v_x_741_, v_m_742_, v_a_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_erase(lean_object* v_00_u03b1_745_, lean_object* v_00_u03b2_746_, lean_object* v_x_747_, lean_object* v_x_748_, lean_object* v_inst_749_, lean_object* v_inst_750_, lean_object* v_m_751_, lean_object* v_a_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_747_, v_x_748_, v_m_751_, v_a_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x3f___redArg(lean_object* v_x_754_, lean_object* v_x_755_, lean_object* v_m_756_, lean_object* v_a_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_754_, v_x_755_, v_m_756_, v_a_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x3f___redArg___boxed(lean_object* v_x_759_, lean_object* v_x_760_, lean_object* v_m_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Std_ExtDHashMap_Const_get_x3f___redArg(v_x_759_, v_x_760_, v_m_761_, v_a_762_);
lean_dec(v_m_761_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x3f(lean_object* v_00_u03b1_764_, lean_object* v_x_765_, lean_object* v_x_766_, lean_object* v_00_u03b2_767_, lean_object* v_inst_768_, lean_object* v_inst_769_, lean_object* v_m_770_, lean_object* v_a_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_765_, v_x_766_, v_m_770_, v_a_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x3f___boxed(lean_object* v_00_u03b1_773_, lean_object* v_x_774_, lean_object* v_x_775_, lean_object* v_00_u03b2_776_, lean_object* v_inst_777_, lean_object* v_inst_778_, lean_object* v_m_779_, lean_object* v_a_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Std_ExtDHashMap_Const_get_x3f(v_00_u03b1_773_, v_x_774_, v_x_775_, v_00_u03b2_776_, v_inst_777_, v_inst_778_, v_m_779_, v_a_780_);
lean_dec(v_m_779_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get___redArg(lean_object* v_x_782_, lean_object* v_x_783_, lean_object* v_m_784_, lean_object* v_a_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_x_782_, v_x_783_, v_m_784_, v_a_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get___redArg___boxed(lean_object* v_x_787_, lean_object* v_x_788_, lean_object* v_m_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Std_ExtDHashMap_Const_get___redArg(v_x_787_, v_x_788_, v_m_789_, v_a_790_);
lean_dec(v_m_789_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get(lean_object* v_00_u03b1_792_, lean_object* v_x_793_, lean_object* v_x_794_, lean_object* v_00_u03b2_795_, lean_object* v_inst_796_, lean_object* v_inst_797_, lean_object* v_m_798_, lean_object* v_a_799_, lean_object* v_h_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_x_793_, v_x_794_, v_m_798_, v_a_799_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get___boxed(lean_object* v_00_u03b1_802_, lean_object* v_x_803_, lean_object* v_x_804_, lean_object* v_00_u03b2_805_, lean_object* v_inst_806_, lean_object* v_inst_807_, lean_object* v_m_808_, lean_object* v_a_809_, lean_object* v_h_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Std_ExtDHashMap_Const_get(v_00_u03b1_802_, v_x_803_, v_x_804_, v_00_u03b2_805_, v_inst_806_, v_inst_807_, v_m_808_, v_a_809_, v_h_810_);
lean_dec(v_m_808_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getD___redArg(lean_object* v_x_812_, lean_object* v_x_813_, lean_object* v_m_814_, lean_object* v_a_815_, lean_object* v_fallback_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_x_812_, v_x_813_, v_m_814_, v_a_815_, v_fallback_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getD___redArg___boxed(lean_object* v_x_818_, lean_object* v_x_819_, lean_object* v_m_820_, lean_object* v_a_821_, lean_object* v_fallback_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Std_ExtDHashMap_Const_getD___redArg(v_x_818_, v_x_819_, v_m_820_, v_a_821_, v_fallback_822_);
lean_dec(v_fallback_822_);
lean_dec(v_m_820_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getD(lean_object* v_00_u03b1_824_, lean_object* v_x_825_, lean_object* v_x_826_, lean_object* v_00_u03b2_827_, lean_object* v_inst_828_, lean_object* v_inst_829_, lean_object* v_m_830_, lean_object* v_a_831_, lean_object* v_fallback_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_x_825_, v_x_826_, v_m_830_, v_a_831_, v_fallback_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getD___boxed(lean_object* v_00_u03b1_834_, lean_object* v_x_835_, lean_object* v_x_836_, lean_object* v_00_u03b2_837_, lean_object* v_inst_838_, lean_object* v_inst_839_, lean_object* v_m_840_, lean_object* v_a_841_, lean_object* v_fallback_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Std_ExtDHashMap_Const_getD(v_00_u03b1_834_, v_x_835_, v_x_836_, v_00_u03b2_837_, v_inst_838_, v_inst_839_, v_m_840_, v_a_841_, v_fallback_842_);
lean_dec(v_fallback_842_);
lean_dec(v_m_840_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x21___redArg(lean_object* v_x_844_, lean_object* v_x_845_, lean_object* v_inst_846_, lean_object* v_m_847_, lean_object* v_a_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_x_844_, v_x_845_, v_inst_846_, v_m_847_, v_a_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x21___redArg___boxed(lean_object* v_x_850_, lean_object* v_x_851_, lean_object* v_inst_852_, lean_object* v_m_853_, lean_object* v_a_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Std_ExtDHashMap_Const_get_x21___redArg(v_x_850_, v_x_851_, v_inst_852_, v_m_853_, v_a_854_);
lean_dec(v_m_853_);
lean_dec(v_inst_852_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x21(lean_object* v_00_u03b1_856_, lean_object* v_x_857_, lean_object* v_x_858_, lean_object* v_00_u03b2_859_, lean_object* v_inst_860_, lean_object* v_inst_861_, lean_object* v_inst_862_, lean_object* v_m_863_, lean_object* v_a_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_x_857_, v_x_858_, v_inst_862_, v_m_863_, v_a_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x21___boxed(lean_object* v_00_u03b1_866_, lean_object* v_x_867_, lean_object* v_x_868_, lean_object* v_00_u03b2_869_, lean_object* v_inst_870_, lean_object* v_inst_871_, lean_object* v_inst_872_, lean_object* v_m_873_, lean_object* v_a_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Std_ExtDHashMap_Const_get_x21(v_00_u03b1_866_, v_x_867_, v_x_868_, v_00_u03b2_869_, v_inst_870_, v_inst_871_, v_inst_872_, v_m_873_, v_a_874_);
lean_dec(v_m_873_);
lean_dec(v_inst_872_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getThenInsertIfNew_x3f___redArg(lean_object* v_x_876_, lean_object* v_x_877_, lean_object* v_m_878_, lean_object* v_a_879_, lean_object* v_b_880_){
_start:
{
lean_object* v_size_881_; lean_object* v_buckets_882_; lean_object* v___x_883_; lean_object* v___x_884_; uint64_t v___x_885_; uint64_t v___x_886_; uint64_t v___x_887_; uint64_t v___x_888_; uint64_t v_fold_889_; uint64_t v___x_890_; uint64_t v___x_891_; uint64_t v___x_892_; size_t v___x_893_; size_t v___x_894_; size_t v___x_895_; size_t v___x_896_; size_t v___x_897_; lean_object* v_bkt_898_; lean_object* v___x_899_; 
v_size_881_ = lean_ctor_get(v_m_878_, 0);
v_buckets_882_ = lean_ctor_get(v_m_878_, 1);
v___x_883_ = lean_array_get_size(v_buckets_882_);
lean_inc_ref(v_x_877_);
lean_inc_n(v_a_879_, 2);
v___x_884_ = lean_apply_1(v_x_877_, v_a_879_);
v___x_885_ = 32ULL;
v___x_886_ = lean_unbox_uint64(v___x_884_);
v___x_887_ = lean_uint64_shift_right(v___x_886_, v___x_885_);
v___x_888_ = lean_unbox_uint64(v___x_884_);
lean_dec_ref(v___x_884_);
v_fold_889_ = lean_uint64_xor(v___x_888_, v___x_887_);
v___x_890_ = 16ULL;
v___x_891_ = lean_uint64_shift_right(v_fold_889_, v___x_890_);
v___x_892_ = lean_uint64_xor(v_fold_889_, v___x_891_);
v___x_893_ = lean_uint64_to_usize(v___x_892_);
v___x_894_ = lean_usize_of_nat(v___x_883_);
v___x_895_ = ((size_t)1ULL);
v___x_896_ = lean_usize_sub(v___x_894_, v___x_895_);
v___x_897_ = lean_usize_land(v___x_893_, v___x_896_);
v_bkt_898_ = lean_array_uget_borrowed(v_buckets_882_, v___x_897_);
lean_inc(v_bkt_898_);
v___x_899_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_x_876_, v_a_879_, v_bkt_898_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_922_; 
lean_inc_ref(v_buckets_882_);
lean_inc(v_size_881_);
v_isSharedCheck_922_ = !lean_is_exclusive(v_m_878_);
if (v_isSharedCheck_922_ == 0)
{
lean_object* v_unused_923_; lean_object* v_unused_924_; 
v_unused_923_ = lean_ctor_get(v_m_878_, 1);
lean_dec(v_unused_923_);
v_unused_924_ = lean_ctor_get(v_m_878_, 0);
lean_dec(v_unused_924_);
v___x_901_ = v_m_878_;
v_isShared_902_ = v_isSharedCheck_922_;
goto v_resetjp_900_;
}
else
{
lean_dec(v_m_878_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_922_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_903_; lean_object* v_size_x27_904_; lean_object* v___x_905_; lean_object* v_buckets_x27_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; uint8_t v___x_912_; 
v___x_903_ = lean_unsigned_to_nat(1u);
v_size_x27_904_ = lean_nat_add(v_size_881_, v___x_903_);
lean_dec(v_size_881_);
lean_inc(v_bkt_898_);
v___x_905_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_905_, 0, v_a_879_);
lean_ctor_set(v___x_905_, 1, v_b_880_);
lean_ctor_set(v___x_905_, 2, v_bkt_898_);
v_buckets_x27_906_ = lean_array_uset(v_buckets_882_, v___x_897_, v___x_905_);
v___x_907_ = lean_unsigned_to_nat(4u);
v___x_908_ = lean_nat_mul(v_size_x27_904_, v___x_907_);
v___x_909_ = lean_unsigned_to_nat(3u);
v___x_910_ = lean_nat_div(v___x_908_, v___x_909_);
lean_dec(v___x_908_);
v___x_911_ = lean_array_get_size(v_buckets_x27_906_);
v___x_912_ = lean_nat_dec_le(v___x_910_, v___x_911_);
lean_dec(v___x_910_);
if (v___x_912_ == 0)
{
lean_object* v_val_913_; lean_object* v___x_915_; 
v_val_913_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_877_, v_buckets_x27_906_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 1, v_val_913_);
lean_ctor_set(v___x_901_, 0, v_size_x27_904_);
v___x_915_ = v___x_901_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_size_x27_904_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v_val_913_);
v___x_915_ = v_reuseFailAlloc_917_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_916_; 
v___x_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_899_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
return v___x_916_;
}
}
else
{
lean_object* v___x_919_; 
lean_dec_ref(v_x_877_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 1, v_buckets_x27_906_);
lean_ctor_set(v___x_901_, 0, v_size_x27_904_);
v___x_919_ = v___x_901_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_size_x27_904_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_buckets_x27_906_);
v___x_919_ = v_reuseFailAlloc_921_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_920_; 
v___x_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_899_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
return v___x_920_;
}
}
}
}
else
{
lean_object* v___x_925_; 
lean_dec(v_b_880_);
lean_dec(v_a_879_);
lean_dec_ref(v_x_877_);
v___x_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_899_);
lean_ctor_set(v___x_925_, 1, v_m_878_);
return v___x_925_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_926_, lean_object* v_x_927_, lean_object* v_x_928_, lean_object* v_00_u03b2_929_, lean_object* v_inst_930_, lean_object* v_inst_931_, lean_object* v_m_932_, lean_object* v_a_933_, lean_object* v_b_934_){
_start:
{
lean_object* v_size_935_; lean_object* v_buckets_936_; lean_object* v___x_937_; lean_object* v___x_938_; uint64_t v___x_939_; uint64_t v___x_940_; uint64_t v___x_941_; uint64_t v___x_942_; uint64_t v_fold_943_; uint64_t v___x_944_; uint64_t v___x_945_; uint64_t v___x_946_; size_t v___x_947_; size_t v___x_948_; size_t v___x_949_; size_t v___x_950_; size_t v___x_951_; lean_object* v_bkt_952_; lean_object* v___x_953_; 
v_size_935_ = lean_ctor_get(v_m_932_, 0);
v_buckets_936_ = lean_ctor_get(v_m_932_, 1);
v___x_937_ = lean_array_get_size(v_buckets_936_);
lean_inc_ref(v_x_928_);
lean_inc_n(v_a_933_, 2);
v___x_938_ = lean_apply_1(v_x_928_, v_a_933_);
v___x_939_ = 32ULL;
v___x_940_ = lean_unbox_uint64(v___x_938_);
v___x_941_ = lean_uint64_shift_right(v___x_940_, v___x_939_);
v___x_942_ = lean_unbox_uint64(v___x_938_);
lean_dec_ref(v___x_938_);
v_fold_943_ = lean_uint64_xor(v___x_942_, v___x_941_);
v___x_944_ = 16ULL;
v___x_945_ = lean_uint64_shift_right(v_fold_943_, v___x_944_);
v___x_946_ = lean_uint64_xor(v_fold_943_, v___x_945_);
v___x_947_ = lean_uint64_to_usize(v___x_946_);
v___x_948_ = lean_usize_of_nat(v___x_937_);
v___x_949_ = ((size_t)1ULL);
v___x_950_ = lean_usize_sub(v___x_948_, v___x_949_);
v___x_951_ = lean_usize_land(v___x_947_, v___x_950_);
v_bkt_952_ = lean_array_uget_borrowed(v_buckets_936_, v___x_951_);
lean_inc(v_bkt_952_);
v___x_953_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_x_927_, v_a_933_, v_bkt_952_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_976_; 
lean_inc_ref(v_buckets_936_);
lean_inc(v_size_935_);
v_isSharedCheck_976_ = !lean_is_exclusive(v_m_932_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; lean_object* v_unused_978_; 
v_unused_977_ = lean_ctor_get(v_m_932_, 1);
lean_dec(v_unused_977_);
v_unused_978_ = lean_ctor_get(v_m_932_, 0);
lean_dec(v_unused_978_);
v___x_955_ = v_m_932_;
v_isShared_956_ = v_isSharedCheck_976_;
goto v_resetjp_954_;
}
else
{
lean_dec(v_m_932_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_976_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; lean_object* v_size_x27_958_; lean_object* v___x_959_; lean_object* v_buckets_x27_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_957_ = lean_unsigned_to_nat(1u);
v_size_x27_958_ = lean_nat_add(v_size_935_, v___x_957_);
lean_dec(v_size_935_);
lean_inc(v_bkt_952_);
v___x_959_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_959_, 0, v_a_933_);
lean_ctor_set(v___x_959_, 1, v_b_934_);
lean_ctor_set(v___x_959_, 2, v_bkt_952_);
v_buckets_x27_960_ = lean_array_uset(v_buckets_936_, v___x_951_, v___x_959_);
v___x_961_ = lean_unsigned_to_nat(4u);
v___x_962_ = lean_nat_mul(v_size_x27_958_, v___x_961_);
v___x_963_ = lean_unsigned_to_nat(3u);
v___x_964_ = lean_nat_div(v___x_962_, v___x_963_);
lean_dec(v___x_962_);
v___x_965_ = lean_array_get_size(v_buckets_x27_960_);
v___x_966_ = lean_nat_dec_le(v___x_964_, v___x_965_);
lean_dec(v___x_964_);
if (v___x_966_ == 0)
{
lean_object* v_val_967_; lean_object* v___x_969_; 
v_val_967_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_928_, v_buckets_x27_960_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 1, v_val_967_);
lean_ctor_set(v___x_955_, 0, v_size_x27_958_);
v___x_969_ = v___x_955_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_size_x27_958_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v_val_967_);
v___x_969_ = v_reuseFailAlloc_971_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_970_; 
v___x_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_953_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
return v___x_970_;
}
}
else
{
lean_object* v___x_973_; 
lean_dec_ref(v_x_928_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 1, v_buckets_x27_960_);
lean_ctor_set(v___x_955_, 0, v_size_x27_958_);
v___x_973_ = v___x_955_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_size_x27_958_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_buckets_x27_960_);
v___x_973_ = v_reuseFailAlloc_975_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_974_; 
v___x_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_953_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
return v___x_974_;
}
}
}
}
else
{
lean_object* v___x_979_; 
lean_dec(v_b_934_);
lean_dec(v_a_933_);
lean_dec_ref(v_x_928_);
v___x_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_953_);
lean_ctor_set(v___x_979_, 1, v_m_932_);
return v___x_979_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x3f___redArg(lean_object* v_x_980_, lean_object* v_x_981_, lean_object* v_m_982_, lean_object* v_a_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_980_, v_x_981_, v_m_982_, v_a_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x3f___redArg___boxed(lean_object* v_x_985_, lean_object* v_x_986_, lean_object* v_m_987_, lean_object* v_a_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Std_ExtDHashMap_getKey_x3f___redArg(v_x_985_, v_x_986_, v_m_987_, v_a_988_);
lean_dec(v_m_987_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x3f(lean_object* v_00_u03b1_990_, lean_object* v_00_u03b2_991_, lean_object* v_x_992_, lean_object* v_x_993_, lean_object* v_inst_994_, lean_object* v_inst_995_, lean_object* v_m_996_, lean_object* v_a_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_992_, v_x_993_, v_m_996_, v_a_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x3f___boxed(lean_object* v_00_u03b1_999_, lean_object* v_00_u03b2_1000_, lean_object* v_x_1001_, lean_object* v_x_1002_, lean_object* v_inst_1003_, lean_object* v_inst_1004_, lean_object* v_m_1005_, lean_object* v_a_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Std_ExtDHashMap_getKey_x3f(v_00_u03b1_999_, v_00_u03b2_1000_, v_x_1001_, v_x_1002_, v_inst_1003_, v_inst_1004_, v_m_1005_, v_a_1006_);
lean_dec(v_m_1005_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey___redArg(lean_object* v_x_1008_, lean_object* v_x_1009_, lean_object* v_m_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_x_1008_, v_x_1009_, v_m_1010_, v_a_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey___redArg___boxed(lean_object* v_x_1013_, lean_object* v_x_1014_, lean_object* v_m_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Std_ExtDHashMap_getKey___redArg(v_x_1013_, v_x_1014_, v_m_1015_, v_a_1016_);
lean_dec(v_m_1015_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey(lean_object* v_00_u03b1_1018_, lean_object* v_00_u03b2_1019_, lean_object* v_x_1020_, lean_object* v_x_1021_, lean_object* v_inst_1022_, lean_object* v_inst_1023_, lean_object* v_m_1024_, lean_object* v_a_1025_, lean_object* v_h_1026_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_x_1020_, v_x_1021_, v_m_1024_, v_a_1025_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey___boxed(lean_object* v_00_u03b1_1028_, lean_object* v_00_u03b2_1029_, lean_object* v_x_1030_, lean_object* v_x_1031_, lean_object* v_inst_1032_, lean_object* v_inst_1033_, lean_object* v_m_1034_, lean_object* v_a_1035_, lean_object* v_h_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Std_ExtDHashMap_getKey(v_00_u03b1_1028_, v_00_u03b2_1029_, v_x_1030_, v_x_1031_, v_inst_1032_, v_inst_1033_, v_m_1034_, v_a_1035_, v_h_1036_);
lean_dec(v_m_1034_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x21___redArg(lean_object* v_x_1038_, lean_object* v_x_1039_, lean_object* v_inst_1040_, lean_object* v_m_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_1038_, v_x_1039_, v_inst_1040_, v_m_1041_, v_a_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x21___redArg___boxed(lean_object* v_x_1044_, lean_object* v_x_1045_, lean_object* v_inst_1046_, lean_object* v_m_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Std_ExtDHashMap_getKey_x21___redArg(v_x_1044_, v_x_1045_, v_inst_1046_, v_m_1047_, v_a_1048_);
lean_dec(v_m_1047_);
lean_dec(v_inst_1046_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x21(lean_object* v_00_u03b1_1050_, lean_object* v_00_u03b2_1051_, lean_object* v_x_1052_, lean_object* v_x_1053_, lean_object* v_inst_1054_, lean_object* v_inst_1055_, lean_object* v_inst_1056_, lean_object* v_m_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_1052_, v_x_1053_, v_inst_1056_, v_m_1057_, v_a_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x21___boxed(lean_object* v_00_u03b1_1060_, lean_object* v_00_u03b2_1061_, lean_object* v_x_1062_, lean_object* v_x_1063_, lean_object* v_inst_1064_, lean_object* v_inst_1065_, lean_object* v_inst_1066_, lean_object* v_m_1067_, lean_object* v_a_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Std_ExtDHashMap_getKey_x21(v_00_u03b1_1060_, v_00_u03b2_1061_, v_x_1062_, v_x_1063_, v_inst_1064_, v_inst_1065_, v_inst_1066_, v_m_1067_, v_a_1068_);
lean_dec(v_m_1067_);
lean_dec(v_inst_1066_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKeyD___redArg(lean_object* v_x_1070_, lean_object* v_x_1071_, lean_object* v_m_1072_, lean_object* v_a_1073_, lean_object* v_fallback_1074_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_1070_, v_x_1071_, v_m_1072_, v_a_1073_, v_fallback_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKeyD___redArg___boxed(lean_object* v_x_1076_, lean_object* v_x_1077_, lean_object* v_m_1078_, lean_object* v_a_1079_, lean_object* v_fallback_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Std_ExtDHashMap_getKeyD___redArg(v_x_1076_, v_x_1077_, v_m_1078_, v_a_1079_, v_fallback_1080_);
lean_dec(v_fallback_1080_);
lean_dec(v_m_1078_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKeyD(lean_object* v_00_u03b1_1082_, lean_object* v_00_u03b2_1083_, lean_object* v_x_1084_, lean_object* v_x_1085_, lean_object* v_inst_1086_, lean_object* v_inst_1087_, lean_object* v_m_1088_, lean_object* v_a_1089_, lean_object* v_fallback_1090_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_1084_, v_x_1085_, v_m_1088_, v_a_1089_, v_fallback_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKeyD___boxed(lean_object* v_00_u03b1_1092_, lean_object* v_00_u03b2_1093_, lean_object* v_x_1094_, lean_object* v_x_1095_, lean_object* v_inst_1096_, lean_object* v_inst_1097_, lean_object* v_m_1098_, lean_object* v_a_1099_, lean_object* v_fallback_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Std_ExtDHashMap_getKeyD(v_00_u03b1_1092_, v_00_u03b2_1093_, v_x_1094_, v_x_1095_, v_inst_1096_, v_inst_1097_, v_m_1098_, v_a_1099_, v_fallback_1100_);
lean_dec(v_fallback_1100_);
lean_dec(v_m_1098_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_size___redArg(lean_object* v_m_1102_){
_start:
{
lean_object* v_size_1103_; 
v_size_1103_ = lean_ctor_get(v_m_1102_, 0);
lean_inc(v_size_1103_);
return v_size_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_size___redArg___boxed(lean_object* v_m_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Std_ExtDHashMap_size___redArg(v_m_1104_);
lean_dec(v_m_1104_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_size(lean_object* v_00_u03b1_1106_, lean_object* v_00_u03b2_1107_, lean_object* v_x_1108_, lean_object* v_x_1109_, lean_object* v_inst_1110_, lean_object* v_inst_1111_, lean_object* v_m_1112_){
_start:
{
lean_object* v_size_1113_; 
v_size_1113_ = lean_ctor_get(v_m_1112_, 0);
lean_inc(v_size_1113_);
return v_size_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_size___boxed(lean_object* v_00_u03b1_1114_, lean_object* v_00_u03b2_1115_, lean_object* v_x_1116_, lean_object* v_x_1117_, lean_object* v_inst_1118_, lean_object* v_inst_1119_, lean_object* v_m_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Std_ExtDHashMap_size(v_00_u03b1_1114_, v_00_u03b2_1115_, v_x_1116_, v_x_1117_, v_inst_1118_, v_inst_1119_, v_m_1120_);
lean_dec(v_m_1120_);
lean_dec_ref(v_x_1117_);
lean_dec_ref(v_x_1116_);
return v_res_1121_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_isEmpty___redArg(lean_object* v_m_1122_){
_start:
{
lean_object* v_size_1123_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
v_size_1123_ = lean_ctor_get(v_m_1122_, 0);
v___x_1124_ = lean_unsigned_to_nat(0u);
v___x_1125_ = lean_nat_dec_eq(v_size_1123_, v___x_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_isEmpty___redArg___boxed(lean_object* v_m_1126_){
_start:
{
uint8_t v_res_1127_; lean_object* v_r_1128_; 
v_res_1127_ = l_Std_ExtDHashMap_isEmpty___redArg(v_m_1126_);
lean_dec(v_m_1126_);
v_r_1128_ = lean_box(v_res_1127_);
return v_r_1128_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_isEmpty(lean_object* v_00_u03b1_1129_, lean_object* v_00_u03b2_1130_, lean_object* v_x_1131_, lean_object* v_x_1132_, lean_object* v_inst_1133_, lean_object* v_inst_1134_, lean_object* v_m_1135_){
_start:
{
lean_object* v_size_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; 
v_size_1136_ = lean_ctor_get(v_m_1135_, 0);
v___x_1137_ = lean_unsigned_to_nat(0u);
v___x_1138_ = lean_nat_dec_eq(v_size_1136_, v___x_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_isEmpty___boxed(lean_object* v_00_u03b1_1139_, lean_object* v_00_u03b2_1140_, lean_object* v_x_1141_, lean_object* v_x_1142_, lean_object* v_inst_1143_, lean_object* v_inst_1144_, lean_object* v_m_1145_){
_start:
{
uint8_t v_res_1146_; lean_object* v_r_1147_; 
v_res_1146_ = l_Std_ExtDHashMap_isEmpty(v_00_u03b1_1139_, v_00_u03b2_1140_, v_x_1141_, v_x_1142_, v_inst_1143_, v_inst_1144_, v_m_1145_);
lean_dec(v_m_1145_);
lean_dec_ref(v_x_1142_);
lean_dec_ref(v_x_1141_);
v_r_1147_ = lean_box(v_res_1146_);
return v_r_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filter___redArg(lean_object* v_f_1148_, lean_object* v_m_1149_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1148_, v_m_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filter(lean_object* v_00_u03b1_1151_, lean_object* v_00_u03b2_1152_, lean_object* v_x_1153_, lean_object* v_x_1154_, lean_object* v_inst_1155_, lean_object* v_inst_1156_, lean_object* v_f_1157_, lean_object* v_m_1158_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1157_, v_m_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filter___boxed(lean_object* v_00_u03b1_1160_, lean_object* v_00_u03b2_1161_, lean_object* v_x_1162_, lean_object* v_x_1163_, lean_object* v_inst_1164_, lean_object* v_inst_1165_, lean_object* v_f_1166_, lean_object* v_m_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Std_ExtDHashMap_filter(v_00_u03b1_1160_, v_00_u03b2_1161_, v_x_1162_, v_x_1163_, v_inst_1164_, v_inst_1165_, v_f_1166_, v_m_1167_);
lean_dec_ref(v_x_1163_);
lean_dec_ref(v_x_1162_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_map___redArg(lean_object* v_f_1169_, lean_object* v_m_1170_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1169_, v_m_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_map(lean_object* v_00_u03b1_1172_, lean_object* v_00_u03b2_1173_, lean_object* v_00_u03b3_1174_, lean_object* v_x_1175_, lean_object* v_x_1176_, lean_object* v_inst_1177_, lean_object* v_inst_1178_, lean_object* v_f_1179_, lean_object* v_m_1180_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1179_, v_m_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_map___boxed(lean_object* v_00_u03b1_1182_, lean_object* v_00_u03b2_1183_, lean_object* v_00_u03b3_1184_, lean_object* v_x_1185_, lean_object* v_x_1186_, lean_object* v_inst_1187_, lean_object* v_inst_1188_, lean_object* v_f_1189_, lean_object* v_m_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Std_ExtDHashMap_map(v_00_u03b1_1182_, v_00_u03b2_1183_, v_00_u03b3_1184_, v_x_1185_, v_x_1186_, v_inst_1187_, v_inst_1188_, v_f_1189_, v_m_1190_);
lean_dec_ref(v_x_1186_);
lean_dec_ref(v_x_1185_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filterMap___redArg(lean_object* v_f_1192_, lean_object* v_m_1193_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1192_, v_m_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filterMap(lean_object* v_00_u03b1_1195_, lean_object* v_00_u03b2_1196_, lean_object* v_00_u03b3_1197_, lean_object* v_x_1198_, lean_object* v_x_1199_, lean_object* v_inst_1200_, lean_object* v_inst_1201_, lean_object* v_f_1202_, lean_object* v_m_1203_){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1202_, v_m_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filterMap___boxed(lean_object* v_00_u03b1_1205_, lean_object* v_00_u03b2_1206_, lean_object* v_00_u03b3_1207_, lean_object* v_x_1208_, lean_object* v_x_1209_, lean_object* v_inst_1210_, lean_object* v_inst_1211_, lean_object* v_f_1212_, lean_object* v_m_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Std_ExtDHashMap_filterMap(v_00_u03b1_1205_, v_00_u03b2_1206_, v_00_u03b3_1207_, v_x_1208_, v_x_1209_, v_inst_1210_, v_inst_1211_, v_f_1212_, v_m_1213_);
lean_dec_ref(v_x_1209_);
lean_dec_ref(v_x_1208_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_modify___redArg(lean_object* v_x_1215_, lean_object* v_x_1216_, lean_object* v_m_1217_, lean_object* v_a_1218_, lean_object* v_f_1219_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(v_x_1215_, v_x_1216_, v_m_1217_, v_a_1218_, v_f_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_modify(lean_object* v_00_u03b1_1221_, lean_object* v_00_u03b2_1222_, lean_object* v_x_1223_, lean_object* v_x_1224_, lean_object* v_inst_1225_, lean_object* v_m_1226_, lean_object* v_a_1227_, lean_object* v_f_1228_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(v_x_1223_, v_x_1224_, v_m_1226_, v_a_1227_, v_f_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_modify___redArg(lean_object* v_x_1230_, lean_object* v_x_1231_, lean_object* v_m_1232_, lean_object* v_a_1233_, lean_object* v_f_1234_){
_start:
{
lean_object* v___x_1235_; 
v___x_1235_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_x_1230_, v_x_1231_, v_m_1232_, v_a_1233_, v_f_1234_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_modify(lean_object* v_00_u03b1_1236_, lean_object* v_x_1237_, lean_object* v_x_1238_, lean_object* v_inst_1239_, lean_object* v_inst_1240_, lean_object* v_00_u03b2_1241_, lean_object* v_m_1242_, lean_object* v_a_1243_, lean_object* v_f_1244_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_x_1237_, v_x_1238_, v_m_1242_, v_a_1243_, v_f_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_alter___redArg(lean_object* v_x_1246_, lean_object* v_x_1247_, lean_object* v_m_1248_, lean_object* v_a_1249_, lean_object* v_f_1250_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(v_x_1246_, v_x_1247_, v_m_1248_, v_a_1249_, v_f_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_alter(lean_object* v_00_u03b1_1252_, lean_object* v_00_u03b2_1253_, lean_object* v_x_1254_, lean_object* v_x_1255_, lean_object* v_inst_1256_, lean_object* v_m_1257_, lean_object* v_a_1258_, lean_object* v_f_1259_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(v_x_1254_, v_x_1255_, v_m_1257_, v_a_1258_, v_f_1259_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_alter___redArg(lean_object* v_x_1261_, lean_object* v_x_1262_, lean_object* v_m_1263_, lean_object* v_a_1264_, lean_object* v_f_1265_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_x_1261_, v_x_1262_, v_m_1263_, v_a_1264_, v_f_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_alter(lean_object* v_00_u03b1_1267_, lean_object* v_x_1268_, lean_object* v_x_1269_, lean_object* v_inst_1270_, lean_object* v_inst_1271_, lean_object* v_00_u03b2_1272_, lean_object* v_m_1273_, lean_object* v_a_1274_, lean_object* v_f_1275_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_x_1268_, v_x_1269_, v_m_1273_, v_a_1274_, v_f_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insertMany___redArg___lam__0(lean_object* v_x_1277_, lean_object* v_x_1278_, lean_object* v_x_1279_, lean_object* v_____s_1280_){
_start:
{
lean_object* v_fst_1281_; lean_object* v_snd_1282_; lean_object* v_m_1283_; lean_object* v___x_1284_; 
v_fst_1281_ = lean_ctor_get(v_x_1279_, 0);
lean_inc(v_fst_1281_);
v_snd_1282_ = lean_ctor_get(v_x_1279_, 1);
lean_inc(v_snd_1282_);
lean_dec_ref(v_x_1279_);
v_m_1283_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1277_, v_x_1278_, v_____s_1280_, v_fst_1281_, v_snd_1282_);
v___x_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1284_, 0, v_m_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insertMany___redArg(lean_object* v_x_1285_, lean_object* v_x_1286_, lean_object* v_inst_1287_, lean_object* v_m_1288_, lean_object* v_l_1289_){
_start:
{
lean_object* v___f_1290_; lean_object* v___x_1291_; 
v___f_1290_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1290_, 0, v_x_1285_);
lean_closure_set(v___f_1290_, 1, v_x_1286_);
v___x_1291_ = lean_apply_4(v_inst_1287_, lean_box(0), v_l_1289_, v_m_1288_, v___f_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insertMany(lean_object* v_00_u03b1_1292_, lean_object* v_00_u03b2_1293_, lean_object* v_x_1294_, lean_object* v_x_1295_, lean_object* v_inst_1296_, lean_object* v_inst_1297_, lean_object* v_00_u03c1_1298_, lean_object* v_inst_1299_, lean_object* v_m_1300_, lean_object* v_l_1301_){
_start:
{
lean_object* v___f_1302_; lean_object* v___x_1303_; 
v___f_1302_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1302_, 0, v_x_1294_);
lean_closure_set(v___f_1302_, 1, v_x_1295_);
v___x_1303_ = lean_apply_4(v_inst_1299_, lean_box(0), v_l_1301_, v_m_1300_, v___f_1302_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertMany___redArg___lam__0(lean_object* v_x_1304_, lean_object* v_x_1305_, lean_object* v_x_1306_, lean_object* v_____s_1307_){
_start:
{
lean_object* v_fst_1308_; lean_object* v_snd_1309_; lean_object* v_m_1310_; lean_object* v___x_1311_; 
v_fst_1308_ = lean_ctor_get(v_x_1306_, 0);
lean_inc(v_fst_1308_);
v_snd_1309_ = lean_ctor_get(v_x_1306_, 1);
lean_inc(v_snd_1309_);
lean_dec_ref(v_x_1306_);
v_m_1310_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1304_, v_x_1305_, v_____s_1307_, v_fst_1308_, v_snd_1309_);
v___x_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1311_, 0, v_m_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertMany___redArg(lean_object* v_x_1312_, lean_object* v_x_1313_, lean_object* v_inst_1314_, lean_object* v_m_1315_, lean_object* v_l_1316_){
_start:
{
lean_object* v___f_1317_; lean_object* v___x_1318_; 
v___f_1317_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_Const_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1317_, 0, v_x_1312_);
lean_closure_set(v___f_1317_, 1, v_x_1313_);
v___x_1318_ = lean_apply_4(v_inst_1314_, lean_box(0), v_l_1316_, v_m_1315_, v___f_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertMany(lean_object* v_00_u03b1_1319_, lean_object* v_x_1320_, lean_object* v_x_1321_, lean_object* v_inst_1322_, lean_object* v_inst_1323_, lean_object* v_00_u03b2_1324_, lean_object* v_00_u03c1_1325_, lean_object* v_inst_1326_, lean_object* v_m_1327_, lean_object* v_l_1328_){
_start:
{
lean_object* v___f_1329_; lean_object* v___x_1330_; 
v___f_1329_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_Const_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1329_, 0, v_x_1320_);
lean_closure_set(v___f_1329_, 1, v_x_1321_);
v___x_1330_ = lean_apply_4(v_inst_1326_, lean_box(0), v_l_1328_, v_m_1327_, v___f_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg___lam__0(lean_object* v_x_1331_, lean_object* v_x_1332_, lean_object* v_a_1333_, lean_object* v_____s_1334_){
_start:
{
lean_object* v___x_1335_; lean_object* v_m_1336_; lean_object* v___x_1337_; 
v___x_1335_ = lean_box(0);
v_m_1336_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_1331_, v_x_1332_, v_____s_1334_, v_a_1333_, v___x_1335_);
v___x_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1337_, 0, v_m_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg(lean_object* v_x_1338_, lean_object* v_x_1339_, lean_object* v_inst_1340_, lean_object* v_m_1341_, lean_object* v_l_1342_){
_start:
{
lean_object* v___f_1343_; lean_object* v___x_1344_; 
v___f_1343_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1343_, 0, v_x_1338_);
lean_closure_set(v___f_1343_, 1, v_x_1339_);
v___x_1344_ = lean_apply_4(v_inst_1340_, lean_box(0), v_l_1342_, v_m_1341_, v___f_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertManyIfNewUnit(lean_object* v_00_u03b1_1345_, lean_object* v_x_1346_, lean_object* v_x_1347_, lean_object* v_inst_1348_, lean_object* v_inst_1349_, lean_object* v_00_u03c1_1350_, lean_object* v_inst_1351_, lean_object* v_m_1352_, lean_object* v_l_1353_){
_start:
{
lean_object* v___f_1354_; lean_object* v___x_1355_; 
v___f_1354_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1354_, 0, v_x_1346_);
lean_closure_set(v___f_1354_, 1, v_x_1347_);
v___x_1355_ = lean_apply_4(v_inst_1351_, lean_box(0), v_l_1353_, v_m_1352_, v___f_1354_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_union___redArg___lam__0(lean_object* v_x_1356_, lean_object* v_x_1357_, lean_object* v_a_1358_, lean_object* v_b_1359_, lean_object* v_acc_1360_){
_start:
{
lean_object* v_r_1361_; lean_object* v___x_1362_; 
v_r_1361_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_1356_, v_x_1357_, v_acc_1360_, v_a_1358_, v_b_1359_);
v___x_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1362_, 0, v_r_1361_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_union___redArg___lam__1(lean_object* v___x_1363_, lean_object* v___f_1364_, lean_object* v_a_1365_, lean_object* v_x_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v___x_1368_; 
v___x_1368_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1363_, v___f_1364_, v_a_1365_, v___y_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_union___redArg(lean_object* v_x_1390_, lean_object* v_x_1391_, lean_object* v_m_u2081_1392_, lean_object* v_m_u2082_1393_){
_start:
{
lean_object* v___x_1394_; lean_object* v_size_1395_; lean_object* v_buckets_1396_; lean_object* v_size_1397_; uint8_t v___x_1398_; 
v___x_1394_ = ((lean_object*)(l_Std_ExtDHashMap_union___redArg___closed__9));
v_size_1395_ = lean_ctor_get(v_m_u2081_1392_, 0);
v_buckets_1396_ = lean_ctor_get(v_m_u2081_1392_, 1);
v_size_1397_ = lean_ctor_get(v_m_u2082_1393_, 0);
v___x_1398_ = lean_nat_dec_le(v_size_1395_, v_size_1397_);
if (v___x_1398_ == 0)
{
lean_object* v___f_1399_; lean_object* v___x_1400_; 
v___f_1399_ = ((lean_object*)(l_Std_ExtDHashMap_union___redArg___closed__10));
v___x_1400_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1399_, v_x_1390_, v_x_1391_, v_m_u2081_1392_, v_m_u2082_1393_);
return v___x_1400_;
}
else
{
lean_object* v___f_1401_; lean_object* v___f_1402_; size_t v_sz_1403_; size_t v___x_1404_; lean_object* v___x_1405_; 
lean_inc_ref(v_buckets_1396_);
lean_dec(v_m_u2081_1392_);
v___f_1401_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1401_, 0, v_x_1390_);
lean_closure_set(v___f_1401_, 1, v_x_1391_);
v___f_1402_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1402_, 0, v___x_1394_);
lean_closure_set(v___f_1402_, 1, v___f_1401_);
v_sz_1403_ = lean_array_size(v_buckets_1396_);
v___x_1404_ = ((size_t)0ULL);
v___x_1405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1394_, v_buckets_1396_, v___f_1402_, v_sz_1403_, v___x_1404_, v_m_u2082_1393_);
return v___x_1405_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_union(lean_object* v_00_u03b1_1406_, lean_object* v_00_u03b2_1407_, lean_object* v_x_1408_, lean_object* v_x_1409_, lean_object* v_inst_1410_, lean_object* v_inst_1411_, lean_object* v_m_u2081_1412_, lean_object* v_m_u2082_1413_){
_start:
{
lean_object* v___x_1414_; lean_object* v_size_1415_; lean_object* v_buckets_1416_; lean_object* v_size_1417_; uint8_t v___x_1418_; 
v___x_1414_ = ((lean_object*)(l_Std_ExtDHashMap_union___redArg___closed__9));
v_size_1415_ = lean_ctor_get(v_m_u2081_1412_, 0);
v_buckets_1416_ = lean_ctor_get(v_m_u2081_1412_, 1);
v_size_1417_ = lean_ctor_get(v_m_u2082_1413_, 0);
v___x_1418_ = lean_nat_dec_le(v_size_1415_, v_size_1417_);
if (v___x_1418_ == 0)
{
lean_object* v___f_1419_; lean_object* v___x_1420_; 
v___f_1419_ = ((lean_object*)(l_Std_ExtDHashMap_union___redArg___closed__10));
v___x_1420_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1419_, v_x_1408_, v_x_1409_, v_m_u2081_1412_, v_m_u2082_1413_);
return v___x_1420_;
}
else
{
lean_object* v___f_1421_; lean_object* v___f_1422_; size_t v_sz_1423_; size_t v___x_1424_; lean_object* v___x_1425_; 
lean_inc_ref(v_buckets_1416_);
lean_dec(v_m_u2081_1412_);
v___f_1421_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1421_, 0, v_x_1408_);
lean_closure_set(v___f_1421_, 1, v_x_1409_);
v___f_1422_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1422_, 0, v___x_1414_);
lean_closure_set(v___f_1422_, 1, v___f_1421_);
v_sz_1423_ = lean_array_size(v_buckets_1416_);
v___x_1424_ = ((size_t)0ULL);
v___x_1425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1414_, v_buckets_1416_, v___f_1422_, v_sz_1423_, v___x_1424_, v_m_u2082_1413_);
return v___x_1425_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instUnionOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_1426_, lean_object* v_x_1427_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_union), 8, 6);
lean_closure_set(v___x_1428_, 0, lean_box(0));
lean_closure_set(v___x_1428_, 1, lean_box(0));
lean_closure_set(v___x_1428_, 2, v_x_1426_);
lean_closure_set(v___x_1428_, 3, v_x_1427_);
lean_closure_set(v___x_1428_, 4, lean_box(0));
lean_closure_set(v___x_1428_, 5, lean_box(0));
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instUnionOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1429_, lean_object* v_00_u03b2_1430_, lean_object* v_x_1431_, lean_object* v_x_1432_, lean_object* v_inst_1433_, lean_object* v_inst_1434_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_union), 8, 6);
lean_closure_set(v___x_1435_, 0, lean_box(0));
lean_closure_set(v___x_1435_, 1, lean_box(0));
lean_closure_set(v___x_1435_, 2, v_x_1431_);
lean_closure_set(v___x_1435_, 3, v_x_1432_);
lean_closure_set(v___x_1435_, 4, lean_box(0));
lean_closure_set(v___x_1435_, 5, lean_box(0));
return v___x_1435_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0(lean_object* v_x_1436_, lean_object* v_x_1437_, lean_object* v_inst_1438_, lean_object* v_m_u2081_1439_, lean_object* v_m_u2082_1440_){
_start:
{
uint8_t v___x_1441_; 
v___x_1441_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_x_1436_, v_x_1437_, v_inst_1438_, v_m_u2081_1439_, v_m_u2082_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0___boxed(lean_object* v_x_1442_, lean_object* v_x_1443_, lean_object* v_inst_1444_, lean_object* v_m_u2081_1445_, lean_object* v_m_u2082_1446_){
_start:
{
uint8_t v_res_1447_; lean_object* v_r_1448_; 
v_res_1447_ = l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0(v_x_1442_, v_x_1443_, v_inst_1444_, v_m_u2081_1445_, v_m_u2082_1446_);
v_r_1448_ = lean_box(v_res_1447_);
return v_r_1448_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg(lean_object* v_x_1449_, lean_object* v_x_1450_, lean_object* v_inst_1451_){
_start:
{
lean_object* v___f_1452_; 
v___f_1452_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1452_, 0, v_x_1449_);
lean_closure_set(v___f_1452_, 1, v_x_1450_);
lean_closure_set(v___f_1452_, 2, v_inst_1451_);
return v___f_1452_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instBEqOfLawfulBEq(lean_object* v_00_u03b1_1453_, lean_object* v_00_u03b2_1454_, lean_object* v_x_1455_, lean_object* v_x_1456_, lean_object* v_inst_1457_, lean_object* v_inst_1458_){
_start:
{
lean_object* v___f_1459_; 
v___f_1459_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1459_, 0, v_x_1455_);
lean_closure_set(v___f_1459_, 1, v_x_1456_);
lean_closure_set(v___f_1459_, 2, v_inst_1458_);
return v___f_1459_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___redArg(lean_object* v_inst_1460_, lean_object* v_inst_1461_, lean_object* v_inst_1462_, lean_object* v_x_1463_, lean_object* v_x_1464_){
_start:
{
uint8_t v___x_1465_; 
v___x_1465_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_inst_1460_, v_inst_1461_, v_inst_1462_, v_x_1463_, v_x_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___redArg___boxed(lean_object* v_inst_1466_, lean_object* v_inst_1467_, lean_object* v_inst_1468_, lean_object* v_x_1469_, lean_object* v_x_1470_){
_start:
{
uint8_t v_res_1471_; lean_object* v_r_1472_; 
v_res_1471_ = l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___redArg(v_inst_1466_, v_inst_1467_, v_inst_1468_, v_x_1469_, v_x_1470_);
v_r_1472_ = lean_box(v_res_1471_);
return v_r_1472_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq(lean_object* v_00_u03b1_1473_, lean_object* v_00_u03b2_1474_, lean_object* v_inst_1475_, lean_object* v_inst_1476_, lean_object* v_inst_1477_, lean_object* v_inst_1478_, lean_object* v_inst_1479_, lean_object* v_x_1480_, lean_object* v_x_1481_){
_start:
{
uint8_t v___x_1482_; 
v___x_1482_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_inst_1475_, v_inst_1477_, v_inst_1478_, v_x_1480_, v_x_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___boxed(lean_object* v_00_u03b1_1483_, lean_object* v_00_u03b2_1484_, lean_object* v_inst_1485_, lean_object* v_inst_1486_, lean_object* v_inst_1487_, lean_object* v_inst_1488_, lean_object* v_inst_1489_, lean_object* v_x_1490_, lean_object* v_x_1491_){
_start:
{
uint8_t v_res_1492_; lean_object* v_r_1493_; 
v_res_1492_ = l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq(v_00_u03b1_1483_, v_00_u03b2_1484_, v_inst_1485_, v_inst_1486_, v_inst_1487_, v_inst_1488_, v_inst_1489_, v_x_1490_, v_x_1491_);
v_r_1493_ = lean_box(v_res_1492_);
return v_r_1493_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_Const_beq___redArg(lean_object* v_x_1494_, lean_object* v_x_1495_, lean_object* v_inst_1496_, lean_object* v_m_u2081_1497_, lean_object* v_m_u2082_1498_){
_start:
{
uint8_t v___x_1499_; 
v___x_1499_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_x_1494_, v_x_1495_, v_inst_1496_, v_m_u2081_1497_, v_m_u2082_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_beq___redArg___boxed(lean_object* v_x_1500_, lean_object* v_x_1501_, lean_object* v_inst_1502_, lean_object* v_m_u2081_1503_, lean_object* v_m_u2082_1504_){
_start:
{
uint8_t v_res_1505_; lean_object* v_r_1506_; 
v_res_1505_ = l_Std_ExtDHashMap_Const_beq___redArg(v_x_1500_, v_x_1501_, v_inst_1502_, v_m_u2081_1503_, v_m_u2082_1504_);
v_r_1506_ = lean_box(v_res_1505_);
return v_r_1506_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_Const_beq(lean_object* v_00_u03b1_1507_, lean_object* v_x_1508_, lean_object* v_x_1509_, lean_object* v_00_u03b2_1510_, lean_object* v_inst_1511_, lean_object* v_inst_1512_, lean_object* v_inst_1513_, lean_object* v_m_u2081_1514_, lean_object* v_m_u2082_1515_){
_start:
{
uint8_t v___x_1516_; 
v___x_1516_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_x_1508_, v_x_1509_, v_inst_1513_, v_m_u2081_1514_, v_m_u2082_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_beq___boxed(lean_object* v_00_u03b1_1517_, lean_object* v_x_1518_, lean_object* v_x_1519_, lean_object* v_00_u03b2_1520_, lean_object* v_inst_1521_, lean_object* v_inst_1522_, lean_object* v_inst_1523_, lean_object* v_m_u2081_1524_, lean_object* v_m_u2082_1525_){
_start:
{
uint8_t v_res_1526_; lean_object* v_r_1527_; 
v_res_1526_ = l_Std_ExtDHashMap_Const_beq(v_00_u03b1_1517_, v_x_1518_, v_x_1519_, v_00_u03b2_1520_, v_inst_1521_, v_inst_1522_, v_inst_1523_, v_m_u2081_1524_, v_m_u2082_1525_);
v_r_1527_ = lean_box(v_res_1526_);
return v_r_1527_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_inter___redArg(lean_object* v_x_1528_, lean_object* v_x_1529_, lean_object* v_m_u2081_1530_, lean_object* v_m_u2082_1531_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_x_1528_, v_x_1529_, v_m_u2081_1530_, v_m_u2082_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_inter(lean_object* v_00_u03b1_1533_, lean_object* v_00_u03b2_1534_, lean_object* v_x_1535_, lean_object* v_x_1536_, lean_object* v_inst_1537_, lean_object* v_inst_1538_, lean_object* v_m_u2081_1539_, lean_object* v_m_u2082_1540_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_x_1535_, v_x_1536_, v_m_u2081_1539_, v_m_u2082_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInterOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_1542_, lean_object* v_x_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_inter), 8, 6);
lean_closure_set(v___x_1544_, 0, lean_box(0));
lean_closure_set(v___x_1544_, 1, lean_box(0));
lean_closure_set(v___x_1544_, 2, v_x_1542_);
lean_closure_set(v___x_1544_, 3, v_x_1543_);
lean_closure_set(v___x_1544_, 4, lean_box(0));
lean_closure_set(v___x_1544_, 5, lean_box(0));
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInterOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1545_, lean_object* v_00_u03b2_1546_, lean_object* v_x_1547_, lean_object* v_x_1548_, lean_object* v_inst_1549_, lean_object* v_inst_1550_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_inter), 8, 6);
lean_closure_set(v___x_1551_, 0, lean_box(0));
lean_closure_set(v___x_1551_, 1, lean_box(0));
lean_closure_set(v___x_1551_, 2, v_x_1547_);
lean_closure_set(v___x_1551_, 3, v_x_1548_);
lean_closure_set(v___x_1551_, 4, lean_box(0));
lean_closure_set(v___x_1551_, 5, lean_box(0));
return v___x_1551_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_diff___redArg___lam__0(lean_object* v_x_1552_, lean_object* v_x_1553_, lean_object* v_m_u2082_1554_, uint8_t v___x_1555_, lean_object* v_k_1556_, lean_object* v_x_1557_){
_start:
{
uint8_t v___x_1558_; 
v___x_1558_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_1552_, v_x_1553_, v_m_u2082_1554_, v_k_1556_);
if (v___x_1558_ == 0)
{
return v___x_1555_;
}
else
{
uint8_t v___x_1559_; 
v___x_1559_ = 0;
return v___x_1559_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_diff___redArg___lam__0___boxed(lean_object* v_x_1560_, lean_object* v_x_1561_, lean_object* v_m_u2082_1562_, lean_object* v___x_1563_, lean_object* v_k_1564_, lean_object* v_x_1565_){
_start:
{
uint8_t v___x_109__boxed_1566_; uint8_t v_res_1567_; lean_object* v_r_1568_; 
v___x_109__boxed_1566_ = lean_unbox(v___x_1563_);
v_res_1567_ = l_Std_ExtDHashMap_diff___redArg___lam__0(v_x_1560_, v_x_1561_, v_m_u2082_1562_, v___x_109__boxed_1566_, v_k_1564_, v_x_1565_);
lean_dec(v_x_1565_);
lean_dec(v_m_u2082_1562_);
v_r_1568_ = lean_box(v_res_1567_);
return v_r_1568_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_diff___redArg(lean_object* v_x_1569_, lean_object* v_x_1570_, lean_object* v_m_u2081_1571_, lean_object* v_m_u2082_1572_){
_start:
{
lean_object* v_size_1573_; lean_object* v_size_1574_; uint8_t v___x_1575_; 
v_size_1573_ = lean_ctor_get(v_m_u2081_1571_, 0);
v_size_1574_ = lean_ctor_get(v_m_u2082_1572_, 0);
v___x_1575_ = lean_nat_dec_le(v_size_1573_, v_size_1574_);
if (v___x_1575_ == 0)
{
lean_object* v___f_1576_; lean_object* v___x_1577_; 
v___f_1576_ = ((lean_object*)(l_Std_ExtDHashMap_union___redArg___closed__10));
v___x_1577_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1576_, v_x_1569_, v_x_1570_, v_m_u2081_1571_, v_m_u2082_1572_);
return v___x_1577_;
}
else
{
lean_object* v___x_1578_; lean_object* v___f_1579_; lean_object* v___x_1580_; 
v___x_1578_ = lean_box(v___x_1575_);
v___f_1579_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1579_, 0, v_x_1569_);
lean_closure_set(v___f_1579_, 1, v_x_1570_);
lean_closure_set(v___f_1579_, 2, v_m_u2082_1572_);
lean_closure_set(v___f_1579_, 3, v___x_1578_);
v___x_1580_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1579_, v_m_u2081_1571_);
return v___x_1580_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_diff(lean_object* v_00_u03b1_1581_, lean_object* v_00_u03b2_1582_, lean_object* v_x_1583_, lean_object* v_x_1584_, lean_object* v_inst_1585_, lean_object* v_inst_1586_, lean_object* v_m_u2081_1587_, lean_object* v_m_u2082_1588_){
_start:
{
lean_object* v_size_1589_; lean_object* v_size_1590_; uint8_t v___x_1591_; 
v_size_1589_ = lean_ctor_get(v_m_u2081_1587_, 0);
v_size_1590_ = lean_ctor_get(v_m_u2082_1588_, 0);
v___x_1591_ = lean_nat_dec_le(v_size_1589_, v_size_1590_);
if (v___x_1591_ == 0)
{
lean_object* v___f_1592_; lean_object* v___x_1593_; 
v___f_1592_ = ((lean_object*)(l_Std_ExtDHashMap_union___redArg___closed__10));
v___x_1593_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1592_, v_x_1583_, v_x_1584_, v_m_u2081_1587_, v_m_u2082_1588_);
return v___x_1593_;
}
else
{
lean_object* v___x_1594_; lean_object* v___f_1595_; lean_object* v___x_1596_; 
v___x_1594_ = lean_box(v___x_1591_);
v___f_1595_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1595_, 0, v_x_1583_);
lean_closure_set(v___f_1595_, 1, v_x_1584_);
lean_closure_set(v___f_1595_, 2, v_m_u2082_1588_);
lean_closure_set(v___f_1595_, 3, v___x_1594_);
v___x_1596_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1595_, v_m_u2081_1587_);
return v___x_1596_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instSDiffOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_1597_, lean_object* v_x_1598_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_diff), 8, 6);
lean_closure_set(v___x_1599_, 0, lean_box(0));
lean_closure_set(v___x_1599_, 1, lean_box(0));
lean_closure_set(v___x_1599_, 2, v_x_1597_);
lean_closure_set(v___x_1599_, 3, v_x_1598_);
lean_closure_set(v___x_1599_, 4, lean_box(0));
lean_closure_set(v___x_1599_, 5, lean_box(0));
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instSDiffOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1600_, lean_object* v_00_u03b2_1601_, lean_object* v_x_1602_, lean_object* v_x_1603_, lean_object* v_inst_1604_, lean_object* v_inst_1605_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_diff), 8, 6);
lean_closure_set(v___x_1606_, 0, lean_box(0));
lean_closure_set(v___x_1606_, 1, lean_box(0));
lean_closure_set(v___x_1606_, 2, v_x_1602_);
lean_closure_set(v___x_1606_, 3, v_x_1603_);
lean_closure_set(v___x_1606_, 4, lean_box(0));
lean_closure_set(v___x_1606_, 5, lean_box(0));
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_unitOfArray___redArg(lean_object* v_inst_1611_, lean_object* v_inst_1612_, lean_object* v_l_1613_){
_start:
{
lean_object* v___f_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___f_1614_ = ((lean_object*)(l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__1));
v___x_1615_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1);
v___x_1616_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1614_, v_inst_1611_, v_inst_1612_, v___x_1615_, v_l_1613_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_unitOfArray(lean_object* v_00_u03b1_1617_, lean_object* v_inst_1618_, lean_object* v_inst_1619_, lean_object* v_l_1620_){
_start:
{
lean_object* v___f_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___f_1621_ = ((lean_object*)(l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__1));
v___x_1622_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1);
v___x_1623_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1621_, v_inst_1618_, v_inst_1619_, v___x_1622_, v_l_1620_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_ofList___redArg(lean_object* v_inst_1628_, lean_object* v_inst_1629_, lean_object* v_l_1630_){
_start:
{
lean_object* v___f_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___f_1631_ = ((lean_object*)(l_Std_ExtDHashMap_ofList___redArg___closed__1));
v___x_1632_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1);
v___x_1633_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1631_, v_inst_1628_, v_inst_1629_, v___x_1632_, v_l_1630_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_ofList(lean_object* v_00_u03b1_1634_, lean_object* v_00_u03b2_1635_, lean_object* v_inst_1636_, lean_object* v_inst_1637_, lean_object* v_l_1638_){
_start:
{
lean_object* v___f_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___f_1639_ = ((lean_object*)(l_Std_ExtDHashMap_ofList___redArg___closed__1));
v___x_1640_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1);
v___x_1641_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1639_, v_inst_1636_, v_inst_1637_, v___x_1640_, v_l_1638_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_ofList___redArg(lean_object* v_inst_1642_, lean_object* v_inst_1643_, lean_object* v_l_1644_){
_start:
{
lean_object* v___f_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___f_1645_ = ((lean_object*)(l_Std_ExtDHashMap_ofList___redArg___closed__1));
v___x_1646_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1);
v___x_1647_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1645_, v_inst_1642_, v_inst_1643_, v___x_1646_, v_l_1644_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_ofList(lean_object* v_00_u03b1_1648_, lean_object* v_00_u03b2_1649_, lean_object* v_inst_1650_, lean_object* v_inst_1651_, lean_object* v_l_1652_){
_start:
{
lean_object* v___f_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___f_1653_ = ((lean_object*)(l_Std_ExtDHashMap_ofList___redArg___closed__1));
v___x_1654_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1);
v___x_1655_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1653_, v_inst_1650_, v_inst_1651_, v___x_1654_, v_l_1652_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_unitOfList___redArg(lean_object* v_inst_1656_, lean_object* v_inst_1657_, lean_object* v_l_1658_){
_start:
{
lean_object* v___f_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___f_1659_ = ((lean_object*)(l_Std_ExtDHashMap_ofList___redArg___closed__1));
v___x_1660_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1);
v___x_1661_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1659_, v_inst_1656_, v_inst_1657_, v___x_1660_, v_l_1658_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_unitOfList(lean_object* v_00_u03b1_1662_, lean_object* v_inst_1663_, lean_object* v_inst_1664_, lean_object* v_l_1665_){
_start:
{
lean_object* v___f_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___f_1666_ = ((lean_object*)(l_Std_ExtDHashMap_ofList___redArg___closed__1));
v___x_1667_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1);
v___x_1668_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1666_, v_inst_1663_, v_inst_1664_, v___x_1667_, v_l_1665_);
return v___x_1668_;
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
