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
lean_object* l_Std_ExtDHashMap_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1);
return v___x_120_;
}
}
LEAN_EXPORT void l_Std_ExtDHashMap_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_121_;
v_res_121_ = l_Std_ExtDHashMap_instEmptyCollection___redArg();
stack->m_obj
 = v_res_121_;
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instEmptyCollection___redArg___boxed(lean_object* v___dummy_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Std_ExtDHashMap_instEmptyCollection___redArg();
return v_res_123_;
}
}
static lean_object* _init_l_Std_ExtDHashMap_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_Std_ExtDHashMap_instEmptyCollection___redArg();
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instEmptyCollection(lean_object* v_00_u03b1_125_, lean_object* v_00_u03b2_126_, lean_object* v_inst_127_, lean_object* v_inst_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___closed__0, &l_Std_ExtDHashMap_instEmptyCollection___closed__0_once, _init_l_Std_ExtDHashMap_instEmptyCollection___closed__0);
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
lean_object* l_Std_ExtDHashMap_instInhabited___redArg(){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1);
return v___x_136_;
}
}
LEAN_EXPORT void l_Std_ExtDHashMap_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_137_;
v_res_137_ = l_Std_ExtDHashMap_instInhabited___redArg();
stack->m_obj
 = v_res_137_;
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInhabited___redArg___boxed(lean_object* v___dummy_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Std_ExtDHashMap_instInhabited___redArg();
return v_res_139_;
}
}
static lean_object* _init_l_Std_ExtDHashMap_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Std_ExtDHashMap_instInhabited___redArg();
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInhabited(lean_object* v_00_u03b1_141_, lean_object* v_00_u03b2_142_, lean_object* v_inst_143_, lean_object* v_inst_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = lean_obj_once(&l_Std_ExtDHashMap_instInhabited___closed__0, &l_Std_ExtDHashMap_instInhabited___closed__0_once, _init_l_Std_ExtDHashMap_instInhabited___closed__0);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInhabited___boxed(lean_object* v_00_u03b1_146_, lean_object* v_00_u03b2_147_, lean_object* v_inst_148_, lean_object* v_inst_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Std_ExtDHashMap_instInhabited(v_00_u03b1_146_, v_00_u03b2_147_, v_inst_148_, v_inst_149_);
lean_dec_ref(v_inst_149_);
lean_dec_ref(v_inst_148_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insert___redArg(lean_object* v_x_151_, lean_object* v_x_152_, lean_object* v_m_153_, lean_object* v_a_154_, lean_object* v_b_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_151_, v_x_152_, v_m_153_, v_a_154_, v_b_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insert(lean_object* v_00_u03b1_157_, lean_object* v_00_u03b2_158_, lean_object* v_x_159_, lean_object* v_x_160_, lean_object* v_inst_161_, lean_object* v_inst_162_, lean_object* v_m_163_, lean_object* v_a_164_, lean_object* v_b_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_159_, v_x_160_, v_m_163_, v_a_164_, v_b_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_167_, lean_object* v_x_168_, lean_object* v_x_169_){
_start:
{
lean_object* v_fst_170_; lean_object* v_snd_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v_fst_170_ = lean_ctor_get(v_x_169_, 0);
lean_inc(v_fst_170_);
v_snd_171_ = lean_ctor_get(v_x_169_, 1);
lean_inc(v_snd_171_);
lean_dec_ref(v_x_169_);
v___x_172_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1);
v___x_173_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_167_, v_x_168_, v___x_172_, v_fst_170_, v_snd_171_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_174_, lean_object* v_x_175_){
_start:
{
lean_object* v___f_176_; 
v___f_176_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_176_, 0, v_x_174_);
lean_closure_set(v___f_176_, 1, v_x_175_);
return v___f_176_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_177_, lean_object* v_00_u03b2_178_, lean_object* v_x_179_, lean_object* v_x_180_, lean_object* v_inst_181_, lean_object* v_inst_182_){
_start:
{
lean_object* v___f_183_; 
v___f_183_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_183_, 0, v_x_179_);
lean_closure_set(v___f_183_, 1, v_x_180_);
return v___f_183_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_184_, lean_object* v_x_185_, lean_object* v_x_186_, lean_object* v_x_187_){
_start:
{
lean_object* v_fst_188_; lean_object* v_snd_189_; lean_object* v___x_190_; 
v_fst_188_ = lean_ctor_get(v_x_186_, 0);
lean_inc(v_fst_188_);
v_snd_189_ = lean_ctor_get(v_x_186_, 1);
lean_inc(v_snd_189_);
lean_dec_ref(v_x_186_);
v___x_190_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_184_, v_x_185_, v_x_187_, v_fst_188_, v_snd_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_191_, lean_object* v_x_192_){
_start:
{
lean_object* v___f_193_; 
v___f_193_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_193_, 0, v_x_191_);
lean_closure_set(v___f_193_, 1, v_x_192_);
return v___f_193_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_194_, lean_object* v_00_u03b2_195_, lean_object* v_x_196_, lean_object* v_x_197_, lean_object* v_inst_198_, lean_object* v_inst_199_){
_start:
{
lean_object* v___f_200_; 
v___f_200_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_200_, 0, v_x_196_);
lean_closure_set(v___f_200_, 1, v_x_197_);
return v___f_200_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insertIfNew___redArg(lean_object* v_x_201_, lean_object* v_x_202_, lean_object* v_m_203_, lean_object* v_a_204_, lean_object* v_b_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_201_, v_x_202_, v_m_203_, v_a_204_, v_b_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insertIfNew(lean_object* v_00_u03b1_207_, lean_object* v_00_u03b2_208_, lean_object* v_x_209_, lean_object* v_x_210_, lean_object* v_inst_211_, lean_object* v_inst_212_, lean_object* v_m_213_, lean_object* v_a_214_, lean_object* v_b_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_209_, v_x_210_, v_m_213_, v_a_214_, v_b_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_containsThenInsert___redArg(lean_object* v_x_217_, lean_object* v_x_218_, lean_object* v_m_219_, lean_object* v_a_220_, lean_object* v_b_221_){
_start:
{
lean_object* v_size_222_; lean_object* v_buckets_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_274_; 
v_size_222_ = lean_ctor_get(v_m_219_, 0);
v_buckets_223_ = lean_ctor_get(v_m_219_, 1);
v_isSharedCheck_274_ = !lean_is_exclusive(v_m_219_);
if (v_isSharedCheck_274_ == 0)
{
v___x_225_ = v_m_219_;
v_isShared_226_ = v_isSharedCheck_274_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_buckets_223_);
lean_inc(v_size_222_);
lean_dec(v_m_219_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_274_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; lean_object* v___x_228_; uint64_t v___x_229_; uint64_t v___x_230_; uint64_t v___x_231_; uint64_t v___x_232_; uint64_t v_fold_233_; uint64_t v___x_234_; uint64_t v___x_235_; uint64_t v___x_236_; size_t v___x_237_; size_t v___x_238_; size_t v___x_239_; size_t v___x_240_; size_t v___x_241_; lean_object* v_bkt_242_; uint8_t v___x_243_; 
v___x_227_ = lean_array_get_size(v_buckets_223_);
lean_inc_ref(v_x_218_);
lean_inc_n(v_a_220_, 2);
v___x_228_ = lean_apply_1(v_x_218_, v_a_220_);
v___x_229_ = 32ULL;
v___x_230_ = lean_unbox_uint64(v___x_228_);
v___x_231_ = lean_uint64_shift_right(v___x_230_, v___x_229_);
v___x_232_ = lean_unbox_uint64(v___x_228_);
lean_dec_ref(v___x_228_);
v_fold_233_ = lean_uint64_xor(v___x_232_, v___x_231_);
v___x_234_ = 16ULL;
v___x_235_ = lean_uint64_shift_right(v_fold_233_, v___x_234_);
v___x_236_ = lean_uint64_xor(v_fold_233_, v___x_235_);
v___x_237_ = lean_uint64_to_usize(v___x_236_);
v___x_238_ = lean_usize_of_nat(v___x_227_);
v___x_239_ = ((size_t)1ULL);
v___x_240_ = lean_usize_sub(v___x_238_, v___x_239_);
v___x_241_ = lean_usize_land(v___x_237_, v___x_240_);
v_bkt_242_ = lean_array_uget_borrowed(v_buckets_223_, v___x_241_);
lean_inc(v_bkt_242_);
lean_inc_ref(v_x_217_);
v___x_243_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_217_, v_a_220_, v_bkt_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; lean_object* v_size_x27_245_; lean_object* v___x_246_; lean_object* v_buckets_x27_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
lean_dec_ref(v_x_217_);
v___x_244_ = lean_unsigned_to_nat(1u);
v_size_x27_245_ = lean_nat_add(v_size_222_, v___x_244_);
lean_dec(v_size_222_);
lean_inc(v_bkt_242_);
v___x_246_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_246_, 0, v_a_220_);
lean_ctor_set(v___x_246_, 1, v_b_221_);
lean_ctor_set(v___x_246_, 2, v_bkt_242_);
v_buckets_x27_247_ = lean_array_uset(v_buckets_223_, v___x_241_, v___x_246_);
v___x_248_ = lean_unsigned_to_nat(4u);
v___x_249_ = lean_nat_mul(v_size_x27_245_, v___x_248_);
v___x_250_ = lean_unsigned_to_nat(3u);
v___x_251_ = lean_nat_div(v___x_249_, v___x_250_);
lean_dec(v___x_249_);
v___x_252_ = lean_array_get_size(v_buckets_x27_247_);
v___x_253_ = lean_nat_dec_le(v___x_251_, v___x_252_);
lean_dec(v___x_251_);
if (v___x_253_ == 0)
{
lean_object* v_val_254_; lean_object* v___x_256_; 
v_val_254_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_218_, v_buckets_x27_247_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 1, v_val_254_);
lean_ctor_set(v___x_225_, 0, v_size_x27_245_);
v___x_256_ = v___x_225_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_size_x27_245_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_val_254_);
v___x_256_ = v_reuseFailAlloc_259_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_box(v___x_243_);
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
lean_ctor_set(v___x_258_, 1, v___x_256_);
return v___x_258_;
}
}
else
{
lean_object* v___x_261_; 
lean_dec_ref(v_x_218_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 1, v_buckets_x27_247_);
lean_ctor_set(v___x_225_, 0, v_size_x27_245_);
v___x_261_ = v___x_225_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_size_x27_245_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v_buckets_x27_247_);
v___x_261_ = v_reuseFailAlloc_264_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = lean_box(v___x_243_);
v___x_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v___x_261_);
return v___x_263_;
}
}
}
else
{
lean_object* v___x_265_; lean_object* v_buckets_x27_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_270_; 
lean_inc(v_bkt_242_);
lean_dec_ref(v_x_218_);
v___x_265_ = lean_box(0);
v_buckets_x27_266_ = lean_array_uset(v_buckets_223_, v___x_241_, v___x_265_);
v___x_267_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_x_217_, v_a_220_, v_b_221_, v_bkt_242_);
v___x_268_ = lean_array_uset(v_buckets_x27_266_, v___x_241_, v___x_267_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 1, v___x_268_);
v___x_270_ = v___x_225_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_size_222_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v___x_268_);
v___x_270_ = v_reuseFailAlloc_273_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = lean_box(v___x_243_);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v___x_270_);
return v___x_272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_containsThenInsert(lean_object* v_00_u03b1_275_, lean_object* v_00_u03b2_276_, lean_object* v_x_277_, lean_object* v_x_278_, lean_object* v_inst_279_, lean_object* v_inst_280_, lean_object* v_m_281_, lean_object* v_a_282_, lean_object* v_b_283_){
_start:
{
lean_object* v_size_284_; lean_object* v_buckets_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_336_; 
v_size_284_ = lean_ctor_get(v_m_281_, 0);
v_buckets_285_ = lean_ctor_get(v_m_281_, 1);
v_isSharedCheck_336_ = !lean_is_exclusive(v_m_281_);
if (v_isSharedCheck_336_ == 0)
{
v___x_287_ = v_m_281_;
v_isShared_288_ = v_isSharedCheck_336_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_buckets_285_);
lean_inc(v_size_284_);
lean_dec(v_m_281_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_336_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_289_; lean_object* v___x_290_; uint64_t v___x_291_; uint64_t v___x_292_; uint64_t v___x_293_; uint64_t v___x_294_; uint64_t v_fold_295_; uint64_t v___x_296_; uint64_t v___x_297_; uint64_t v___x_298_; size_t v___x_299_; size_t v___x_300_; size_t v___x_301_; size_t v___x_302_; size_t v___x_303_; lean_object* v_bkt_304_; uint8_t v___x_305_; 
v___x_289_ = lean_array_get_size(v_buckets_285_);
lean_inc_ref(v_x_278_);
lean_inc_n(v_a_282_, 2);
v___x_290_ = lean_apply_1(v_x_278_, v_a_282_);
v___x_291_ = 32ULL;
v___x_292_ = lean_unbox_uint64(v___x_290_);
v___x_293_ = lean_uint64_shift_right(v___x_292_, v___x_291_);
v___x_294_ = lean_unbox_uint64(v___x_290_);
lean_dec_ref(v___x_290_);
v_fold_295_ = lean_uint64_xor(v___x_294_, v___x_293_);
v___x_296_ = 16ULL;
v___x_297_ = lean_uint64_shift_right(v_fold_295_, v___x_296_);
v___x_298_ = lean_uint64_xor(v_fold_295_, v___x_297_);
v___x_299_ = lean_uint64_to_usize(v___x_298_);
v___x_300_ = lean_usize_of_nat(v___x_289_);
v___x_301_ = ((size_t)1ULL);
v___x_302_ = lean_usize_sub(v___x_300_, v___x_301_);
v___x_303_ = lean_usize_land(v___x_299_, v___x_302_);
v_bkt_304_ = lean_array_uget_borrowed(v_buckets_285_, v___x_303_);
lean_inc(v_bkt_304_);
lean_inc_ref(v_x_277_);
v___x_305_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_277_, v_a_282_, v_bkt_304_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; lean_object* v_size_x27_307_; lean_object* v___x_308_; lean_object* v_buckets_x27_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
lean_dec_ref(v_x_277_);
v___x_306_ = lean_unsigned_to_nat(1u);
v_size_x27_307_ = lean_nat_add(v_size_284_, v___x_306_);
lean_dec(v_size_284_);
lean_inc(v_bkt_304_);
v___x_308_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_308_, 0, v_a_282_);
lean_ctor_set(v___x_308_, 1, v_b_283_);
lean_ctor_set(v___x_308_, 2, v_bkt_304_);
v_buckets_x27_309_ = lean_array_uset(v_buckets_285_, v___x_303_, v___x_308_);
v___x_310_ = lean_unsigned_to_nat(4u);
v___x_311_ = lean_nat_mul(v_size_x27_307_, v___x_310_);
v___x_312_ = lean_unsigned_to_nat(3u);
v___x_313_ = lean_nat_div(v___x_311_, v___x_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_array_get_size(v_buckets_x27_309_);
v___x_315_ = lean_nat_dec_le(v___x_313_, v___x_314_);
lean_dec(v___x_313_);
if (v___x_315_ == 0)
{
lean_object* v_val_316_; lean_object* v___x_318_; 
v_val_316_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_278_, v_buckets_x27_309_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 1, v_val_316_);
lean_ctor_set(v___x_287_, 0, v_size_x27_307_);
v___x_318_ = v___x_287_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_size_x27_307_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_val_316_);
v___x_318_ = v_reuseFailAlloc_321_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_box(v___x_305_);
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v___x_318_);
return v___x_320_;
}
}
else
{
lean_object* v___x_323_; 
lean_dec_ref(v_x_278_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 1, v_buckets_x27_309_);
lean_ctor_set(v___x_287_, 0, v_size_x27_307_);
v___x_323_ = v___x_287_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_size_x27_307_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_buckets_x27_309_);
v___x_323_ = v_reuseFailAlloc_326_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_box(v___x_305_);
v___x_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set(v___x_325_, 1, v___x_323_);
return v___x_325_;
}
}
}
else
{
lean_object* v___x_327_; lean_object* v_buckets_x27_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_332_; 
lean_inc(v_bkt_304_);
lean_dec_ref(v_x_278_);
v___x_327_ = lean_box(0);
v_buckets_x27_328_ = lean_array_uset(v_buckets_285_, v___x_303_, v___x_327_);
v___x_329_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_x_277_, v_a_282_, v_b_283_, v_bkt_304_);
v___x_330_ = lean_array_uset(v_buckets_x27_328_, v___x_303_, v___x_329_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 1, v___x_330_);
v___x_332_ = v___x_287_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_size_284_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v___x_330_);
v___x_332_ = v_reuseFailAlloc_335_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_box(v___x_305_);
v___x_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v___x_332_);
return v___x_334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_containsThenInsertIfNew___redArg(lean_object* v_x_337_, lean_object* v_x_338_, lean_object* v_m_339_, lean_object* v_a_340_, lean_object* v_b_341_){
_start:
{
lean_object* v_size_342_; lean_object* v_buckets_343_; lean_object* v___x_344_; lean_object* v___x_345_; uint64_t v___x_346_; uint64_t v___x_347_; uint64_t v___x_348_; uint64_t v___x_349_; uint64_t v_fold_350_; uint64_t v___x_351_; uint64_t v___x_352_; uint64_t v___x_353_; size_t v___x_354_; size_t v___x_355_; size_t v___x_356_; size_t v___x_357_; size_t v___x_358_; lean_object* v_bkt_359_; uint8_t v___x_360_; 
v_size_342_ = lean_ctor_get(v_m_339_, 0);
v_buckets_343_ = lean_ctor_get(v_m_339_, 1);
v___x_344_ = lean_array_get_size(v_buckets_343_);
lean_inc_ref(v_x_338_);
lean_inc_n(v_a_340_, 2);
v___x_345_ = lean_apply_1(v_x_338_, v_a_340_);
v___x_346_ = 32ULL;
v___x_347_ = lean_unbox_uint64(v___x_345_);
v___x_348_ = lean_uint64_shift_right(v___x_347_, v___x_346_);
v___x_349_ = lean_unbox_uint64(v___x_345_);
lean_dec_ref(v___x_345_);
v_fold_350_ = lean_uint64_xor(v___x_349_, v___x_348_);
v___x_351_ = 16ULL;
v___x_352_ = lean_uint64_shift_right(v_fold_350_, v___x_351_);
v___x_353_ = lean_uint64_xor(v_fold_350_, v___x_352_);
v___x_354_ = lean_uint64_to_usize(v___x_353_);
v___x_355_ = lean_usize_of_nat(v___x_344_);
v___x_356_ = ((size_t)1ULL);
v___x_357_ = lean_usize_sub(v___x_355_, v___x_356_);
v___x_358_ = lean_usize_land(v___x_354_, v___x_357_);
v_bkt_359_ = lean_array_uget_borrowed(v_buckets_343_, v___x_358_);
lean_inc(v_bkt_359_);
v___x_360_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_337_, v_a_340_, v_bkt_359_);
if (v___x_360_ == 0)
{
lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_385_; 
lean_inc_ref(v_buckets_343_);
lean_inc(v_size_342_);
v_isSharedCheck_385_ = !lean_is_exclusive(v_m_339_);
if (v_isSharedCheck_385_ == 0)
{
lean_object* v_unused_386_; lean_object* v_unused_387_; 
v_unused_386_ = lean_ctor_get(v_m_339_, 1);
lean_dec(v_unused_386_);
v_unused_387_ = lean_ctor_get(v_m_339_, 0);
lean_dec(v_unused_387_);
v___x_362_ = v_m_339_;
v_isShared_363_ = v_isSharedCheck_385_;
goto v_resetjp_361_;
}
else
{
lean_dec(v_m_339_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_385_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_364_; lean_object* v_size_x27_365_; lean_object* v___x_366_; lean_object* v_buckets_x27_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_364_ = lean_unsigned_to_nat(1u);
v_size_x27_365_ = lean_nat_add(v_size_342_, v___x_364_);
lean_dec(v_size_342_);
lean_inc(v_bkt_359_);
v___x_366_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_366_, 0, v_a_340_);
lean_ctor_set(v___x_366_, 1, v_b_341_);
lean_ctor_set(v___x_366_, 2, v_bkt_359_);
v_buckets_x27_367_ = lean_array_uset(v_buckets_343_, v___x_358_, v___x_366_);
v___x_368_ = lean_unsigned_to_nat(4u);
v___x_369_ = lean_nat_mul(v_size_x27_365_, v___x_368_);
v___x_370_ = lean_unsigned_to_nat(3u);
v___x_371_ = lean_nat_div(v___x_369_, v___x_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_array_get_size(v_buckets_x27_367_);
v___x_373_ = lean_nat_dec_le(v___x_371_, v___x_372_);
lean_dec(v___x_371_);
if (v___x_373_ == 0)
{
lean_object* v_val_374_; lean_object* v___x_376_; 
v_val_374_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_338_, v_buckets_x27_367_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 1, v_val_374_);
lean_ctor_set(v___x_362_, 0, v_size_x27_365_);
v___x_376_ = v___x_362_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_size_x27_365_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_val_374_);
v___x_376_ = v_reuseFailAlloc_379_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_box(v___x_360_);
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
lean_ctor_set(v___x_378_, 1, v___x_376_);
return v___x_378_;
}
}
else
{
lean_object* v___x_381_; 
lean_dec_ref(v_x_338_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 1, v_buckets_x27_367_);
lean_ctor_set(v___x_362_, 0, v_size_x27_365_);
v___x_381_ = v___x_362_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_size_x27_365_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v_buckets_x27_367_);
v___x_381_ = v_reuseFailAlloc_384_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_box(v___x_360_);
v___x_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v___x_381_);
return v___x_383_;
}
}
}
}
else
{
lean_object* v___x_388_; lean_object* v___x_389_; 
lean_dec(v_b_341_);
lean_dec(v_a_340_);
lean_dec_ref(v_x_338_);
v___x_388_ = lean_box(v___x_360_);
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set(v___x_389_, 1, v_m_339_);
return v___x_389_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_containsThenInsertIfNew(lean_object* v_00_u03b1_390_, lean_object* v_00_u03b2_391_, lean_object* v_x_392_, lean_object* v_x_393_, lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_m_396_, lean_object* v_a_397_, lean_object* v_b_398_){
_start:
{
lean_object* v_size_399_; lean_object* v_buckets_400_; lean_object* v___x_401_; lean_object* v___x_402_; uint64_t v___x_403_; uint64_t v___x_404_; uint64_t v___x_405_; uint64_t v___x_406_; uint64_t v_fold_407_; uint64_t v___x_408_; uint64_t v___x_409_; uint64_t v___x_410_; size_t v___x_411_; size_t v___x_412_; size_t v___x_413_; size_t v___x_414_; size_t v___x_415_; lean_object* v_bkt_416_; uint8_t v___x_417_; 
v_size_399_ = lean_ctor_get(v_m_396_, 0);
v_buckets_400_ = lean_ctor_get(v_m_396_, 1);
v___x_401_ = lean_array_get_size(v_buckets_400_);
lean_inc_ref(v_x_393_);
lean_inc_n(v_a_397_, 2);
v___x_402_ = lean_apply_1(v_x_393_, v_a_397_);
v___x_403_ = 32ULL;
v___x_404_ = lean_unbox_uint64(v___x_402_);
v___x_405_ = lean_uint64_shift_right(v___x_404_, v___x_403_);
v___x_406_ = lean_unbox_uint64(v___x_402_);
lean_dec_ref(v___x_402_);
v_fold_407_ = lean_uint64_xor(v___x_406_, v___x_405_);
v___x_408_ = 16ULL;
v___x_409_ = lean_uint64_shift_right(v_fold_407_, v___x_408_);
v___x_410_ = lean_uint64_xor(v_fold_407_, v___x_409_);
v___x_411_ = lean_uint64_to_usize(v___x_410_);
v___x_412_ = lean_usize_of_nat(v___x_401_);
v___x_413_ = ((size_t)1ULL);
v___x_414_ = lean_usize_sub(v___x_412_, v___x_413_);
v___x_415_ = lean_usize_land(v___x_411_, v___x_414_);
v_bkt_416_ = lean_array_uget_borrowed(v_buckets_400_, v___x_415_);
lean_inc(v_bkt_416_);
v___x_417_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_392_, v_a_397_, v_bkt_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_442_; 
lean_inc_ref(v_buckets_400_);
lean_inc(v_size_399_);
v_isSharedCheck_442_ = !lean_is_exclusive(v_m_396_);
if (v_isSharedCheck_442_ == 0)
{
lean_object* v_unused_443_; lean_object* v_unused_444_; 
v_unused_443_ = lean_ctor_get(v_m_396_, 1);
lean_dec(v_unused_443_);
v_unused_444_ = lean_ctor_get(v_m_396_, 0);
lean_dec(v_unused_444_);
v___x_419_ = v_m_396_;
v_isShared_420_ = v_isSharedCheck_442_;
goto v_resetjp_418_;
}
else
{
lean_dec(v_m_396_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_442_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_421_; lean_object* v_size_x27_422_; lean_object* v___x_423_; lean_object* v_buckets_x27_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_421_ = lean_unsigned_to_nat(1u);
v_size_x27_422_ = lean_nat_add(v_size_399_, v___x_421_);
lean_dec(v_size_399_);
lean_inc(v_bkt_416_);
v___x_423_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_423_, 0, v_a_397_);
lean_ctor_set(v___x_423_, 1, v_b_398_);
lean_ctor_set(v___x_423_, 2, v_bkt_416_);
v_buckets_x27_424_ = lean_array_uset(v_buckets_400_, v___x_415_, v___x_423_);
v___x_425_ = lean_unsigned_to_nat(4u);
v___x_426_ = lean_nat_mul(v_size_x27_422_, v___x_425_);
v___x_427_ = lean_unsigned_to_nat(3u);
v___x_428_ = lean_nat_div(v___x_426_, v___x_427_);
lean_dec(v___x_426_);
v___x_429_ = lean_array_get_size(v_buckets_x27_424_);
v___x_430_ = lean_nat_dec_le(v___x_428_, v___x_429_);
lean_dec(v___x_428_);
if (v___x_430_ == 0)
{
lean_object* v_val_431_; lean_object* v___x_433_; 
v_val_431_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_393_, v_buckets_x27_424_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 1, v_val_431_);
lean_ctor_set(v___x_419_, 0, v_size_x27_422_);
v___x_433_ = v___x_419_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_size_x27_422_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_val_431_);
v___x_433_ = v_reuseFailAlloc_436_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_box(v___x_417_);
v___x_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
lean_ctor_set(v___x_435_, 1, v___x_433_);
return v___x_435_;
}
}
else
{
lean_object* v___x_438_; 
lean_dec_ref(v_x_393_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 1, v_buckets_x27_424_);
lean_ctor_set(v___x_419_, 0, v_size_x27_422_);
v___x_438_ = v___x_419_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_size_x27_422_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_buckets_x27_424_);
v___x_438_ = v_reuseFailAlloc_441_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = lean_box(v___x_417_);
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v___x_438_);
return v___x_440_;
}
}
}
}
else
{
lean_object* v___x_445_; lean_object* v___x_446_; 
lean_dec(v_b_398_);
lean_dec(v_a_397_);
lean_dec_ref(v_x_393_);
v___x_445_ = lean_box(v___x_417_);
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
lean_ctor_set(v___x_446_, 1, v_m_396_);
return v___x_446_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getThenInsertIfNew_x3f___redArg(lean_object* v_x_447_, lean_object* v_x_448_, lean_object* v_m_449_, lean_object* v_a_450_, lean_object* v_b_451_){
_start:
{
lean_object* v_size_452_; lean_object* v_buckets_453_; lean_object* v___x_454_; lean_object* v___x_455_; uint64_t v___x_456_; uint64_t v___x_457_; uint64_t v___x_458_; uint64_t v___x_459_; uint64_t v_fold_460_; uint64_t v___x_461_; uint64_t v___x_462_; uint64_t v___x_463_; size_t v___x_464_; size_t v___x_465_; size_t v___x_466_; size_t v___x_467_; size_t v___x_468_; lean_object* v_bkt_469_; lean_object* v___x_470_; 
v_size_452_ = lean_ctor_get(v_m_449_, 0);
v_buckets_453_ = lean_ctor_get(v_m_449_, 1);
v___x_454_ = lean_array_get_size(v_buckets_453_);
lean_inc_ref(v_x_448_);
lean_inc_n(v_a_450_, 2);
v___x_455_ = lean_apply_1(v_x_448_, v_a_450_);
v___x_456_ = 32ULL;
v___x_457_ = lean_unbox_uint64(v___x_455_);
v___x_458_ = lean_uint64_shift_right(v___x_457_, v___x_456_);
v___x_459_ = lean_unbox_uint64(v___x_455_);
lean_dec_ref(v___x_455_);
v_fold_460_ = lean_uint64_xor(v___x_459_, v___x_458_);
v___x_461_ = 16ULL;
v___x_462_ = lean_uint64_shift_right(v_fold_460_, v___x_461_);
v___x_463_ = lean_uint64_xor(v_fold_460_, v___x_462_);
v___x_464_ = lean_uint64_to_usize(v___x_463_);
v___x_465_ = lean_usize_of_nat(v___x_454_);
v___x_466_ = ((size_t)1ULL);
v___x_467_ = lean_usize_sub(v___x_465_, v___x_466_);
v___x_468_ = lean_usize_land(v___x_464_, v___x_467_);
v_bkt_469_ = lean_array_uget_borrowed(v_buckets_453_, v___x_468_);
lean_inc(v_bkt_469_);
v___x_470_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(v_x_447_, v_a_450_, v_bkt_469_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_493_; 
lean_inc_ref(v_buckets_453_);
lean_inc(v_size_452_);
v_isSharedCheck_493_ = !lean_is_exclusive(v_m_449_);
if (v_isSharedCheck_493_ == 0)
{
lean_object* v_unused_494_; lean_object* v_unused_495_; 
v_unused_494_ = lean_ctor_get(v_m_449_, 1);
lean_dec(v_unused_494_);
v_unused_495_ = lean_ctor_get(v_m_449_, 0);
lean_dec(v_unused_495_);
v___x_472_ = v_m_449_;
v_isShared_473_ = v_isSharedCheck_493_;
goto v_resetjp_471_;
}
else
{
lean_dec(v_m_449_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_493_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v_size_x27_475_; lean_object* v___x_476_; lean_object* v_buckets_x27_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_474_ = lean_unsigned_to_nat(1u);
v_size_x27_475_ = lean_nat_add(v_size_452_, v___x_474_);
lean_dec(v_size_452_);
lean_inc(v_bkt_469_);
v___x_476_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_476_, 0, v_a_450_);
lean_ctor_set(v___x_476_, 1, v_b_451_);
lean_ctor_set(v___x_476_, 2, v_bkt_469_);
v_buckets_x27_477_ = lean_array_uset(v_buckets_453_, v___x_468_, v___x_476_);
v___x_478_ = lean_unsigned_to_nat(4u);
v___x_479_ = lean_nat_mul(v_size_x27_475_, v___x_478_);
v___x_480_ = lean_unsigned_to_nat(3u);
v___x_481_ = lean_nat_div(v___x_479_, v___x_480_);
lean_dec(v___x_479_);
v___x_482_ = lean_array_get_size(v_buckets_x27_477_);
v___x_483_ = lean_nat_dec_le(v___x_481_, v___x_482_);
lean_dec(v___x_481_);
if (v___x_483_ == 0)
{
lean_object* v_val_484_; lean_object* v___x_486_; 
v_val_484_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_448_, v_buckets_x27_477_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 1, v_val_484_);
lean_ctor_set(v___x_472_, 0, v_size_x27_475_);
v___x_486_ = v___x_472_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_size_x27_475_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_val_484_);
v___x_486_ = v_reuseFailAlloc_488_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_487_; 
v___x_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_470_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
return v___x_487_;
}
}
else
{
lean_object* v___x_490_; 
lean_dec_ref(v_x_448_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 1, v_buckets_x27_477_);
lean_ctor_set(v___x_472_, 0, v_size_x27_475_);
v___x_490_ = v___x_472_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_size_x27_475_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_buckets_x27_477_);
v___x_490_ = v_reuseFailAlloc_492_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_491_; 
v___x_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_470_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
return v___x_491_;
}
}
}
}
else
{
lean_object* v___x_496_; 
lean_dec(v_b_451_);
lean_dec(v_a_450_);
lean_dec_ref(v_x_448_);
v___x_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_470_);
lean_ctor_set(v___x_496_, 1, v_m_449_);
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_497_, lean_object* v_00_u03b2_498_, lean_object* v_x_499_, lean_object* v_x_500_, lean_object* v_inst_501_, lean_object* v_m_502_, lean_object* v_a_503_, lean_object* v_b_504_){
_start:
{
lean_object* v_size_505_; lean_object* v_buckets_506_; lean_object* v___x_507_; lean_object* v___x_508_; uint64_t v___x_509_; uint64_t v___x_510_; uint64_t v___x_511_; uint64_t v___x_512_; uint64_t v_fold_513_; uint64_t v___x_514_; uint64_t v___x_515_; uint64_t v___x_516_; size_t v___x_517_; size_t v___x_518_; size_t v___x_519_; size_t v___x_520_; size_t v___x_521_; lean_object* v_bkt_522_; lean_object* v___x_523_; 
v_size_505_ = lean_ctor_get(v_m_502_, 0);
v_buckets_506_ = lean_ctor_get(v_m_502_, 1);
v___x_507_ = lean_array_get_size(v_buckets_506_);
lean_inc_ref(v_x_500_);
lean_inc_n(v_a_503_, 2);
v___x_508_ = lean_apply_1(v_x_500_, v_a_503_);
v___x_509_ = 32ULL;
v___x_510_ = lean_unbox_uint64(v___x_508_);
v___x_511_ = lean_uint64_shift_right(v___x_510_, v___x_509_);
v___x_512_ = lean_unbox_uint64(v___x_508_);
lean_dec_ref(v___x_508_);
v_fold_513_ = lean_uint64_xor(v___x_512_, v___x_511_);
v___x_514_ = 16ULL;
v___x_515_ = lean_uint64_shift_right(v_fold_513_, v___x_514_);
v___x_516_ = lean_uint64_xor(v_fold_513_, v___x_515_);
v___x_517_ = lean_uint64_to_usize(v___x_516_);
v___x_518_ = lean_usize_of_nat(v___x_507_);
v___x_519_ = ((size_t)1ULL);
v___x_520_ = lean_usize_sub(v___x_518_, v___x_519_);
v___x_521_ = lean_usize_land(v___x_517_, v___x_520_);
v_bkt_522_ = lean_array_uget_borrowed(v_buckets_506_, v___x_521_);
lean_inc(v_bkt_522_);
v___x_523_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(v_x_499_, v_a_503_, v_bkt_522_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_546_; 
lean_inc_ref(v_buckets_506_);
lean_inc(v_size_505_);
v_isSharedCheck_546_ = !lean_is_exclusive(v_m_502_);
if (v_isSharedCheck_546_ == 0)
{
lean_object* v_unused_547_; lean_object* v_unused_548_; 
v_unused_547_ = lean_ctor_get(v_m_502_, 1);
lean_dec(v_unused_547_);
v_unused_548_ = lean_ctor_get(v_m_502_, 0);
lean_dec(v_unused_548_);
v___x_525_ = v_m_502_;
v_isShared_526_ = v_isSharedCheck_546_;
goto v_resetjp_524_;
}
else
{
lean_dec(v_m_502_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_546_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v_size_x27_528_; lean_object* v___x_529_; lean_object* v_buckets_x27_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_527_ = lean_unsigned_to_nat(1u);
v_size_x27_528_ = lean_nat_add(v_size_505_, v___x_527_);
lean_dec(v_size_505_);
lean_inc(v_bkt_522_);
v___x_529_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_529_, 0, v_a_503_);
lean_ctor_set(v___x_529_, 1, v_b_504_);
lean_ctor_set(v___x_529_, 2, v_bkt_522_);
v_buckets_x27_530_ = lean_array_uset(v_buckets_506_, v___x_521_, v___x_529_);
v___x_531_ = lean_unsigned_to_nat(4u);
v___x_532_ = lean_nat_mul(v_size_x27_528_, v___x_531_);
v___x_533_ = lean_unsigned_to_nat(3u);
v___x_534_ = lean_nat_div(v___x_532_, v___x_533_);
lean_dec(v___x_532_);
v___x_535_ = lean_array_get_size(v_buckets_x27_530_);
v___x_536_ = lean_nat_dec_le(v___x_534_, v___x_535_);
lean_dec(v___x_534_);
if (v___x_536_ == 0)
{
lean_object* v_val_537_; lean_object* v___x_539_; 
v_val_537_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_500_, v_buckets_x27_530_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 1, v_val_537_);
lean_ctor_set(v___x_525_, 0, v_size_x27_528_);
v___x_539_ = v___x_525_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_size_x27_528_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_val_537_);
v___x_539_ = v_reuseFailAlloc_541_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_540_; 
v___x_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_523_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
return v___x_540_;
}
}
else
{
lean_object* v___x_543_; 
lean_dec_ref(v_x_500_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 1, v_buckets_x27_530_);
lean_ctor_set(v___x_525_, 0, v_size_x27_528_);
v___x_543_ = v___x_525_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_size_x27_528_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_buckets_x27_530_);
v___x_543_ = v_reuseFailAlloc_545_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; 
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_523_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
return v___x_544_;
}
}
}
}
else
{
lean_object* v___x_549_; 
lean_dec(v_b_504_);
lean_dec(v_a_503_);
lean_dec_ref(v_x_500_);
v___x_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_523_);
lean_ctor_set(v___x_549_, 1, v_m_502_);
return v___x_549_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x3f___redArg(lean_object* v_x_550_, lean_object* v_x_551_, lean_object* v_m_552_, lean_object* v_a_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_x_550_, v_x_551_, v_m_552_, v_a_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x3f___redArg___boxed(lean_object* v_x_555_, lean_object* v_x_556_, lean_object* v_m_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Std_ExtDHashMap_get_x3f___redArg(v_x_555_, v_x_556_, v_m_557_, v_a_558_);
lean_dec(v_m_557_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x3f(lean_object* v_00_u03b1_560_, lean_object* v_00_u03b2_561_, lean_object* v_x_562_, lean_object* v_x_563_, lean_object* v_inst_564_, lean_object* v_m_565_, lean_object* v_a_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_x_562_, v_x_563_, v_m_565_, v_a_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x3f___boxed(lean_object* v_00_u03b1_568_, lean_object* v_00_u03b2_569_, lean_object* v_x_570_, lean_object* v_x_571_, lean_object* v_inst_572_, lean_object* v_m_573_, lean_object* v_a_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Std_ExtDHashMap_get_x3f(v_00_u03b1_568_, v_00_u03b2_569_, v_x_570_, v_x_571_, v_inst_572_, v_m_573_, v_a_574_);
lean_dec(v_m_573_);
return v_res_575_;
}
}
uint8_t l_Std_ExtDHashMap_contains___redArg(lean_object* v_x_576_, lean_object* v_x_577_, lean_object* v_m_578_, lean_object* v_a_579_){
_start:
{
uint8_t v___x_580_; 
v___x_580_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_576_, v_x_577_, v_m_578_, v_a_579_);
return v___x_580_;
}
}
LEAN_EXPORT void l_Std_ExtDHashMap_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_576_ = stack[0].m_obj;
lean_object* v_x_577_ = stack[1].m_obj;
lean_object* v_m_578_ = stack[2].m_obj;
lean_object* v_a_579_ = stack[3].m_obj;
uint8_t v_res_581_;
v_res_581_ = l_Std_ExtDHashMap_contains___redArg(v_x_576_, v_x_577_, v_m_578_, v_a_579_);
stack->m_num = v_res_581_;
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_contains___redArg___boxed(lean_object* v_x_582_, lean_object* v_x_583_, lean_object* v_m_584_, lean_object* v_a_585_){
_start:
{
uint8_t v_res_586_; lean_object* v_r_587_; 
v_res_586_ = l_Std_ExtDHashMap_contains___redArg(v_x_582_, v_x_583_, v_m_584_, v_a_585_);
lean_dec(v_m_584_);
v_r_587_ = lean_box(v_res_586_);
return v_r_587_;
}
}
uint8_t l_Std_ExtDHashMap_contains(lean_object* v_00_u03b1_588_, lean_object* v_00_u03b2_589_, lean_object* v_x_590_, lean_object* v_x_591_, lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_m_594_, lean_object* v_a_595_){
_start:
{
uint8_t v___x_596_; 
v___x_596_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_590_, v_x_591_, v_m_594_, v_a_595_);
return v___x_596_;
}
}
LEAN_EXPORT void l_Std_ExtDHashMap_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_590_ = stack[2].m_obj;
lean_object* v_x_591_ = stack[3].m_obj;
lean_object* v_m_594_ = stack[6].m_obj;
lean_object* v_a_595_ = stack[7].m_obj;
uint8_t v_res_597_;
v_res_597_ = l_Std_ExtDHashMap_contains(lean_box(0), lean_box(0), v_x_590_, v_x_591_, lean_box(0), lean_box(0), v_m_594_, v_a_595_);
stack->m_num = v_res_597_;
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_contains___boxed(lean_object* v_00_u03b1_598_, lean_object* v_00_u03b2_599_, lean_object* v_x_600_, lean_object* v_x_601_, lean_object* v_inst_602_, lean_object* v_inst_603_, lean_object* v_m_604_, lean_object* v_a_605_){
_start:
{
uint8_t v_res_606_; lean_object* v_r_607_; 
v_res_606_ = l_Std_ExtDHashMap_contains(v_00_u03b1_598_, v_00_u03b2_599_, v_x_600_, v_x_601_, v_inst_602_, v_inst_603_, v_m_604_, v_a_605_);
lean_dec(v_m_604_);
v_r_607_ = lean_box(v_res_606_);
return v_r_607_;
}
}
lean_object* l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable___redArg(){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = lean_box(0);
return v___x_609_;
}
}
LEAN_EXPORT void l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_610_;
v_res_610_ = l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable___redArg();
stack->m_obj
 = v_res_610_;
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable___redArg___boxed(lean_object* v___dummy_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable___redArg();
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_613_, lean_object* v_00_u03b2_614_, lean_object* v_x_615_, lean_object* v_x_616_, lean_object* v_inst_617_, lean_object* v_inst_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = lean_box(0);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable___boxed(lean_object* v_00_u03b1_620_, lean_object* v_00_u03b2_621_, lean_object* v_x_622_, lean_object* v_x_623_, lean_object* v_inst_624_, lean_object* v_inst_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable(v_00_u03b1_620_, v_00_u03b2_621_, v_x_622_, v_x_623_, v_inst_624_, v_inst_625_);
lean_dec_ref(v_x_623_);
lean_dec_ref(v_x_622_);
return v_res_626_;
}
}
uint8_t l_Std_ExtDHashMap_instDecidableMem___redArg(lean_object* v_x_627_, lean_object* v_x_628_, lean_object* v_m_629_, lean_object* v_a_630_){
_start:
{
uint8_t v___x_631_; 
v___x_631_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_627_, v_x_628_, v_m_629_, v_a_630_);
return v___x_631_;
}
}
LEAN_EXPORT void l_Std_ExtDHashMap_instDecidableMem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_627_ = stack[0].m_obj;
lean_object* v_x_628_ = stack[1].m_obj;
lean_object* v_m_629_ = stack[2].m_obj;
lean_object* v_a_630_ = stack[3].m_obj;
uint8_t v_res_632_;
v_res_632_ = l_Std_ExtDHashMap_instDecidableMem___redArg(v_x_627_, v_x_628_, v_m_629_, v_a_630_);
stack->m_num = v_res_632_;
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instDecidableMem___redArg___boxed(lean_object* v_x_633_, lean_object* v_x_634_, lean_object* v_m_635_, lean_object* v_a_636_){
_start:
{
uint8_t v_res_637_; lean_object* v_r_638_; 
v_res_637_ = l_Std_ExtDHashMap_instDecidableMem___redArg(v_x_633_, v_x_634_, v_m_635_, v_a_636_);
lean_dec(v_m_635_);
v_r_638_ = lean_box(v_res_637_);
return v_r_638_;
}
}
uint8_t l_Std_ExtDHashMap_instDecidableMem(lean_object* v_00_u03b1_639_, lean_object* v_00_u03b2_640_, lean_object* v_x_641_, lean_object* v_x_642_, lean_object* v_inst_643_, lean_object* v_inst_644_, lean_object* v_m_645_, lean_object* v_a_646_){
_start:
{
uint8_t v___x_647_; 
v___x_647_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_641_, v_x_642_, v_m_645_, v_a_646_);
return v___x_647_;
}
}
LEAN_EXPORT void l_Std_ExtDHashMap_instDecidableMem_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_641_ = stack[2].m_obj;
lean_object* v_x_642_ = stack[3].m_obj;
lean_object* v_m_645_ = stack[6].m_obj;
lean_object* v_a_646_ = stack[7].m_obj;
uint8_t v_res_648_;
v_res_648_ = l_Std_ExtDHashMap_instDecidableMem(lean_box(0), lean_box(0), v_x_641_, v_x_642_, lean_box(0), lean_box(0), v_m_645_, v_a_646_);
stack->m_num = v_res_648_;
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instDecidableMem___boxed(lean_object* v_00_u03b1_649_, lean_object* v_00_u03b2_650_, lean_object* v_x_651_, lean_object* v_x_652_, lean_object* v_inst_653_, lean_object* v_inst_654_, lean_object* v_m_655_, lean_object* v_a_656_){
_start:
{
uint8_t v_res_657_; lean_object* v_r_658_; 
v_res_657_ = l_Std_ExtDHashMap_instDecidableMem(v_00_u03b1_649_, v_00_u03b2_650_, v_x_651_, v_x_652_, v_inst_653_, v_inst_654_, v_m_655_, v_a_656_);
lean_dec(v_m_655_);
v_r_658_ = lean_box(v_res_657_);
return v_r_658_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get___redArg(lean_object* v_x_659_, lean_object* v_x_660_, lean_object* v_m_661_, lean_object* v_a_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_x_659_, v_x_660_, v_m_661_, v_a_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get___redArg___boxed(lean_object* v_x_664_, lean_object* v_x_665_, lean_object* v_m_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Std_ExtDHashMap_get___redArg(v_x_664_, v_x_665_, v_m_666_, v_a_667_);
lean_dec(v_m_666_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get(lean_object* v_00_u03b1_669_, lean_object* v_00_u03b2_670_, lean_object* v_x_671_, lean_object* v_x_672_, lean_object* v_inst_673_, lean_object* v_m_674_, lean_object* v_a_675_, lean_object* v_h_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_x_671_, v_x_672_, v_m_674_, v_a_675_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get___boxed(lean_object* v_00_u03b1_678_, lean_object* v_00_u03b2_679_, lean_object* v_x_680_, lean_object* v_x_681_, lean_object* v_inst_682_, lean_object* v_m_683_, lean_object* v_a_684_, lean_object* v_h_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Std_ExtDHashMap_get(v_00_u03b1_678_, v_00_u03b2_679_, v_x_680_, v_x_681_, v_inst_682_, v_m_683_, v_a_684_, v_h_685_);
lean_dec(v_m_683_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x21___redArg(lean_object* v_x_687_, lean_object* v_x_688_, lean_object* v_m_689_, lean_object* v_a_690_, lean_object* v_inst_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(v_x_687_, v_x_688_, v_m_689_, v_a_690_, v_inst_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x21___redArg___boxed(lean_object* v_x_693_, lean_object* v_x_694_, lean_object* v_m_695_, lean_object* v_a_696_, lean_object* v_inst_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Std_ExtDHashMap_get_x21___redArg(v_x_693_, v_x_694_, v_m_695_, v_a_696_, v_inst_697_);
lean_dec(v_inst_697_);
lean_dec(v_m_695_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x21(lean_object* v_00_u03b1_699_, lean_object* v_00_u03b2_700_, lean_object* v_x_701_, lean_object* v_x_702_, lean_object* v_inst_703_, lean_object* v_m_704_, lean_object* v_a_705_, lean_object* v_inst_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(v_x_701_, v_x_702_, v_m_704_, v_a_705_, v_inst_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x21___boxed(lean_object* v_00_u03b1_708_, lean_object* v_00_u03b2_709_, lean_object* v_x_710_, lean_object* v_x_711_, lean_object* v_inst_712_, lean_object* v_m_713_, lean_object* v_a_714_, lean_object* v_inst_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Std_ExtDHashMap_get_x21(v_00_u03b1_708_, v_00_u03b2_709_, v_x_710_, v_x_711_, v_inst_712_, v_m_713_, v_a_714_, v_inst_715_);
lean_dec(v_inst_715_);
lean_dec(v_m_713_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getD___redArg(lean_object* v_x_717_, lean_object* v_x_718_, lean_object* v_m_719_, lean_object* v_a_720_, lean_object* v_fallback_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(v_x_717_, v_x_718_, v_m_719_, v_a_720_, v_fallback_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getD___redArg___boxed(lean_object* v_x_723_, lean_object* v_x_724_, lean_object* v_m_725_, lean_object* v_a_726_, lean_object* v_fallback_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Std_ExtDHashMap_getD___redArg(v_x_723_, v_x_724_, v_m_725_, v_a_726_, v_fallback_727_);
lean_dec(v_fallback_727_);
lean_dec(v_m_725_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getD(lean_object* v_00_u03b1_729_, lean_object* v_00_u03b2_730_, lean_object* v_x_731_, lean_object* v_x_732_, lean_object* v_inst_733_, lean_object* v_m_734_, lean_object* v_a_735_, lean_object* v_fallback_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(v_x_731_, v_x_732_, v_m_734_, v_a_735_, v_fallback_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getD___boxed(lean_object* v_00_u03b1_738_, lean_object* v_00_u03b2_739_, lean_object* v_x_740_, lean_object* v_x_741_, lean_object* v_inst_742_, lean_object* v_m_743_, lean_object* v_a_744_, lean_object* v_fallback_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Std_ExtDHashMap_getD(v_00_u03b1_738_, v_00_u03b2_739_, v_x_740_, v_x_741_, v_inst_742_, v_m_743_, v_a_744_, v_fallback_745_);
lean_dec(v_fallback_745_);
lean_dec(v_m_743_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_erase___redArg(lean_object* v_x_747_, lean_object* v_x_748_, lean_object* v_m_749_, lean_object* v_a_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_747_, v_x_748_, v_m_749_, v_a_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_erase(lean_object* v_00_u03b1_752_, lean_object* v_00_u03b2_753_, lean_object* v_x_754_, lean_object* v_x_755_, lean_object* v_inst_756_, lean_object* v_inst_757_, lean_object* v_m_758_, lean_object* v_a_759_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_754_, v_x_755_, v_m_758_, v_a_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x3f___redArg(lean_object* v_x_761_, lean_object* v_x_762_, lean_object* v_m_763_, lean_object* v_a_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_761_, v_x_762_, v_m_763_, v_a_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x3f___redArg___boxed(lean_object* v_x_766_, lean_object* v_x_767_, lean_object* v_m_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Std_ExtDHashMap_Const_get_x3f___redArg(v_x_766_, v_x_767_, v_m_768_, v_a_769_);
lean_dec(v_m_768_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x3f(lean_object* v_00_u03b1_771_, lean_object* v_x_772_, lean_object* v_x_773_, lean_object* v_00_u03b2_774_, lean_object* v_inst_775_, lean_object* v_inst_776_, lean_object* v_m_777_, lean_object* v_a_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_772_, v_x_773_, v_m_777_, v_a_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x3f___boxed(lean_object* v_00_u03b1_780_, lean_object* v_x_781_, lean_object* v_x_782_, lean_object* v_00_u03b2_783_, lean_object* v_inst_784_, lean_object* v_inst_785_, lean_object* v_m_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Std_ExtDHashMap_Const_get_x3f(v_00_u03b1_780_, v_x_781_, v_x_782_, v_00_u03b2_783_, v_inst_784_, v_inst_785_, v_m_786_, v_a_787_);
lean_dec(v_m_786_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get___redArg(lean_object* v_x_789_, lean_object* v_x_790_, lean_object* v_m_791_, lean_object* v_a_792_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_x_789_, v_x_790_, v_m_791_, v_a_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get___redArg___boxed(lean_object* v_x_794_, lean_object* v_x_795_, lean_object* v_m_796_, lean_object* v_a_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Std_ExtDHashMap_Const_get___redArg(v_x_794_, v_x_795_, v_m_796_, v_a_797_);
lean_dec(v_m_796_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get(lean_object* v_00_u03b1_799_, lean_object* v_x_800_, lean_object* v_x_801_, lean_object* v_00_u03b2_802_, lean_object* v_inst_803_, lean_object* v_inst_804_, lean_object* v_m_805_, lean_object* v_a_806_, lean_object* v_h_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_x_800_, v_x_801_, v_m_805_, v_a_806_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get___boxed(lean_object* v_00_u03b1_809_, lean_object* v_x_810_, lean_object* v_x_811_, lean_object* v_00_u03b2_812_, lean_object* v_inst_813_, lean_object* v_inst_814_, lean_object* v_m_815_, lean_object* v_a_816_, lean_object* v_h_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Std_ExtDHashMap_Const_get(v_00_u03b1_809_, v_x_810_, v_x_811_, v_00_u03b2_812_, v_inst_813_, v_inst_814_, v_m_815_, v_a_816_, v_h_817_);
lean_dec(v_m_815_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getD___redArg(lean_object* v_x_819_, lean_object* v_x_820_, lean_object* v_m_821_, lean_object* v_a_822_, lean_object* v_fallback_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_x_819_, v_x_820_, v_m_821_, v_a_822_, v_fallback_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getD___redArg___boxed(lean_object* v_x_825_, lean_object* v_x_826_, lean_object* v_m_827_, lean_object* v_a_828_, lean_object* v_fallback_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Std_ExtDHashMap_Const_getD___redArg(v_x_825_, v_x_826_, v_m_827_, v_a_828_, v_fallback_829_);
lean_dec(v_fallback_829_);
lean_dec(v_m_827_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getD(lean_object* v_00_u03b1_831_, lean_object* v_x_832_, lean_object* v_x_833_, lean_object* v_00_u03b2_834_, lean_object* v_inst_835_, lean_object* v_inst_836_, lean_object* v_m_837_, lean_object* v_a_838_, lean_object* v_fallback_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_x_832_, v_x_833_, v_m_837_, v_a_838_, v_fallback_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getD___boxed(lean_object* v_00_u03b1_841_, lean_object* v_x_842_, lean_object* v_x_843_, lean_object* v_00_u03b2_844_, lean_object* v_inst_845_, lean_object* v_inst_846_, lean_object* v_m_847_, lean_object* v_a_848_, lean_object* v_fallback_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Std_ExtDHashMap_Const_getD(v_00_u03b1_841_, v_x_842_, v_x_843_, v_00_u03b2_844_, v_inst_845_, v_inst_846_, v_m_847_, v_a_848_, v_fallback_849_);
lean_dec(v_fallback_849_);
lean_dec(v_m_847_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x21___redArg(lean_object* v_x_851_, lean_object* v_x_852_, lean_object* v_inst_853_, lean_object* v_m_854_, lean_object* v_a_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_x_851_, v_x_852_, v_inst_853_, v_m_854_, v_a_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x21___redArg___boxed(lean_object* v_x_857_, lean_object* v_x_858_, lean_object* v_inst_859_, lean_object* v_m_860_, lean_object* v_a_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Std_ExtDHashMap_Const_get_x21___redArg(v_x_857_, v_x_858_, v_inst_859_, v_m_860_, v_a_861_);
lean_dec(v_m_860_);
lean_dec(v_inst_859_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x21(lean_object* v_00_u03b1_863_, lean_object* v_x_864_, lean_object* v_x_865_, lean_object* v_00_u03b2_866_, lean_object* v_inst_867_, lean_object* v_inst_868_, lean_object* v_inst_869_, lean_object* v_m_870_, lean_object* v_a_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_x_864_, v_x_865_, v_inst_869_, v_m_870_, v_a_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x21___boxed(lean_object* v_00_u03b1_873_, lean_object* v_x_874_, lean_object* v_x_875_, lean_object* v_00_u03b2_876_, lean_object* v_inst_877_, lean_object* v_inst_878_, lean_object* v_inst_879_, lean_object* v_m_880_, lean_object* v_a_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Std_ExtDHashMap_Const_get_x21(v_00_u03b1_873_, v_x_874_, v_x_875_, v_00_u03b2_876_, v_inst_877_, v_inst_878_, v_inst_879_, v_m_880_, v_a_881_);
lean_dec(v_m_880_);
lean_dec(v_inst_879_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getThenInsertIfNew_x3f___redArg(lean_object* v_x_883_, lean_object* v_x_884_, lean_object* v_m_885_, lean_object* v_a_886_, lean_object* v_b_887_){
_start:
{
lean_object* v_size_888_; lean_object* v_buckets_889_; lean_object* v___x_890_; lean_object* v___x_891_; uint64_t v___x_892_; uint64_t v___x_893_; uint64_t v___x_894_; uint64_t v___x_895_; uint64_t v_fold_896_; uint64_t v___x_897_; uint64_t v___x_898_; uint64_t v___x_899_; size_t v___x_900_; size_t v___x_901_; size_t v___x_902_; size_t v___x_903_; size_t v___x_904_; lean_object* v_bkt_905_; lean_object* v___x_906_; 
v_size_888_ = lean_ctor_get(v_m_885_, 0);
v_buckets_889_ = lean_ctor_get(v_m_885_, 1);
v___x_890_ = lean_array_get_size(v_buckets_889_);
lean_inc_ref(v_x_884_);
lean_inc_n(v_a_886_, 2);
v___x_891_ = lean_apply_1(v_x_884_, v_a_886_);
v___x_892_ = 32ULL;
v___x_893_ = lean_unbox_uint64(v___x_891_);
v___x_894_ = lean_uint64_shift_right(v___x_893_, v___x_892_);
v___x_895_ = lean_unbox_uint64(v___x_891_);
lean_dec_ref(v___x_891_);
v_fold_896_ = lean_uint64_xor(v___x_895_, v___x_894_);
v___x_897_ = 16ULL;
v___x_898_ = lean_uint64_shift_right(v_fold_896_, v___x_897_);
v___x_899_ = lean_uint64_xor(v_fold_896_, v___x_898_);
v___x_900_ = lean_uint64_to_usize(v___x_899_);
v___x_901_ = lean_usize_of_nat(v___x_890_);
v___x_902_ = ((size_t)1ULL);
v___x_903_ = lean_usize_sub(v___x_901_, v___x_902_);
v___x_904_ = lean_usize_land(v___x_900_, v___x_903_);
v_bkt_905_ = lean_array_uget_borrowed(v_buckets_889_, v___x_904_);
lean_inc(v_bkt_905_);
v___x_906_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_x_883_, v_a_886_, v_bkt_905_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_929_; 
lean_inc_ref(v_buckets_889_);
lean_inc(v_size_888_);
v_isSharedCheck_929_ = !lean_is_exclusive(v_m_885_);
if (v_isSharedCheck_929_ == 0)
{
lean_object* v_unused_930_; lean_object* v_unused_931_; 
v_unused_930_ = lean_ctor_get(v_m_885_, 1);
lean_dec(v_unused_930_);
v_unused_931_ = lean_ctor_get(v_m_885_, 0);
lean_dec(v_unused_931_);
v___x_908_ = v_m_885_;
v_isShared_909_ = v_isSharedCheck_929_;
goto v_resetjp_907_;
}
else
{
lean_dec(v_m_885_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_929_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; lean_object* v_size_x27_911_; lean_object* v___x_912_; lean_object* v_buckets_x27_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v___x_910_ = lean_unsigned_to_nat(1u);
v_size_x27_911_ = lean_nat_add(v_size_888_, v___x_910_);
lean_dec(v_size_888_);
lean_inc(v_bkt_905_);
v___x_912_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_912_, 0, v_a_886_);
lean_ctor_set(v___x_912_, 1, v_b_887_);
lean_ctor_set(v___x_912_, 2, v_bkt_905_);
v_buckets_x27_913_ = lean_array_uset(v_buckets_889_, v___x_904_, v___x_912_);
v___x_914_ = lean_unsigned_to_nat(4u);
v___x_915_ = lean_nat_mul(v_size_x27_911_, v___x_914_);
v___x_916_ = lean_unsigned_to_nat(3u);
v___x_917_ = lean_nat_div(v___x_915_, v___x_916_);
lean_dec(v___x_915_);
v___x_918_ = lean_array_get_size(v_buckets_x27_913_);
v___x_919_ = lean_nat_dec_le(v___x_917_, v___x_918_);
lean_dec(v___x_917_);
if (v___x_919_ == 0)
{
lean_object* v_val_920_; lean_object* v___x_922_; 
v_val_920_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_884_, v_buckets_x27_913_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 1, v_val_920_);
lean_ctor_set(v___x_908_, 0, v_size_x27_911_);
v___x_922_ = v___x_908_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_size_x27_911_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_val_920_);
v___x_922_ = v_reuseFailAlloc_924_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_923_; 
v___x_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_906_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
return v___x_923_;
}
}
else
{
lean_object* v___x_926_; 
lean_dec_ref(v_x_884_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 1, v_buckets_x27_913_);
lean_ctor_set(v___x_908_, 0, v_size_x27_911_);
v___x_926_ = v___x_908_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_size_x27_911_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v_buckets_x27_913_);
v___x_926_ = v_reuseFailAlloc_928_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
lean_object* v___x_927_; 
v___x_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_906_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
return v___x_927_;
}
}
}
}
else
{
lean_object* v___x_932_; 
lean_dec(v_b_887_);
lean_dec(v_a_886_);
lean_dec_ref(v_x_884_);
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_906_);
lean_ctor_set(v___x_932_, 1, v_m_885_);
return v___x_932_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_933_, lean_object* v_x_934_, lean_object* v_x_935_, lean_object* v_00_u03b2_936_, lean_object* v_inst_937_, lean_object* v_inst_938_, lean_object* v_m_939_, lean_object* v_a_940_, lean_object* v_b_941_){
_start:
{
lean_object* v_size_942_; lean_object* v_buckets_943_; lean_object* v___x_944_; lean_object* v___x_945_; uint64_t v___x_946_; uint64_t v___x_947_; uint64_t v___x_948_; uint64_t v___x_949_; uint64_t v_fold_950_; uint64_t v___x_951_; uint64_t v___x_952_; uint64_t v___x_953_; size_t v___x_954_; size_t v___x_955_; size_t v___x_956_; size_t v___x_957_; size_t v___x_958_; lean_object* v_bkt_959_; lean_object* v___x_960_; 
v_size_942_ = lean_ctor_get(v_m_939_, 0);
v_buckets_943_ = lean_ctor_get(v_m_939_, 1);
v___x_944_ = lean_array_get_size(v_buckets_943_);
lean_inc_ref(v_x_935_);
lean_inc_n(v_a_940_, 2);
v___x_945_ = lean_apply_1(v_x_935_, v_a_940_);
v___x_946_ = 32ULL;
v___x_947_ = lean_unbox_uint64(v___x_945_);
v___x_948_ = lean_uint64_shift_right(v___x_947_, v___x_946_);
v___x_949_ = lean_unbox_uint64(v___x_945_);
lean_dec_ref(v___x_945_);
v_fold_950_ = lean_uint64_xor(v___x_949_, v___x_948_);
v___x_951_ = 16ULL;
v___x_952_ = lean_uint64_shift_right(v_fold_950_, v___x_951_);
v___x_953_ = lean_uint64_xor(v_fold_950_, v___x_952_);
v___x_954_ = lean_uint64_to_usize(v___x_953_);
v___x_955_ = lean_usize_of_nat(v___x_944_);
v___x_956_ = ((size_t)1ULL);
v___x_957_ = lean_usize_sub(v___x_955_, v___x_956_);
v___x_958_ = lean_usize_land(v___x_954_, v___x_957_);
v_bkt_959_ = lean_array_uget_borrowed(v_buckets_943_, v___x_958_);
lean_inc(v_bkt_959_);
v___x_960_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_x_934_, v_a_940_, v_bkt_959_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_983_; 
lean_inc_ref(v_buckets_943_);
lean_inc(v_size_942_);
v_isSharedCheck_983_ = !lean_is_exclusive(v_m_939_);
if (v_isSharedCheck_983_ == 0)
{
lean_object* v_unused_984_; lean_object* v_unused_985_; 
v_unused_984_ = lean_ctor_get(v_m_939_, 1);
lean_dec(v_unused_984_);
v_unused_985_ = lean_ctor_get(v_m_939_, 0);
lean_dec(v_unused_985_);
v___x_962_ = v_m_939_;
v_isShared_963_ = v_isSharedCheck_983_;
goto v_resetjp_961_;
}
else
{
lean_dec(v_m_939_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_983_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_964_; lean_object* v_size_x27_965_; lean_object* v___x_966_; lean_object* v_buckets_x27_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_964_ = lean_unsigned_to_nat(1u);
v_size_x27_965_ = lean_nat_add(v_size_942_, v___x_964_);
lean_dec(v_size_942_);
lean_inc(v_bkt_959_);
v___x_966_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_966_, 0, v_a_940_);
lean_ctor_set(v___x_966_, 1, v_b_941_);
lean_ctor_set(v___x_966_, 2, v_bkt_959_);
v_buckets_x27_967_ = lean_array_uset(v_buckets_943_, v___x_958_, v___x_966_);
v___x_968_ = lean_unsigned_to_nat(4u);
v___x_969_ = lean_nat_mul(v_size_x27_965_, v___x_968_);
v___x_970_ = lean_unsigned_to_nat(3u);
v___x_971_ = lean_nat_div(v___x_969_, v___x_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_array_get_size(v_buckets_x27_967_);
v___x_973_ = lean_nat_dec_le(v___x_971_, v___x_972_);
lean_dec(v___x_971_);
if (v___x_973_ == 0)
{
lean_object* v_val_974_; lean_object* v___x_976_; 
v_val_974_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_935_, v_buckets_x27_967_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 1, v_val_974_);
lean_ctor_set(v___x_962_, 0, v_size_x27_965_);
v___x_976_ = v___x_962_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_size_x27_965_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_val_974_);
v___x_976_ = v_reuseFailAlloc_978_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
lean_object* v___x_977_; 
v___x_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_960_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
return v___x_977_;
}
}
else
{
lean_object* v___x_980_; 
lean_dec_ref(v_x_935_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 1, v_buckets_x27_967_);
lean_ctor_set(v___x_962_, 0, v_size_x27_965_);
v___x_980_ = v___x_962_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_size_x27_965_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_buckets_x27_967_);
v___x_980_ = v_reuseFailAlloc_982_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_981_; 
v___x_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_960_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
return v___x_981_;
}
}
}
}
else
{
lean_object* v___x_986_; 
lean_dec(v_b_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_x_935_);
v___x_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_960_);
lean_ctor_set(v___x_986_, 1, v_m_939_);
return v___x_986_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x3f___redArg(lean_object* v_x_987_, lean_object* v_x_988_, lean_object* v_m_989_, lean_object* v_a_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_987_, v_x_988_, v_m_989_, v_a_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x3f___redArg___boxed(lean_object* v_x_992_, lean_object* v_x_993_, lean_object* v_m_994_, lean_object* v_a_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Std_ExtDHashMap_getKey_x3f___redArg(v_x_992_, v_x_993_, v_m_994_, v_a_995_);
lean_dec(v_m_994_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x3f(lean_object* v_00_u03b1_997_, lean_object* v_00_u03b2_998_, lean_object* v_x_999_, lean_object* v_x_1000_, lean_object* v_inst_1001_, lean_object* v_inst_1002_, lean_object* v_m_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_999_, v_x_1000_, v_m_1003_, v_a_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x3f___boxed(lean_object* v_00_u03b1_1006_, lean_object* v_00_u03b2_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_, lean_object* v_inst_1010_, lean_object* v_inst_1011_, lean_object* v_m_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Std_ExtDHashMap_getKey_x3f(v_00_u03b1_1006_, v_00_u03b2_1007_, v_x_1008_, v_x_1009_, v_inst_1010_, v_inst_1011_, v_m_1012_, v_a_1013_);
lean_dec(v_m_1012_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey___redArg(lean_object* v_x_1015_, lean_object* v_x_1016_, lean_object* v_m_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_x_1015_, v_x_1016_, v_m_1017_, v_a_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey___redArg___boxed(lean_object* v_x_1020_, lean_object* v_x_1021_, lean_object* v_m_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Std_ExtDHashMap_getKey___redArg(v_x_1020_, v_x_1021_, v_m_1022_, v_a_1023_);
lean_dec(v_m_1022_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey(lean_object* v_00_u03b1_1025_, lean_object* v_00_u03b2_1026_, lean_object* v_x_1027_, lean_object* v_x_1028_, lean_object* v_inst_1029_, lean_object* v_inst_1030_, lean_object* v_m_1031_, lean_object* v_a_1032_, lean_object* v_h_1033_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_x_1027_, v_x_1028_, v_m_1031_, v_a_1032_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey___boxed(lean_object* v_00_u03b1_1035_, lean_object* v_00_u03b2_1036_, lean_object* v_x_1037_, lean_object* v_x_1038_, lean_object* v_inst_1039_, lean_object* v_inst_1040_, lean_object* v_m_1041_, lean_object* v_a_1042_, lean_object* v_h_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Std_ExtDHashMap_getKey(v_00_u03b1_1035_, v_00_u03b2_1036_, v_x_1037_, v_x_1038_, v_inst_1039_, v_inst_1040_, v_m_1041_, v_a_1042_, v_h_1043_);
lean_dec(v_m_1041_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x21___redArg(lean_object* v_x_1045_, lean_object* v_x_1046_, lean_object* v_inst_1047_, lean_object* v_m_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_1045_, v_x_1046_, v_inst_1047_, v_m_1048_, v_a_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x21___redArg___boxed(lean_object* v_x_1051_, lean_object* v_x_1052_, lean_object* v_inst_1053_, lean_object* v_m_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Std_ExtDHashMap_getKey_x21___redArg(v_x_1051_, v_x_1052_, v_inst_1053_, v_m_1054_, v_a_1055_);
lean_dec(v_m_1054_);
lean_dec(v_inst_1053_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x21(lean_object* v_00_u03b1_1057_, lean_object* v_00_u03b2_1058_, lean_object* v_x_1059_, lean_object* v_x_1060_, lean_object* v_inst_1061_, lean_object* v_inst_1062_, lean_object* v_inst_1063_, lean_object* v_m_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_1059_, v_x_1060_, v_inst_1063_, v_m_1064_, v_a_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x21___boxed(lean_object* v_00_u03b1_1067_, lean_object* v_00_u03b2_1068_, lean_object* v_x_1069_, lean_object* v_x_1070_, lean_object* v_inst_1071_, lean_object* v_inst_1072_, lean_object* v_inst_1073_, lean_object* v_m_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Std_ExtDHashMap_getKey_x21(v_00_u03b1_1067_, v_00_u03b2_1068_, v_x_1069_, v_x_1070_, v_inst_1071_, v_inst_1072_, v_inst_1073_, v_m_1074_, v_a_1075_);
lean_dec(v_m_1074_);
lean_dec(v_inst_1073_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKeyD___redArg(lean_object* v_x_1077_, lean_object* v_x_1078_, lean_object* v_m_1079_, lean_object* v_a_1080_, lean_object* v_fallback_1081_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_1077_, v_x_1078_, v_m_1079_, v_a_1080_, v_fallback_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKeyD___redArg___boxed(lean_object* v_x_1083_, lean_object* v_x_1084_, lean_object* v_m_1085_, lean_object* v_a_1086_, lean_object* v_fallback_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Std_ExtDHashMap_getKeyD___redArg(v_x_1083_, v_x_1084_, v_m_1085_, v_a_1086_, v_fallback_1087_);
lean_dec(v_fallback_1087_);
lean_dec(v_m_1085_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKeyD(lean_object* v_00_u03b1_1089_, lean_object* v_00_u03b2_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_, lean_object* v_inst_1093_, lean_object* v_inst_1094_, lean_object* v_m_1095_, lean_object* v_a_1096_, lean_object* v_fallback_1097_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_1091_, v_x_1092_, v_m_1095_, v_a_1096_, v_fallback_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKeyD___boxed(lean_object* v_00_u03b1_1099_, lean_object* v_00_u03b2_1100_, lean_object* v_x_1101_, lean_object* v_x_1102_, lean_object* v_inst_1103_, lean_object* v_inst_1104_, lean_object* v_m_1105_, lean_object* v_a_1106_, lean_object* v_fallback_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Std_ExtDHashMap_getKeyD(v_00_u03b1_1099_, v_00_u03b2_1100_, v_x_1101_, v_x_1102_, v_inst_1103_, v_inst_1104_, v_m_1105_, v_a_1106_, v_fallback_1107_);
lean_dec(v_fallback_1107_);
lean_dec(v_m_1105_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_size___redArg(lean_object* v_m_1109_){
_start:
{
lean_object* v_size_1110_; 
v_size_1110_ = lean_ctor_get(v_m_1109_, 0);
lean_inc(v_size_1110_);
return v_size_1110_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_size___redArg___boxed(lean_object* v_m_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Std_ExtDHashMap_size___redArg(v_m_1111_);
lean_dec(v_m_1111_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_size(lean_object* v_00_u03b1_1113_, lean_object* v_00_u03b2_1114_, lean_object* v_x_1115_, lean_object* v_x_1116_, lean_object* v_inst_1117_, lean_object* v_inst_1118_, lean_object* v_m_1119_){
_start:
{
lean_object* v_size_1120_; 
v_size_1120_ = lean_ctor_get(v_m_1119_, 0);
lean_inc(v_size_1120_);
return v_size_1120_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_size___boxed(lean_object* v_00_u03b1_1121_, lean_object* v_00_u03b2_1122_, lean_object* v_x_1123_, lean_object* v_x_1124_, lean_object* v_inst_1125_, lean_object* v_inst_1126_, lean_object* v_m_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Std_ExtDHashMap_size(v_00_u03b1_1121_, v_00_u03b2_1122_, v_x_1123_, v_x_1124_, v_inst_1125_, v_inst_1126_, v_m_1127_);
lean_dec(v_m_1127_);
lean_dec_ref(v_x_1124_);
lean_dec_ref(v_x_1123_);
return v_res_1128_;
}
}
uint8_t l_Std_ExtDHashMap_isEmpty___redArg(lean_object* v_m_1129_){
_start:
{
lean_object* v_size_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v_size_1130_ = lean_ctor_get(v_m_1129_, 0);
v___x_1131_ = lean_unsigned_to_nat(0u);
v___x_1132_ = lean_nat_dec_eq(v_size_1130_, v___x_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT void l_Std_ExtDHashMap_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1129_ = stack[0].m_obj;
uint8_t v_res_1133_;
v_res_1133_ = l_Std_ExtDHashMap_isEmpty___redArg(v_m_1129_);
stack->m_num = v_res_1133_;
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_isEmpty___redArg___boxed(lean_object* v_m_1134_){
_start:
{
uint8_t v_res_1135_; lean_object* v_r_1136_; 
v_res_1135_ = l_Std_ExtDHashMap_isEmpty___redArg(v_m_1134_);
lean_dec(v_m_1134_);
v_r_1136_ = lean_box(v_res_1135_);
return v_r_1136_;
}
}
uint8_t l_Std_ExtDHashMap_isEmpty(lean_object* v_00_u03b1_1137_, lean_object* v_00_u03b2_1138_, lean_object* v_x_1139_, lean_object* v_x_1140_, lean_object* v_inst_1141_, lean_object* v_inst_1142_, lean_object* v_m_1143_){
_start:
{
lean_object* v_size_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; 
v_size_1144_ = lean_ctor_get(v_m_1143_, 0);
v___x_1145_ = lean_unsigned_to_nat(0u);
v___x_1146_ = lean_nat_dec_eq(v_size_1144_, v___x_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT void l_Std_ExtDHashMap_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1139_ = stack[2].m_obj;
lean_object* v_x_1140_ = stack[3].m_obj;
lean_object* v_m_1143_ = stack[6].m_obj;
uint8_t v_res_1147_;
v_res_1147_ = l_Std_ExtDHashMap_isEmpty(lean_box(0), lean_box(0), v_x_1139_, v_x_1140_, lean_box(0), lean_box(0), v_m_1143_);
stack->m_num = v_res_1147_;
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_isEmpty___boxed(lean_object* v_00_u03b1_1148_, lean_object* v_00_u03b2_1149_, lean_object* v_x_1150_, lean_object* v_x_1151_, lean_object* v_inst_1152_, lean_object* v_inst_1153_, lean_object* v_m_1154_){
_start:
{
uint8_t v_res_1155_; lean_object* v_r_1156_; 
v_res_1155_ = l_Std_ExtDHashMap_isEmpty(v_00_u03b1_1148_, v_00_u03b2_1149_, v_x_1150_, v_x_1151_, v_inst_1152_, v_inst_1153_, v_m_1154_);
lean_dec(v_m_1154_);
lean_dec_ref(v_x_1151_);
lean_dec_ref(v_x_1150_);
v_r_1156_ = lean_box(v_res_1155_);
return v_r_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filter___redArg(lean_object* v_f_1157_, lean_object* v_m_1158_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1157_, v_m_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filter(lean_object* v_00_u03b1_1160_, lean_object* v_00_u03b2_1161_, lean_object* v_x_1162_, lean_object* v_x_1163_, lean_object* v_inst_1164_, lean_object* v_inst_1165_, lean_object* v_f_1166_, lean_object* v_m_1167_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1166_, v_m_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filter___boxed(lean_object* v_00_u03b1_1169_, lean_object* v_00_u03b2_1170_, lean_object* v_x_1171_, lean_object* v_x_1172_, lean_object* v_inst_1173_, lean_object* v_inst_1174_, lean_object* v_f_1175_, lean_object* v_m_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Std_ExtDHashMap_filter(v_00_u03b1_1169_, v_00_u03b2_1170_, v_x_1171_, v_x_1172_, v_inst_1173_, v_inst_1174_, v_f_1175_, v_m_1176_);
lean_dec_ref(v_x_1172_);
lean_dec_ref(v_x_1171_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_map___redArg(lean_object* v_f_1178_, lean_object* v_m_1179_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1178_, v_m_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_map(lean_object* v_00_u03b1_1181_, lean_object* v_00_u03b2_1182_, lean_object* v_00_u03b3_1183_, lean_object* v_x_1184_, lean_object* v_x_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_, lean_object* v_f_1188_, lean_object* v_m_1189_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1188_, v_m_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_map___boxed(lean_object* v_00_u03b1_1191_, lean_object* v_00_u03b2_1192_, lean_object* v_00_u03b3_1193_, lean_object* v_x_1194_, lean_object* v_x_1195_, lean_object* v_inst_1196_, lean_object* v_inst_1197_, lean_object* v_f_1198_, lean_object* v_m_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Std_ExtDHashMap_map(v_00_u03b1_1191_, v_00_u03b2_1192_, v_00_u03b3_1193_, v_x_1194_, v_x_1195_, v_inst_1196_, v_inst_1197_, v_f_1198_, v_m_1199_);
lean_dec_ref(v_x_1195_);
lean_dec_ref(v_x_1194_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filterMap___redArg(lean_object* v_f_1201_, lean_object* v_m_1202_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1201_, v_m_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filterMap(lean_object* v_00_u03b1_1204_, lean_object* v_00_u03b2_1205_, lean_object* v_00_u03b3_1206_, lean_object* v_x_1207_, lean_object* v_x_1208_, lean_object* v_inst_1209_, lean_object* v_inst_1210_, lean_object* v_f_1211_, lean_object* v_m_1212_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1211_, v_m_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filterMap___boxed(lean_object* v_00_u03b1_1214_, lean_object* v_00_u03b2_1215_, lean_object* v_00_u03b3_1216_, lean_object* v_x_1217_, lean_object* v_x_1218_, lean_object* v_inst_1219_, lean_object* v_inst_1220_, lean_object* v_f_1221_, lean_object* v_m_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Std_ExtDHashMap_filterMap(v_00_u03b1_1214_, v_00_u03b2_1215_, v_00_u03b3_1216_, v_x_1217_, v_x_1218_, v_inst_1219_, v_inst_1220_, v_f_1221_, v_m_1222_);
lean_dec_ref(v_x_1218_);
lean_dec_ref(v_x_1217_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_modify___redArg(lean_object* v_x_1224_, lean_object* v_x_1225_, lean_object* v_m_1226_, lean_object* v_a_1227_, lean_object* v_f_1228_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(v_x_1224_, v_x_1225_, v_m_1226_, v_a_1227_, v_f_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_modify(lean_object* v_00_u03b1_1230_, lean_object* v_00_u03b2_1231_, lean_object* v_x_1232_, lean_object* v_x_1233_, lean_object* v_inst_1234_, lean_object* v_m_1235_, lean_object* v_a_1236_, lean_object* v_f_1237_){
_start:
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(v_x_1232_, v_x_1233_, v_m_1235_, v_a_1236_, v_f_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_modify___redArg(lean_object* v_x_1239_, lean_object* v_x_1240_, lean_object* v_m_1241_, lean_object* v_a_1242_, lean_object* v_f_1243_){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_x_1239_, v_x_1240_, v_m_1241_, v_a_1242_, v_f_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_modify(lean_object* v_00_u03b1_1245_, lean_object* v_x_1246_, lean_object* v_x_1247_, lean_object* v_inst_1248_, lean_object* v_inst_1249_, lean_object* v_00_u03b2_1250_, lean_object* v_m_1251_, lean_object* v_a_1252_, lean_object* v_f_1253_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_x_1246_, v_x_1247_, v_m_1251_, v_a_1252_, v_f_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_alter___redArg(lean_object* v_x_1255_, lean_object* v_x_1256_, lean_object* v_m_1257_, lean_object* v_a_1258_, lean_object* v_f_1259_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(v_x_1255_, v_x_1256_, v_m_1257_, v_a_1258_, v_f_1259_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_alter(lean_object* v_00_u03b1_1261_, lean_object* v_00_u03b2_1262_, lean_object* v_x_1263_, lean_object* v_x_1264_, lean_object* v_inst_1265_, lean_object* v_m_1266_, lean_object* v_a_1267_, lean_object* v_f_1268_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(v_x_1263_, v_x_1264_, v_m_1266_, v_a_1267_, v_f_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_alter___redArg(lean_object* v_x_1270_, lean_object* v_x_1271_, lean_object* v_m_1272_, lean_object* v_a_1273_, lean_object* v_f_1274_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_x_1270_, v_x_1271_, v_m_1272_, v_a_1273_, v_f_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_alter(lean_object* v_00_u03b1_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_, lean_object* v_inst_1279_, lean_object* v_inst_1280_, lean_object* v_00_u03b2_1281_, lean_object* v_m_1282_, lean_object* v_a_1283_, lean_object* v_f_1284_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_x_1277_, v_x_1278_, v_m_1282_, v_a_1283_, v_f_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insertMany___redArg___lam__0(lean_object* v_x_1286_, lean_object* v_x_1287_, lean_object* v_x_1288_, lean_object* v_____s_1289_){
_start:
{
lean_object* v_fst_1290_; lean_object* v_snd_1291_; lean_object* v_m_1292_; lean_object* v___x_1293_; 
v_fst_1290_ = lean_ctor_get(v_x_1288_, 0);
lean_inc(v_fst_1290_);
v_snd_1291_ = lean_ctor_get(v_x_1288_, 1);
lean_inc(v_snd_1291_);
lean_dec_ref(v_x_1288_);
v_m_1292_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1286_, v_x_1287_, v_____s_1289_, v_fst_1290_, v_snd_1291_);
v___x_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1293_, 0, v_m_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insertMany___redArg(lean_object* v_x_1294_, lean_object* v_x_1295_, lean_object* v_inst_1296_, lean_object* v_m_1297_, lean_object* v_l_1298_){
_start:
{
lean_object* v___f_1299_; lean_object* v___x_1300_; 
v___f_1299_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1299_, 0, v_x_1294_);
lean_closure_set(v___f_1299_, 1, v_x_1295_);
v___x_1300_ = lean_apply_4(v_inst_1296_, lean_box(0), v_l_1298_, v_m_1297_, v___f_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insertMany(lean_object* v_00_u03b1_1301_, lean_object* v_00_u03b2_1302_, lean_object* v_x_1303_, lean_object* v_x_1304_, lean_object* v_inst_1305_, lean_object* v_inst_1306_, lean_object* v_00_u03c1_1307_, lean_object* v_inst_1308_, lean_object* v_m_1309_, lean_object* v_l_1310_){
_start:
{
lean_object* v___f_1311_; lean_object* v___x_1312_; 
v___f_1311_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1311_, 0, v_x_1303_);
lean_closure_set(v___f_1311_, 1, v_x_1304_);
v___x_1312_ = lean_apply_4(v_inst_1308_, lean_box(0), v_l_1310_, v_m_1309_, v___f_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertMany___redArg___lam__0(lean_object* v_x_1313_, lean_object* v_x_1314_, lean_object* v_x_1315_, lean_object* v_____s_1316_){
_start:
{
lean_object* v_fst_1317_; lean_object* v_snd_1318_; lean_object* v_m_1319_; lean_object* v___x_1320_; 
v_fst_1317_ = lean_ctor_get(v_x_1315_, 0);
lean_inc(v_fst_1317_);
v_snd_1318_ = lean_ctor_get(v_x_1315_, 1);
lean_inc(v_snd_1318_);
lean_dec_ref(v_x_1315_);
v_m_1319_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1313_, v_x_1314_, v_____s_1316_, v_fst_1317_, v_snd_1318_);
v___x_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1320_, 0, v_m_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertMany___redArg(lean_object* v_x_1321_, lean_object* v_x_1322_, lean_object* v_inst_1323_, lean_object* v_m_1324_, lean_object* v_l_1325_){
_start:
{
lean_object* v___f_1326_; lean_object* v___x_1327_; 
v___f_1326_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_Const_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1326_, 0, v_x_1321_);
lean_closure_set(v___f_1326_, 1, v_x_1322_);
v___x_1327_ = lean_apply_4(v_inst_1323_, lean_box(0), v_l_1325_, v_m_1324_, v___f_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertMany(lean_object* v_00_u03b1_1328_, lean_object* v_x_1329_, lean_object* v_x_1330_, lean_object* v_inst_1331_, lean_object* v_inst_1332_, lean_object* v_00_u03b2_1333_, lean_object* v_00_u03c1_1334_, lean_object* v_inst_1335_, lean_object* v_m_1336_, lean_object* v_l_1337_){
_start:
{
lean_object* v___f_1338_; lean_object* v___x_1339_; 
v___f_1338_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_Const_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1338_, 0, v_x_1329_);
lean_closure_set(v___f_1338_, 1, v_x_1330_);
v___x_1339_ = lean_apply_4(v_inst_1335_, lean_box(0), v_l_1337_, v_m_1336_, v___f_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg___lam__0(lean_object* v_x_1340_, lean_object* v_x_1341_, lean_object* v_a_1342_, lean_object* v_____s_1343_){
_start:
{
lean_object* v___x_1344_; lean_object* v_m_1345_; lean_object* v___x_1346_; 
v___x_1344_ = lean_box(0);
v_m_1345_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_1340_, v_x_1341_, v_____s_1343_, v_a_1342_, v___x_1344_);
v___x_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1346_, 0, v_m_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg(lean_object* v_x_1347_, lean_object* v_x_1348_, lean_object* v_inst_1349_, lean_object* v_m_1350_, lean_object* v_l_1351_){
_start:
{
lean_object* v___f_1352_; lean_object* v___x_1353_; 
v___f_1352_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1352_, 0, v_x_1347_);
lean_closure_set(v___f_1352_, 1, v_x_1348_);
v___x_1353_ = lean_apply_4(v_inst_1349_, lean_box(0), v_l_1351_, v_m_1350_, v___f_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertManyIfNewUnit(lean_object* v_00_u03b1_1354_, lean_object* v_x_1355_, lean_object* v_x_1356_, lean_object* v_inst_1357_, lean_object* v_inst_1358_, lean_object* v_00_u03c1_1359_, lean_object* v_inst_1360_, lean_object* v_m_1361_, lean_object* v_l_1362_){
_start:
{
lean_object* v___f_1363_; lean_object* v___x_1364_; 
v___f_1363_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1363_, 0, v_x_1355_);
lean_closure_set(v___f_1363_, 1, v_x_1356_);
v___x_1364_ = lean_apply_4(v_inst_1360_, lean_box(0), v_l_1362_, v_m_1361_, v___f_1363_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_union___redArg___lam__0(lean_object* v_x_1365_, lean_object* v_x_1366_, lean_object* v_a_1367_, lean_object* v_b_1368_, lean_object* v_acc_1369_){
_start:
{
lean_object* v_r_1370_; lean_object* v___x_1371_; 
v_r_1370_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_1365_, v_x_1366_, v_acc_1369_, v_a_1367_, v_b_1368_);
v___x_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1371_, 0, v_r_1370_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_union___redArg___lam__1(lean_object* v___x_1372_, lean_object* v___f_1373_, lean_object* v_a_1374_, lean_object* v_x_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v___x_1377_; 
v___x_1377_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1372_, v___f_1373_, v_a_1374_, v___y_1376_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_union___redArg(lean_object* v_x_1399_, lean_object* v_x_1400_, lean_object* v_m_u2081_1401_, lean_object* v_m_u2082_1402_){
_start:
{
lean_object* v___x_1403_; lean_object* v_size_1404_; lean_object* v_buckets_1405_; lean_object* v_size_1406_; uint8_t v___x_1407_; 
v___x_1403_ = ((lean_object*)(l_Std_ExtDHashMap_union___redArg___closed__9));
v_size_1404_ = lean_ctor_get(v_m_u2081_1401_, 0);
v_buckets_1405_ = lean_ctor_get(v_m_u2081_1401_, 1);
v_size_1406_ = lean_ctor_get(v_m_u2082_1402_, 0);
v___x_1407_ = lean_nat_dec_le(v_size_1404_, v_size_1406_);
if (v___x_1407_ == 0)
{
lean_object* v___f_1408_; lean_object* v___x_1409_; 
v___f_1408_ = ((lean_object*)(l_Std_ExtDHashMap_union___redArg___closed__10));
v___x_1409_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1408_, v_x_1399_, v_x_1400_, v_m_u2081_1401_, v_m_u2082_1402_);
return v___x_1409_;
}
else
{
lean_object* v___f_1410_; lean_object* v___f_1411_; size_t v_sz_1412_; size_t v___x_1413_; lean_object* v___x_1414_; 
lean_inc_ref(v_buckets_1405_);
lean_dec(v_m_u2081_1401_);
v___f_1410_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1410_, 0, v_x_1399_);
lean_closure_set(v___f_1410_, 1, v_x_1400_);
v___f_1411_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1411_, 0, v___x_1403_);
lean_closure_set(v___f_1411_, 1, v___f_1410_);
v_sz_1412_ = lean_array_size(v_buckets_1405_);
v___x_1413_ = ((size_t)0ULL);
v___x_1414_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1403_, v_buckets_1405_, v___f_1411_, v_sz_1412_, v___x_1413_, v_m_u2082_1402_);
return v___x_1414_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_union(lean_object* v_00_u03b1_1415_, lean_object* v_00_u03b2_1416_, lean_object* v_x_1417_, lean_object* v_x_1418_, lean_object* v_inst_1419_, lean_object* v_inst_1420_, lean_object* v_m_u2081_1421_, lean_object* v_m_u2082_1422_){
_start:
{
lean_object* v___x_1423_; lean_object* v_size_1424_; lean_object* v_buckets_1425_; lean_object* v_size_1426_; uint8_t v___x_1427_; 
v___x_1423_ = ((lean_object*)(l_Std_ExtDHashMap_union___redArg___closed__9));
v_size_1424_ = lean_ctor_get(v_m_u2081_1421_, 0);
v_buckets_1425_ = lean_ctor_get(v_m_u2081_1421_, 1);
v_size_1426_ = lean_ctor_get(v_m_u2082_1422_, 0);
v___x_1427_ = lean_nat_dec_le(v_size_1424_, v_size_1426_);
if (v___x_1427_ == 0)
{
lean_object* v___f_1428_; lean_object* v___x_1429_; 
v___f_1428_ = ((lean_object*)(l_Std_ExtDHashMap_union___redArg___closed__10));
v___x_1429_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1428_, v_x_1417_, v_x_1418_, v_m_u2081_1421_, v_m_u2082_1422_);
return v___x_1429_;
}
else
{
lean_object* v___f_1430_; lean_object* v___f_1431_; size_t v_sz_1432_; size_t v___x_1433_; lean_object* v___x_1434_; 
lean_inc_ref(v_buckets_1425_);
lean_dec(v_m_u2081_1421_);
v___f_1430_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1430_, 0, v_x_1417_);
lean_closure_set(v___f_1430_, 1, v_x_1418_);
v___f_1431_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1431_, 0, v___x_1423_);
lean_closure_set(v___f_1431_, 1, v___f_1430_);
v_sz_1432_ = lean_array_size(v_buckets_1425_);
v___x_1433_ = ((size_t)0ULL);
v___x_1434_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1423_, v_buckets_1425_, v___f_1431_, v_sz_1432_, v___x_1433_, v_m_u2082_1422_);
return v___x_1434_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instUnionOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_1435_, lean_object* v_x_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_union), 8, 6);
lean_closure_set(v___x_1437_, 0, lean_box(0));
lean_closure_set(v___x_1437_, 1, lean_box(0));
lean_closure_set(v___x_1437_, 2, v_x_1435_);
lean_closure_set(v___x_1437_, 3, v_x_1436_);
lean_closure_set(v___x_1437_, 4, lean_box(0));
lean_closure_set(v___x_1437_, 5, lean_box(0));
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instUnionOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1438_, lean_object* v_00_u03b2_1439_, lean_object* v_x_1440_, lean_object* v_x_1441_, lean_object* v_inst_1442_, lean_object* v_inst_1443_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_union), 8, 6);
lean_closure_set(v___x_1444_, 0, lean_box(0));
lean_closure_set(v___x_1444_, 1, lean_box(0));
lean_closure_set(v___x_1444_, 2, v_x_1440_);
lean_closure_set(v___x_1444_, 3, v_x_1441_);
lean_closure_set(v___x_1444_, 4, lean_box(0));
lean_closure_set(v___x_1444_, 5, lean_box(0));
return v___x_1444_;
}
}
uint8_t l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0(lean_object* v_x_1445_, lean_object* v_x_1446_, lean_object* v_inst_1447_, lean_object* v_m_u2081_1448_, lean_object* v_m_u2082_1449_){
_start:
{
uint8_t v___x_1450_; 
v___x_1450_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_x_1445_, v_x_1446_, v_inst_1447_, v_m_u2081_1448_, v_m_u2082_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT void l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1445_ = stack[0].m_obj;
lean_object* v_x_1446_ = stack[1].m_obj;
lean_object* v_inst_1447_ = stack[2].m_obj;
lean_object* v_m_u2081_1448_ = stack[3].m_obj;
lean_object* v_m_u2082_1449_ = stack[4].m_obj;
uint8_t v_res_1451_;
v_res_1451_ = l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0(v_x_1445_, v_x_1446_, v_inst_1447_, v_m_u2081_1448_, v_m_u2082_1449_);
stack->m_num = v_res_1451_;
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0___boxed(lean_object* v_x_1452_, lean_object* v_x_1453_, lean_object* v_inst_1454_, lean_object* v_m_u2081_1455_, lean_object* v_m_u2082_1456_){
_start:
{
uint8_t v_res_1457_; lean_object* v_r_1458_; 
v_res_1457_ = l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0(v_x_1452_, v_x_1453_, v_inst_1454_, v_m_u2081_1455_, v_m_u2082_1456_);
v_r_1458_ = lean_box(v_res_1457_);
return v_r_1458_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg(lean_object* v_x_1459_, lean_object* v_x_1460_, lean_object* v_inst_1461_){
_start:
{
lean_object* v___f_1462_; 
v___f_1462_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1462_, 0, v_x_1459_);
lean_closure_set(v___f_1462_, 1, v_x_1460_);
lean_closure_set(v___f_1462_, 2, v_inst_1461_);
return v___f_1462_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instBEqOfLawfulBEq(lean_object* v_00_u03b1_1463_, lean_object* v_00_u03b2_1464_, lean_object* v_x_1465_, lean_object* v_x_1466_, lean_object* v_inst_1467_, lean_object* v_inst_1468_){
_start:
{
lean_object* v___f_1469_; 
v___f_1469_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1469_, 0, v_x_1465_);
lean_closure_set(v___f_1469_, 1, v_x_1466_);
lean_closure_set(v___f_1469_, 2, v_inst_1468_);
return v___f_1469_;
}
}
uint8_t l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___redArg(lean_object* v_inst_1470_, lean_object* v_inst_1471_, lean_object* v_inst_1472_, lean_object* v_x_1473_, lean_object* v_x_1474_){
_start:
{
uint8_t v___x_1475_; 
v___x_1475_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_inst_1470_, v_inst_1471_, v_inst_1472_, v_x_1473_, v_x_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT void l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1470_ = stack[0].m_obj;
lean_object* v_inst_1471_ = stack[1].m_obj;
lean_object* v_inst_1472_ = stack[2].m_obj;
lean_object* v_x_1473_ = stack[3].m_obj;
lean_object* v_x_1474_ = stack[4].m_obj;
uint8_t v_res_1476_;
v_res_1476_ = l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___redArg(v_inst_1470_, v_inst_1471_, v_inst_1472_, v_x_1473_, v_x_1474_);
stack->m_num = v_res_1476_;
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___redArg___boxed(lean_object* v_inst_1477_, lean_object* v_inst_1478_, lean_object* v_inst_1479_, lean_object* v_x_1480_, lean_object* v_x_1481_){
_start:
{
uint8_t v_res_1482_; lean_object* v_r_1483_; 
v_res_1482_ = l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___redArg(v_inst_1477_, v_inst_1478_, v_inst_1479_, v_x_1480_, v_x_1481_);
v_r_1483_ = lean_box(v_res_1482_);
return v_r_1483_;
}
}
uint8_t l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq(lean_object* v_00_u03b1_1484_, lean_object* v_00_u03b2_1485_, lean_object* v_inst_1486_, lean_object* v_inst_1487_, lean_object* v_inst_1488_, lean_object* v_inst_1489_, lean_object* v_inst_1490_, lean_object* v_x_1491_, lean_object* v_x_1492_){
_start:
{
uint8_t v___x_1493_; 
v___x_1493_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_inst_1486_, v_inst_1488_, v_inst_1489_, v_x_1491_, v_x_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT void l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1486_ = stack[2].m_obj;
lean_object* v_inst_1488_ = stack[4].m_obj;
lean_object* v_inst_1489_ = stack[5].m_obj;
lean_object* v_x_1491_ = stack[7].m_obj;
lean_object* v_x_1492_ = stack[8].m_obj;
uint8_t v_res_1494_;
v_res_1494_ = l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq(lean_box(0), lean_box(0), v_inst_1486_, lean_box(0), v_inst_1488_, v_inst_1489_, lean_box(0), v_x_1491_, v_x_1492_);
stack->m_num = v_res_1494_;
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___boxed(lean_object* v_00_u03b1_1495_, lean_object* v_00_u03b2_1496_, lean_object* v_inst_1497_, lean_object* v_inst_1498_, lean_object* v_inst_1499_, lean_object* v_inst_1500_, lean_object* v_inst_1501_, lean_object* v_x_1502_, lean_object* v_x_1503_){
_start:
{
uint8_t v_res_1504_; lean_object* v_r_1505_; 
v_res_1504_ = l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq(v_00_u03b1_1495_, v_00_u03b2_1496_, v_inst_1497_, v_inst_1498_, v_inst_1499_, v_inst_1500_, v_inst_1501_, v_x_1502_, v_x_1503_);
v_r_1505_ = lean_box(v_res_1504_);
return v_r_1505_;
}
}
uint8_t l_Std_ExtDHashMap_Const_beq___redArg(lean_object* v_x_1506_, lean_object* v_x_1507_, lean_object* v_inst_1508_, lean_object* v_m_u2081_1509_, lean_object* v_m_u2082_1510_){
_start:
{
uint8_t v___x_1511_; 
v___x_1511_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_x_1506_, v_x_1507_, v_inst_1508_, v_m_u2081_1509_, v_m_u2082_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT void l_Std_ExtDHashMap_Const_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1506_ = stack[0].m_obj;
lean_object* v_x_1507_ = stack[1].m_obj;
lean_object* v_inst_1508_ = stack[2].m_obj;
lean_object* v_m_u2081_1509_ = stack[3].m_obj;
lean_object* v_m_u2082_1510_ = stack[4].m_obj;
uint8_t v_res_1512_;
v_res_1512_ = l_Std_ExtDHashMap_Const_beq___redArg(v_x_1506_, v_x_1507_, v_inst_1508_, v_m_u2081_1509_, v_m_u2082_1510_);
stack->m_num = v_res_1512_;
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_beq___redArg___boxed(lean_object* v_x_1513_, lean_object* v_x_1514_, lean_object* v_inst_1515_, lean_object* v_m_u2081_1516_, lean_object* v_m_u2082_1517_){
_start:
{
uint8_t v_res_1518_; lean_object* v_r_1519_; 
v_res_1518_ = l_Std_ExtDHashMap_Const_beq___redArg(v_x_1513_, v_x_1514_, v_inst_1515_, v_m_u2081_1516_, v_m_u2082_1517_);
v_r_1519_ = lean_box(v_res_1518_);
return v_r_1519_;
}
}
uint8_t l_Std_ExtDHashMap_Const_beq(lean_object* v_00_u03b1_1520_, lean_object* v_x_1521_, lean_object* v_x_1522_, lean_object* v_00_u03b2_1523_, lean_object* v_inst_1524_, lean_object* v_inst_1525_, lean_object* v_inst_1526_, lean_object* v_m_u2081_1527_, lean_object* v_m_u2082_1528_){
_start:
{
uint8_t v___x_1529_; 
v___x_1529_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_x_1521_, v_x_1522_, v_inst_1526_, v_m_u2081_1527_, v_m_u2082_1528_);
return v___x_1529_;
}
}
LEAN_EXPORT void l_Std_ExtDHashMap_Const_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1521_ = stack[1].m_obj;
lean_object* v_x_1522_ = stack[2].m_obj;
lean_object* v_inst_1526_ = stack[6].m_obj;
lean_object* v_m_u2081_1527_ = stack[7].m_obj;
lean_object* v_m_u2082_1528_ = stack[8].m_obj;
uint8_t v_res_1530_;
v_res_1530_ = l_Std_ExtDHashMap_Const_beq(lean_box(0), v_x_1521_, v_x_1522_, lean_box(0), lean_box(0), lean_box(0), v_inst_1526_, v_m_u2081_1527_, v_m_u2082_1528_);
stack->m_num = v_res_1530_;
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_beq___boxed(lean_object* v_00_u03b1_1531_, lean_object* v_x_1532_, lean_object* v_x_1533_, lean_object* v_00_u03b2_1534_, lean_object* v_inst_1535_, lean_object* v_inst_1536_, lean_object* v_inst_1537_, lean_object* v_m_u2081_1538_, lean_object* v_m_u2082_1539_){
_start:
{
uint8_t v_res_1540_; lean_object* v_r_1541_; 
v_res_1540_ = l_Std_ExtDHashMap_Const_beq(v_00_u03b1_1531_, v_x_1532_, v_x_1533_, v_00_u03b2_1534_, v_inst_1535_, v_inst_1536_, v_inst_1537_, v_m_u2081_1538_, v_m_u2082_1539_);
v_r_1541_ = lean_box(v_res_1540_);
return v_r_1541_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_inter___redArg(lean_object* v_x_1542_, lean_object* v_x_1543_, lean_object* v_m_u2081_1544_, lean_object* v_m_u2082_1545_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_x_1542_, v_x_1543_, v_m_u2081_1544_, v_m_u2082_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_inter(lean_object* v_00_u03b1_1547_, lean_object* v_00_u03b2_1548_, lean_object* v_x_1549_, lean_object* v_x_1550_, lean_object* v_inst_1551_, lean_object* v_inst_1552_, lean_object* v_m_u2081_1553_, lean_object* v_m_u2082_1554_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_x_1549_, v_x_1550_, v_m_u2081_1553_, v_m_u2082_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInterOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_1556_, lean_object* v_x_1557_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_inter), 8, 6);
lean_closure_set(v___x_1558_, 0, lean_box(0));
lean_closure_set(v___x_1558_, 1, lean_box(0));
lean_closure_set(v___x_1558_, 2, v_x_1556_);
lean_closure_set(v___x_1558_, 3, v_x_1557_);
lean_closure_set(v___x_1558_, 4, lean_box(0));
lean_closure_set(v___x_1558_, 5, lean_box(0));
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInterOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1559_, lean_object* v_00_u03b2_1560_, lean_object* v_x_1561_, lean_object* v_x_1562_, lean_object* v_inst_1563_, lean_object* v_inst_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_inter), 8, 6);
lean_closure_set(v___x_1565_, 0, lean_box(0));
lean_closure_set(v___x_1565_, 1, lean_box(0));
lean_closure_set(v___x_1565_, 2, v_x_1561_);
lean_closure_set(v___x_1565_, 3, v_x_1562_);
lean_closure_set(v___x_1565_, 4, lean_box(0));
lean_closure_set(v___x_1565_, 5, lean_box(0));
return v___x_1565_;
}
}
uint8_t l_Std_ExtDHashMap_diff___redArg___lam__0(lean_object* v_x_1566_, lean_object* v_x_1567_, lean_object* v_m_u2082_1568_, uint8_t v___x_1569_, lean_object* v_k_1570_, lean_object* v_x_1571_){
_start:
{
uint8_t v___x_1572_; 
v___x_1572_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_1566_, v_x_1567_, v_m_u2082_1568_, v_k_1570_);
if (v___x_1572_ == 0)
{
return v___x_1569_;
}
else
{
uint8_t v___x_1573_; 
v___x_1573_ = 0;
return v___x_1573_;
}
}
}
LEAN_EXPORT void l_Std_ExtDHashMap_diff___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1566_ = stack[0].m_obj;
lean_object* v_x_1567_ = stack[1].m_obj;
lean_object* v_m_u2082_1568_ = stack[2].m_obj;
uint8_t v___x_1569_ = stack[3].m_num;
lean_object* v_k_1570_ = stack[4].m_obj;
lean_object* v_x_1571_ = stack[5].m_obj;
uint8_t v_res_1574_;
v_res_1574_ = l_Std_ExtDHashMap_diff___redArg___lam__0(v_x_1566_, v_x_1567_, v_m_u2082_1568_, v___x_1569_, v_k_1570_, v_x_1571_);
stack->m_num = v_res_1574_;
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_diff___redArg___lam__0___boxed(lean_object* v_x_1575_, lean_object* v_x_1576_, lean_object* v_m_u2082_1577_, lean_object* v___x_1578_, lean_object* v_k_1579_, lean_object* v_x_1580_){
_start:
{
uint8_t v___x_109__boxed_1581_; uint8_t v_res_1582_; lean_object* v_r_1583_; 
v___x_109__boxed_1581_ = lean_unbox(v___x_1578_);
v_res_1582_ = l_Std_ExtDHashMap_diff___redArg___lam__0(v_x_1575_, v_x_1576_, v_m_u2082_1577_, v___x_109__boxed_1581_, v_k_1579_, v_x_1580_);
lean_dec(v_x_1580_);
lean_dec(v_m_u2082_1577_);
v_r_1583_ = lean_box(v_res_1582_);
return v_r_1583_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_diff___redArg(lean_object* v_x_1584_, lean_object* v_x_1585_, lean_object* v_m_u2081_1586_, lean_object* v_m_u2082_1587_){
_start:
{
lean_object* v_size_1588_; lean_object* v_size_1589_; uint8_t v___x_1590_; 
v_size_1588_ = lean_ctor_get(v_m_u2081_1586_, 0);
v_size_1589_ = lean_ctor_get(v_m_u2082_1587_, 0);
v___x_1590_ = lean_nat_dec_le(v_size_1588_, v_size_1589_);
if (v___x_1590_ == 0)
{
lean_object* v___f_1591_; lean_object* v___x_1592_; 
v___f_1591_ = ((lean_object*)(l_Std_ExtDHashMap_union___redArg___closed__10));
v___x_1592_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1591_, v_x_1584_, v_x_1585_, v_m_u2081_1586_, v_m_u2082_1587_);
return v___x_1592_;
}
else
{
lean_object* v___x_1593_; lean_object* v___f_1594_; lean_object* v___x_1595_; 
v___x_1593_ = lean_box(v___x_1590_);
v___f_1594_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1594_, 0, v_x_1584_);
lean_closure_set(v___f_1594_, 1, v_x_1585_);
lean_closure_set(v___f_1594_, 2, v_m_u2082_1587_);
lean_closure_set(v___f_1594_, 3, v___x_1593_);
v___x_1595_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1594_, v_m_u2081_1586_);
return v___x_1595_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_diff(lean_object* v_00_u03b1_1596_, lean_object* v_00_u03b2_1597_, lean_object* v_x_1598_, lean_object* v_x_1599_, lean_object* v_inst_1600_, lean_object* v_inst_1601_, lean_object* v_m_u2081_1602_, lean_object* v_m_u2082_1603_){
_start:
{
lean_object* v_size_1604_; lean_object* v_size_1605_; uint8_t v___x_1606_; 
v_size_1604_ = lean_ctor_get(v_m_u2081_1602_, 0);
v_size_1605_ = lean_ctor_get(v_m_u2082_1603_, 0);
v___x_1606_ = lean_nat_dec_le(v_size_1604_, v_size_1605_);
if (v___x_1606_ == 0)
{
lean_object* v___f_1607_; lean_object* v___x_1608_; 
v___f_1607_ = ((lean_object*)(l_Std_ExtDHashMap_union___redArg___closed__10));
v___x_1608_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1607_, v_x_1598_, v_x_1599_, v_m_u2081_1602_, v_m_u2082_1603_);
return v___x_1608_;
}
else
{
lean_object* v___x_1609_; lean_object* v___f_1610_; lean_object* v___x_1611_; 
v___x_1609_ = lean_box(v___x_1606_);
v___f_1610_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1610_, 0, v_x_1598_);
lean_closure_set(v___f_1610_, 1, v_x_1599_);
lean_closure_set(v___f_1610_, 2, v_m_u2082_1603_);
lean_closure_set(v___f_1610_, 3, v___x_1609_);
v___x_1611_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1610_, v_m_u2081_1602_);
return v___x_1611_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instSDiffOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_1612_, lean_object* v_x_1613_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_diff), 8, 6);
lean_closure_set(v___x_1614_, 0, lean_box(0));
lean_closure_set(v___x_1614_, 1, lean_box(0));
lean_closure_set(v___x_1614_, 2, v_x_1612_);
lean_closure_set(v___x_1614_, 3, v_x_1613_);
lean_closure_set(v___x_1614_, 4, lean_box(0));
lean_closure_set(v___x_1614_, 5, lean_box(0));
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instSDiffOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1615_, lean_object* v_00_u03b2_1616_, lean_object* v_x_1617_, lean_object* v_x_1618_, lean_object* v_inst_1619_, lean_object* v_inst_1620_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_diff), 8, 6);
lean_closure_set(v___x_1621_, 0, lean_box(0));
lean_closure_set(v___x_1621_, 1, lean_box(0));
lean_closure_set(v___x_1621_, 2, v_x_1617_);
lean_closure_set(v___x_1621_, 3, v_x_1618_);
lean_closure_set(v___x_1621_, 4, lean_box(0));
lean_closure_set(v___x_1621_, 5, lean_box(0));
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_unitOfArray___redArg(lean_object* v_inst_1626_, lean_object* v_inst_1627_, lean_object* v_l_1628_){
_start:
{
lean_object* v___f_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___f_1629_ = ((lean_object*)(l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__1));
v___x_1630_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1);
v___x_1631_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1629_, v_inst_1626_, v_inst_1627_, v___x_1630_, v_l_1628_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_unitOfArray(lean_object* v_00_u03b1_1632_, lean_object* v_inst_1633_, lean_object* v_inst_1634_, lean_object* v_l_1635_){
_start:
{
lean_object* v___f_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___f_1636_ = ((lean_object*)(l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__1));
v___x_1637_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1);
v___x_1638_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1636_, v_inst_1633_, v_inst_1634_, v___x_1637_, v_l_1635_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_ofList___redArg(lean_object* v_inst_1643_, lean_object* v_inst_1644_, lean_object* v_l_1645_){
_start:
{
lean_object* v___f_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___f_1646_ = ((lean_object*)(l_Std_ExtDHashMap_ofList___redArg___closed__1));
v___x_1647_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1);
v___x_1648_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1646_, v_inst_1643_, v_inst_1644_, v___x_1647_, v_l_1645_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_ofList(lean_object* v_00_u03b1_1649_, lean_object* v_00_u03b2_1650_, lean_object* v_inst_1651_, lean_object* v_inst_1652_, lean_object* v_l_1653_){
_start:
{
lean_object* v___f_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___f_1654_ = ((lean_object*)(l_Std_ExtDHashMap_ofList___redArg___closed__1));
v___x_1655_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1);
v___x_1656_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1654_, v_inst_1651_, v_inst_1652_, v___x_1655_, v_l_1653_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_ofList___redArg(lean_object* v_inst_1657_, lean_object* v_inst_1658_, lean_object* v_l_1659_){
_start:
{
lean_object* v___f_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___f_1660_ = ((lean_object*)(l_Std_ExtDHashMap_ofList___redArg___closed__1));
v___x_1661_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1);
v___x_1662_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1660_, v_inst_1657_, v_inst_1658_, v___x_1661_, v_l_1659_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_ofList(lean_object* v_00_u03b1_1663_, lean_object* v_00_u03b2_1664_, lean_object* v_inst_1665_, lean_object* v_inst_1666_, lean_object* v_l_1667_){
_start:
{
lean_object* v___f_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___f_1668_ = ((lean_object*)(l_Std_ExtDHashMap_ofList___redArg___closed__1));
v___x_1669_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1);
v___x_1670_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1668_, v_inst_1665_, v_inst_1666_, v___x_1669_, v_l_1667_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_unitOfList___redArg(lean_object* v_inst_1671_, lean_object* v_inst_1672_, lean_object* v_l_1673_){
_start:
{
lean_object* v___f_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___f_1674_ = ((lean_object*)(l_Std_ExtDHashMap_ofList___redArg___closed__1));
v___x_1675_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1);
v___x_1676_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1674_, v_inst_1671_, v_inst_1672_, v___x_1675_, v_l_1673_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_unitOfList(lean_object* v_00_u03b1_1677_, lean_object* v_inst_1678_, lean_object* v_inst_1679_, lean_object* v_l_1680_){
_start:
{
lean_object* v___f_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___f_1681_ = ((lean_object*)(l_Std_ExtDHashMap_ofList___redArg___closed__1));
v___x_1682_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___redArg___closed__1);
v___x_1683_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1681_, v_inst_1678_, v_inst_1679_, v___x_1682_, v_l_1680_);
return v___x_1683_;
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
