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
static lean_once_cell_t l_Std_ExtDHashMap_instEmptyCollection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtDHashMap_instEmptyCollection___closed__0;
static lean_once_cell_t l_Std_ExtDHashMap_instEmptyCollection___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtDHashMap_instEmptyCollection___closed__1;
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instEmptyCollection(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Std_ExtDHashMap_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_113_ = lean_box(0);
v___x_114_ = lean_unsigned_to_nat(16u);
v___x_115_ = lean_mk_array(v___x_114_, v___x_113_);
return v___x_115_;
}
}
static lean_object* _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_116_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___closed__0, &l_Std_ExtDHashMap_instEmptyCollection___closed__0_once, _init_l_Std_ExtDHashMap_instEmptyCollection___closed__0);
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v___x_116_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instEmptyCollection(lean_object* v_00_u03b1_119_, lean_object* v_00_u03b2_120_, lean_object* v_inst_121_, lean_object* v_inst_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instEmptyCollection___boxed(lean_object* v_00_u03b1_124_, lean_object* v_00_u03b2_125_, lean_object* v_inst_126_, lean_object* v_inst_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Std_ExtDHashMap_instEmptyCollection(v_00_u03b1_124_, v_00_u03b2_125_, v_inst_126_, v_inst_127_);
lean_dec_ref(v_inst_127_);
lean_dec_ref(v_inst_126_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInhabited(lean_object* v_00_u03b1_129_, lean_object* v_00_u03b2_130_, lean_object* v_inst_131_, lean_object* v_inst_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInhabited___boxed(lean_object* v_00_u03b1_134_, lean_object* v_00_u03b2_135_, lean_object* v_inst_136_, lean_object* v_inst_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Std_ExtDHashMap_instInhabited(v_00_u03b1_134_, v_00_u03b2_135_, v_inst_136_, v_inst_137_);
lean_dec_ref(v_inst_137_);
lean_dec_ref(v_inst_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insert___redArg(lean_object* v_x_139_, lean_object* v_x_140_, lean_object* v_m_141_, lean_object* v_a_142_, lean_object* v_b_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_139_, v_x_140_, v_m_141_, v_a_142_, v_b_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insert(lean_object* v_00_u03b1_145_, lean_object* v_00_u03b2_146_, lean_object* v_x_147_, lean_object* v_x_148_, lean_object* v_inst_149_, lean_object* v_inst_150_, lean_object* v_m_151_, lean_object* v_a_152_, lean_object* v_b_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_147_, v_x_148_, v_m_151_, v_a_152_, v_b_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_155_, lean_object* v_x_156_, lean_object* v_x_157_){
_start:
{
lean_object* v_fst_158_; lean_object* v_snd_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_fst_158_ = lean_ctor_get(v_x_157_, 0);
lean_inc(v_fst_158_);
v_snd_159_ = lean_ctor_get(v_x_157_, 1);
lean_inc(v_snd_159_);
lean_dec_ref(v_x_157_);
v___x_160_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1);
v___x_161_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_155_, v_x_156_, v___x_160_, v_fst_158_, v_snd_159_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_162_, lean_object* v_x_163_){
_start:
{
lean_object* v___f_164_; 
v___f_164_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_164_, 0, v_x_162_);
lean_closure_set(v___f_164_, 1, v_x_163_);
return v___f_164_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_165_, lean_object* v_00_u03b2_166_, lean_object* v_x_167_, lean_object* v_x_168_, lean_object* v_inst_169_, lean_object* v_inst_170_){
_start:
{
lean_object* v___f_171_; 
v___f_171_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_instSingletonSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_171_, 0, v_x_167_);
lean_closure_set(v___f_171_, 1, v_x_168_);
return v___f_171_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_172_, lean_object* v_x_173_, lean_object* v_x_174_, lean_object* v_x_175_){
_start:
{
lean_object* v_fst_176_; lean_object* v_snd_177_; lean_object* v___x_178_; 
v_fst_176_ = lean_ctor_get(v_x_174_, 0);
lean_inc(v_fst_176_);
v_snd_177_ = lean_ctor_get(v_x_174_, 1);
lean_inc(v_snd_177_);
lean_dec_ref(v_x_174_);
v___x_178_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_172_, v_x_173_, v_x_175_, v_fst_176_, v_snd_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_179_, lean_object* v_x_180_){
_start:
{
lean_object* v___f_181_; 
v___f_181_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_181_, 0, v_x_179_);
lean_closure_set(v___f_181_, 1, v_x_180_);
return v___f_181_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_182_, lean_object* v_00_u03b2_183_, lean_object* v_x_184_, lean_object* v_x_185_, lean_object* v_inst_186_, lean_object* v_inst_187_){
_start:
{
lean_object* v___f_188_; 
v___f_188_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_instInsertSigmaOfEquivBEqOfLawfulHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_188_, 0, v_x_184_);
lean_closure_set(v___f_188_, 1, v_x_185_);
return v___f_188_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insertIfNew___redArg(lean_object* v_x_189_, lean_object* v_x_190_, lean_object* v_m_191_, lean_object* v_a_192_, lean_object* v_b_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_189_, v_x_190_, v_m_191_, v_a_192_, v_b_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insertIfNew(lean_object* v_00_u03b1_195_, lean_object* v_00_u03b2_196_, lean_object* v_x_197_, lean_object* v_x_198_, lean_object* v_inst_199_, lean_object* v_inst_200_, lean_object* v_m_201_, lean_object* v_a_202_, lean_object* v_b_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_197_, v_x_198_, v_m_201_, v_a_202_, v_b_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_containsThenInsert___redArg(lean_object* v_x_205_, lean_object* v_x_206_, lean_object* v_m_207_, lean_object* v_a_208_, lean_object* v_b_209_){
_start:
{
lean_object* v_size_210_; lean_object* v_buckets_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_262_; 
v_size_210_ = lean_ctor_get(v_m_207_, 0);
v_buckets_211_ = lean_ctor_get(v_m_207_, 1);
v_isSharedCheck_262_ = !lean_is_exclusive(v_m_207_);
if (v_isSharedCheck_262_ == 0)
{
v___x_213_ = v_m_207_;
v_isShared_214_ = v_isSharedCheck_262_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_buckets_211_);
lean_inc(v_size_210_);
lean_dec(v_m_207_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_262_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_215_; lean_object* v___x_216_; uint64_t v___x_217_; uint64_t v___x_218_; uint64_t v___x_219_; uint64_t v___x_220_; uint64_t v_fold_221_; uint64_t v___x_222_; uint64_t v___x_223_; uint64_t v___x_224_; size_t v___x_225_; size_t v___x_226_; size_t v___x_227_; size_t v___x_228_; size_t v___x_229_; lean_object* v_bkt_230_; uint8_t v___x_231_; 
v___x_215_ = lean_array_get_size(v_buckets_211_);
lean_inc_ref(v_x_206_);
lean_inc_n(v_a_208_, 2);
v___x_216_ = lean_apply_1(v_x_206_, v_a_208_);
v___x_217_ = 32ULL;
v___x_218_ = lean_unbox_uint64(v___x_216_);
v___x_219_ = lean_uint64_shift_right(v___x_218_, v___x_217_);
v___x_220_ = lean_unbox_uint64(v___x_216_);
lean_dec_ref(v___x_216_);
v_fold_221_ = lean_uint64_xor(v___x_220_, v___x_219_);
v___x_222_ = 16ULL;
v___x_223_ = lean_uint64_shift_right(v_fold_221_, v___x_222_);
v___x_224_ = lean_uint64_xor(v_fold_221_, v___x_223_);
v___x_225_ = lean_uint64_to_usize(v___x_224_);
v___x_226_ = lean_usize_of_nat(v___x_215_);
v___x_227_ = ((size_t)1ULL);
v___x_228_ = lean_usize_sub(v___x_226_, v___x_227_);
v___x_229_ = lean_usize_land(v___x_225_, v___x_228_);
v_bkt_230_ = lean_array_uget_borrowed(v_buckets_211_, v___x_229_);
lean_inc(v_bkt_230_);
lean_inc_ref(v_x_205_);
v___x_231_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_205_, v_a_208_, v_bkt_230_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v_size_x27_233_; lean_object* v___x_234_; lean_object* v_buckets_x27_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
lean_dec_ref(v_x_205_);
v___x_232_ = lean_unsigned_to_nat(1u);
v_size_x27_233_ = lean_nat_add(v_size_210_, v___x_232_);
lean_dec(v_size_210_);
lean_inc(v_bkt_230_);
v___x_234_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_234_, 0, v_a_208_);
lean_ctor_set(v___x_234_, 1, v_b_209_);
lean_ctor_set(v___x_234_, 2, v_bkt_230_);
v_buckets_x27_235_ = lean_array_uset(v_buckets_211_, v___x_229_, v___x_234_);
v___x_236_ = lean_unsigned_to_nat(4u);
v___x_237_ = lean_nat_mul(v_size_x27_233_, v___x_236_);
v___x_238_ = lean_unsigned_to_nat(3u);
v___x_239_ = lean_nat_div(v___x_237_, v___x_238_);
lean_dec(v___x_237_);
v___x_240_ = lean_array_get_size(v_buckets_x27_235_);
v___x_241_ = lean_nat_dec_le(v___x_239_, v___x_240_);
lean_dec(v___x_239_);
if (v___x_241_ == 0)
{
lean_object* v_val_242_; lean_object* v___x_244_; 
v_val_242_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_206_, v_buckets_x27_235_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 1, v_val_242_);
lean_ctor_set(v___x_213_, 0, v_size_x27_233_);
v___x_244_ = v___x_213_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_size_x27_233_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v_val_242_);
v___x_244_ = v_reuseFailAlloc_247_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_box(v___x_231_);
v___x_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v___x_244_);
return v___x_246_;
}
}
else
{
lean_object* v___x_249_; 
lean_dec_ref(v_x_206_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 1, v_buckets_x27_235_);
lean_ctor_set(v___x_213_, 0, v_size_x27_233_);
v___x_249_ = v___x_213_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_size_x27_233_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_buckets_x27_235_);
v___x_249_ = v_reuseFailAlloc_252_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = lean_box(v___x_231_);
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v___x_249_);
return v___x_251_;
}
}
}
else
{
lean_object* v___x_253_; lean_object* v_buckets_x27_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_258_; 
lean_inc(v_bkt_230_);
lean_dec_ref(v_x_206_);
v___x_253_ = lean_box(0);
v_buckets_x27_254_ = lean_array_uset(v_buckets_211_, v___x_229_, v___x_253_);
v___x_255_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_x_205_, v_a_208_, v_b_209_, v_bkt_230_);
v___x_256_ = lean_array_uset(v_buckets_x27_254_, v___x_229_, v___x_255_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 1, v___x_256_);
v___x_258_ = v___x_213_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_size_210_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v___x_256_);
v___x_258_ = v_reuseFailAlloc_261_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_box(v___x_231_);
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v___x_258_);
return v___x_260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_containsThenInsert(lean_object* v_00_u03b1_263_, lean_object* v_00_u03b2_264_, lean_object* v_x_265_, lean_object* v_x_266_, lean_object* v_inst_267_, lean_object* v_inst_268_, lean_object* v_m_269_, lean_object* v_a_270_, lean_object* v_b_271_){
_start:
{
lean_object* v_size_272_; lean_object* v_buckets_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_324_; 
v_size_272_ = lean_ctor_get(v_m_269_, 0);
v_buckets_273_ = lean_ctor_get(v_m_269_, 1);
v_isSharedCheck_324_ = !lean_is_exclusive(v_m_269_);
if (v_isSharedCheck_324_ == 0)
{
v___x_275_ = v_m_269_;
v_isShared_276_ = v_isSharedCheck_324_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_buckets_273_);
lean_inc(v_size_272_);
lean_dec(v_m_269_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_324_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; lean_object* v___x_278_; uint64_t v___x_279_; uint64_t v___x_280_; uint64_t v___x_281_; uint64_t v___x_282_; uint64_t v_fold_283_; uint64_t v___x_284_; uint64_t v___x_285_; uint64_t v___x_286_; size_t v___x_287_; size_t v___x_288_; size_t v___x_289_; size_t v___x_290_; size_t v___x_291_; lean_object* v_bkt_292_; uint8_t v___x_293_; 
v___x_277_ = lean_array_get_size(v_buckets_273_);
lean_inc_ref(v_x_266_);
lean_inc_n(v_a_270_, 2);
v___x_278_ = lean_apply_1(v_x_266_, v_a_270_);
v___x_279_ = 32ULL;
v___x_280_ = lean_unbox_uint64(v___x_278_);
v___x_281_ = lean_uint64_shift_right(v___x_280_, v___x_279_);
v___x_282_ = lean_unbox_uint64(v___x_278_);
lean_dec_ref(v___x_278_);
v_fold_283_ = lean_uint64_xor(v___x_282_, v___x_281_);
v___x_284_ = 16ULL;
v___x_285_ = lean_uint64_shift_right(v_fold_283_, v___x_284_);
v___x_286_ = lean_uint64_xor(v_fold_283_, v___x_285_);
v___x_287_ = lean_uint64_to_usize(v___x_286_);
v___x_288_ = lean_usize_of_nat(v___x_277_);
v___x_289_ = ((size_t)1ULL);
v___x_290_ = lean_usize_sub(v___x_288_, v___x_289_);
v___x_291_ = lean_usize_land(v___x_287_, v___x_290_);
v_bkt_292_ = lean_array_uget_borrowed(v_buckets_273_, v___x_291_);
lean_inc(v_bkt_292_);
lean_inc_ref(v_x_265_);
v___x_293_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_265_, v_a_270_, v_bkt_292_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; lean_object* v_size_x27_295_; lean_object* v___x_296_; lean_object* v_buckets_x27_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
lean_dec_ref(v_x_265_);
v___x_294_ = lean_unsigned_to_nat(1u);
v_size_x27_295_ = lean_nat_add(v_size_272_, v___x_294_);
lean_dec(v_size_272_);
lean_inc(v_bkt_292_);
v___x_296_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_296_, 0, v_a_270_);
lean_ctor_set(v___x_296_, 1, v_b_271_);
lean_ctor_set(v___x_296_, 2, v_bkt_292_);
v_buckets_x27_297_ = lean_array_uset(v_buckets_273_, v___x_291_, v___x_296_);
v___x_298_ = lean_unsigned_to_nat(4u);
v___x_299_ = lean_nat_mul(v_size_x27_295_, v___x_298_);
v___x_300_ = lean_unsigned_to_nat(3u);
v___x_301_ = lean_nat_div(v___x_299_, v___x_300_);
lean_dec(v___x_299_);
v___x_302_ = lean_array_get_size(v_buckets_x27_297_);
v___x_303_ = lean_nat_dec_le(v___x_301_, v___x_302_);
lean_dec(v___x_301_);
if (v___x_303_ == 0)
{
lean_object* v_val_304_; lean_object* v___x_306_; 
v_val_304_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_266_, v_buckets_x27_297_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 1, v_val_304_);
lean_ctor_set(v___x_275_, 0, v_size_x27_295_);
v___x_306_ = v___x_275_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_size_x27_295_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_val_304_);
v___x_306_ = v_reuseFailAlloc_309_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_box(v___x_293_);
v___x_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v___x_306_);
return v___x_308_;
}
}
else
{
lean_object* v___x_311_; 
lean_dec_ref(v_x_266_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 1, v_buckets_x27_297_);
lean_ctor_set(v___x_275_, 0, v_size_x27_295_);
v___x_311_ = v___x_275_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_size_x27_295_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v_buckets_x27_297_);
v___x_311_ = v_reuseFailAlloc_314_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_box(v___x_293_);
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v___x_311_);
return v___x_313_;
}
}
}
else
{
lean_object* v___x_315_; lean_object* v_buckets_x27_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_320_; 
lean_inc(v_bkt_292_);
lean_dec_ref(v_x_266_);
v___x_315_ = lean_box(0);
v_buckets_x27_316_ = lean_array_uset(v_buckets_273_, v___x_291_, v___x_315_);
v___x_317_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_x_265_, v_a_270_, v_b_271_, v_bkt_292_);
v___x_318_ = lean_array_uset(v_buckets_x27_316_, v___x_291_, v___x_317_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 1, v___x_318_);
v___x_320_ = v___x_275_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_size_272_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v___x_318_);
v___x_320_ = v_reuseFailAlloc_323_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_box(v___x_293_);
v___x_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v___x_320_);
return v___x_322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_containsThenInsertIfNew___redArg(lean_object* v_x_325_, lean_object* v_x_326_, lean_object* v_m_327_, lean_object* v_a_328_, lean_object* v_b_329_){
_start:
{
lean_object* v_size_330_; lean_object* v_buckets_331_; lean_object* v___x_332_; lean_object* v___x_333_; uint64_t v___x_334_; uint64_t v___x_335_; uint64_t v___x_336_; uint64_t v___x_337_; uint64_t v_fold_338_; uint64_t v___x_339_; uint64_t v___x_340_; uint64_t v___x_341_; size_t v___x_342_; size_t v___x_343_; size_t v___x_344_; size_t v___x_345_; size_t v___x_346_; lean_object* v_bkt_347_; uint8_t v___x_348_; 
v_size_330_ = lean_ctor_get(v_m_327_, 0);
v_buckets_331_ = lean_ctor_get(v_m_327_, 1);
v___x_332_ = lean_array_get_size(v_buckets_331_);
lean_inc_ref(v_x_326_);
lean_inc_n(v_a_328_, 2);
v___x_333_ = lean_apply_1(v_x_326_, v_a_328_);
v___x_334_ = 32ULL;
v___x_335_ = lean_unbox_uint64(v___x_333_);
v___x_336_ = lean_uint64_shift_right(v___x_335_, v___x_334_);
v___x_337_ = lean_unbox_uint64(v___x_333_);
lean_dec_ref(v___x_333_);
v_fold_338_ = lean_uint64_xor(v___x_337_, v___x_336_);
v___x_339_ = 16ULL;
v___x_340_ = lean_uint64_shift_right(v_fold_338_, v___x_339_);
v___x_341_ = lean_uint64_xor(v_fold_338_, v___x_340_);
v___x_342_ = lean_uint64_to_usize(v___x_341_);
v___x_343_ = lean_usize_of_nat(v___x_332_);
v___x_344_ = ((size_t)1ULL);
v___x_345_ = lean_usize_sub(v___x_343_, v___x_344_);
v___x_346_ = lean_usize_land(v___x_342_, v___x_345_);
v_bkt_347_ = lean_array_uget_borrowed(v_buckets_331_, v___x_346_);
lean_inc(v_bkt_347_);
v___x_348_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_325_, v_a_328_, v_bkt_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_373_; 
lean_inc_ref(v_buckets_331_);
lean_inc(v_size_330_);
v_isSharedCheck_373_ = !lean_is_exclusive(v_m_327_);
if (v_isSharedCheck_373_ == 0)
{
lean_object* v_unused_374_; lean_object* v_unused_375_; 
v_unused_374_ = lean_ctor_get(v_m_327_, 1);
lean_dec(v_unused_374_);
v_unused_375_ = lean_ctor_get(v_m_327_, 0);
lean_dec(v_unused_375_);
v___x_350_ = v_m_327_;
v_isShared_351_ = v_isSharedCheck_373_;
goto v_resetjp_349_;
}
else
{
lean_dec(v_m_327_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_373_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_352_; lean_object* v_size_x27_353_; lean_object* v___x_354_; lean_object* v_buckets_x27_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_352_ = lean_unsigned_to_nat(1u);
v_size_x27_353_ = lean_nat_add(v_size_330_, v___x_352_);
lean_dec(v_size_330_);
lean_inc(v_bkt_347_);
v___x_354_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_354_, 0, v_a_328_);
lean_ctor_set(v___x_354_, 1, v_b_329_);
lean_ctor_set(v___x_354_, 2, v_bkt_347_);
v_buckets_x27_355_ = lean_array_uset(v_buckets_331_, v___x_346_, v___x_354_);
v___x_356_ = lean_unsigned_to_nat(4u);
v___x_357_ = lean_nat_mul(v_size_x27_353_, v___x_356_);
v___x_358_ = lean_unsigned_to_nat(3u);
v___x_359_ = lean_nat_div(v___x_357_, v___x_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_array_get_size(v_buckets_x27_355_);
v___x_361_ = lean_nat_dec_le(v___x_359_, v___x_360_);
lean_dec(v___x_359_);
if (v___x_361_ == 0)
{
lean_object* v_val_362_; lean_object* v___x_364_; 
v_val_362_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_326_, v_buckets_x27_355_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 1, v_val_362_);
lean_ctor_set(v___x_350_, 0, v_size_x27_353_);
v___x_364_ = v___x_350_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_size_x27_353_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_val_362_);
v___x_364_ = v_reuseFailAlloc_367_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_box(v___x_348_);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
lean_ctor_set(v___x_366_, 1, v___x_364_);
return v___x_366_;
}
}
else
{
lean_object* v___x_369_; 
lean_dec_ref(v_x_326_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 1, v_buckets_x27_355_);
lean_ctor_set(v___x_350_, 0, v_size_x27_353_);
v___x_369_ = v___x_350_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_size_x27_353_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_buckets_x27_355_);
v___x_369_ = v_reuseFailAlloc_372_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = lean_box(v___x_348_);
v___x_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
lean_ctor_set(v___x_371_, 1, v___x_369_);
return v___x_371_;
}
}
}
}
else
{
lean_object* v___x_376_; lean_object* v___x_377_; 
lean_dec(v_b_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_x_326_);
v___x_376_ = lean_box(v___x_348_);
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
lean_ctor_set(v___x_377_, 1, v_m_327_);
return v___x_377_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_containsThenInsertIfNew(lean_object* v_00_u03b1_378_, lean_object* v_00_u03b2_379_, lean_object* v_x_380_, lean_object* v_x_381_, lean_object* v_inst_382_, lean_object* v_inst_383_, lean_object* v_m_384_, lean_object* v_a_385_, lean_object* v_b_386_){
_start:
{
lean_object* v_size_387_; lean_object* v_buckets_388_; lean_object* v___x_389_; lean_object* v___x_390_; uint64_t v___x_391_; uint64_t v___x_392_; uint64_t v___x_393_; uint64_t v___x_394_; uint64_t v_fold_395_; uint64_t v___x_396_; uint64_t v___x_397_; uint64_t v___x_398_; size_t v___x_399_; size_t v___x_400_; size_t v___x_401_; size_t v___x_402_; size_t v___x_403_; lean_object* v_bkt_404_; uint8_t v___x_405_; 
v_size_387_ = lean_ctor_get(v_m_384_, 0);
v_buckets_388_ = lean_ctor_get(v_m_384_, 1);
v___x_389_ = lean_array_get_size(v_buckets_388_);
lean_inc_ref(v_x_381_);
lean_inc_n(v_a_385_, 2);
v___x_390_ = lean_apply_1(v_x_381_, v_a_385_);
v___x_391_ = 32ULL;
v___x_392_ = lean_unbox_uint64(v___x_390_);
v___x_393_ = lean_uint64_shift_right(v___x_392_, v___x_391_);
v___x_394_ = lean_unbox_uint64(v___x_390_);
lean_dec_ref(v___x_390_);
v_fold_395_ = lean_uint64_xor(v___x_394_, v___x_393_);
v___x_396_ = 16ULL;
v___x_397_ = lean_uint64_shift_right(v_fold_395_, v___x_396_);
v___x_398_ = lean_uint64_xor(v_fold_395_, v___x_397_);
v___x_399_ = lean_uint64_to_usize(v___x_398_);
v___x_400_ = lean_usize_of_nat(v___x_389_);
v___x_401_ = ((size_t)1ULL);
v___x_402_ = lean_usize_sub(v___x_400_, v___x_401_);
v___x_403_ = lean_usize_land(v___x_399_, v___x_402_);
v_bkt_404_ = lean_array_uget_borrowed(v_buckets_388_, v___x_403_);
lean_inc(v_bkt_404_);
v___x_405_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_380_, v_a_385_, v_bkt_404_);
if (v___x_405_ == 0)
{
lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_430_; 
lean_inc_ref(v_buckets_388_);
lean_inc(v_size_387_);
v_isSharedCheck_430_ = !lean_is_exclusive(v_m_384_);
if (v_isSharedCheck_430_ == 0)
{
lean_object* v_unused_431_; lean_object* v_unused_432_; 
v_unused_431_ = lean_ctor_get(v_m_384_, 1);
lean_dec(v_unused_431_);
v_unused_432_ = lean_ctor_get(v_m_384_, 0);
lean_dec(v_unused_432_);
v___x_407_ = v_m_384_;
v_isShared_408_ = v_isSharedCheck_430_;
goto v_resetjp_406_;
}
else
{
lean_dec(v_m_384_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_430_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; lean_object* v_size_x27_410_; lean_object* v___x_411_; lean_object* v_buckets_x27_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_409_ = lean_unsigned_to_nat(1u);
v_size_x27_410_ = lean_nat_add(v_size_387_, v___x_409_);
lean_dec(v_size_387_);
lean_inc(v_bkt_404_);
v___x_411_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_411_, 0, v_a_385_);
lean_ctor_set(v___x_411_, 1, v_b_386_);
lean_ctor_set(v___x_411_, 2, v_bkt_404_);
v_buckets_x27_412_ = lean_array_uset(v_buckets_388_, v___x_403_, v___x_411_);
v___x_413_ = lean_unsigned_to_nat(4u);
v___x_414_ = lean_nat_mul(v_size_x27_410_, v___x_413_);
v___x_415_ = lean_unsigned_to_nat(3u);
v___x_416_ = lean_nat_div(v___x_414_, v___x_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_array_get_size(v_buckets_x27_412_);
v___x_418_ = lean_nat_dec_le(v___x_416_, v___x_417_);
lean_dec(v___x_416_);
if (v___x_418_ == 0)
{
lean_object* v_val_419_; lean_object* v___x_421_; 
v_val_419_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_381_, v_buckets_x27_412_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 1, v_val_419_);
lean_ctor_set(v___x_407_, 0, v_size_x27_410_);
v___x_421_ = v___x_407_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_size_x27_410_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_val_419_);
v___x_421_ = v_reuseFailAlloc_424_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_box(v___x_405_);
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v___x_421_);
return v___x_423_;
}
}
else
{
lean_object* v___x_426_; 
lean_dec_ref(v_x_381_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 1, v_buckets_x27_412_);
lean_ctor_set(v___x_407_, 0, v_size_x27_410_);
v___x_426_ = v___x_407_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_size_x27_410_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_buckets_x27_412_);
v___x_426_ = v_reuseFailAlloc_429_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_box(v___x_405_);
v___x_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v___x_426_);
return v___x_428_;
}
}
}
}
else
{
lean_object* v___x_433_; lean_object* v___x_434_; 
lean_dec(v_b_386_);
lean_dec(v_a_385_);
lean_dec_ref(v_x_381_);
v___x_433_ = lean_box(v___x_405_);
v___x_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
lean_ctor_set(v___x_434_, 1, v_m_384_);
return v___x_434_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getThenInsertIfNew_x3f___redArg(lean_object* v_x_435_, lean_object* v_x_436_, lean_object* v_m_437_, lean_object* v_a_438_, lean_object* v_b_439_){
_start:
{
lean_object* v_size_440_; lean_object* v_buckets_441_; lean_object* v___x_442_; lean_object* v___x_443_; uint64_t v___x_444_; uint64_t v___x_445_; uint64_t v___x_446_; uint64_t v___x_447_; uint64_t v_fold_448_; uint64_t v___x_449_; uint64_t v___x_450_; uint64_t v___x_451_; size_t v___x_452_; size_t v___x_453_; size_t v___x_454_; size_t v___x_455_; size_t v___x_456_; lean_object* v_bkt_457_; lean_object* v___x_458_; 
v_size_440_ = lean_ctor_get(v_m_437_, 0);
v_buckets_441_ = lean_ctor_get(v_m_437_, 1);
v___x_442_ = lean_array_get_size(v_buckets_441_);
lean_inc_ref(v_x_436_);
lean_inc_n(v_a_438_, 2);
v___x_443_ = lean_apply_1(v_x_436_, v_a_438_);
v___x_444_ = 32ULL;
v___x_445_ = lean_unbox_uint64(v___x_443_);
v___x_446_ = lean_uint64_shift_right(v___x_445_, v___x_444_);
v___x_447_ = lean_unbox_uint64(v___x_443_);
lean_dec_ref(v___x_443_);
v_fold_448_ = lean_uint64_xor(v___x_447_, v___x_446_);
v___x_449_ = 16ULL;
v___x_450_ = lean_uint64_shift_right(v_fold_448_, v___x_449_);
v___x_451_ = lean_uint64_xor(v_fold_448_, v___x_450_);
v___x_452_ = lean_uint64_to_usize(v___x_451_);
v___x_453_ = lean_usize_of_nat(v___x_442_);
v___x_454_ = ((size_t)1ULL);
v___x_455_ = lean_usize_sub(v___x_453_, v___x_454_);
v___x_456_ = lean_usize_land(v___x_452_, v___x_455_);
v_bkt_457_ = lean_array_uget_borrowed(v_buckets_441_, v___x_456_);
lean_inc(v_bkt_457_);
v___x_458_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(v_x_435_, v_a_438_, v_bkt_457_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_481_; 
lean_inc_ref(v_buckets_441_);
lean_inc(v_size_440_);
v_isSharedCheck_481_ = !lean_is_exclusive(v_m_437_);
if (v_isSharedCheck_481_ == 0)
{
lean_object* v_unused_482_; lean_object* v_unused_483_; 
v_unused_482_ = lean_ctor_get(v_m_437_, 1);
lean_dec(v_unused_482_);
v_unused_483_ = lean_ctor_get(v_m_437_, 0);
lean_dec(v_unused_483_);
v___x_460_ = v_m_437_;
v_isShared_461_ = v_isSharedCheck_481_;
goto v_resetjp_459_;
}
else
{
lean_dec(v_m_437_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_481_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; lean_object* v_size_x27_463_; lean_object* v___x_464_; lean_object* v_buckets_x27_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_462_ = lean_unsigned_to_nat(1u);
v_size_x27_463_ = lean_nat_add(v_size_440_, v___x_462_);
lean_dec(v_size_440_);
lean_inc(v_bkt_457_);
v___x_464_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_464_, 0, v_a_438_);
lean_ctor_set(v___x_464_, 1, v_b_439_);
lean_ctor_set(v___x_464_, 2, v_bkt_457_);
v_buckets_x27_465_ = lean_array_uset(v_buckets_441_, v___x_456_, v___x_464_);
v___x_466_ = lean_unsigned_to_nat(4u);
v___x_467_ = lean_nat_mul(v_size_x27_463_, v___x_466_);
v___x_468_ = lean_unsigned_to_nat(3u);
v___x_469_ = lean_nat_div(v___x_467_, v___x_468_);
lean_dec(v___x_467_);
v___x_470_ = lean_array_get_size(v_buckets_x27_465_);
v___x_471_ = lean_nat_dec_le(v___x_469_, v___x_470_);
lean_dec(v___x_469_);
if (v___x_471_ == 0)
{
lean_object* v_val_472_; lean_object* v___x_474_; 
v_val_472_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_436_, v_buckets_x27_465_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 1, v_val_472_);
lean_ctor_set(v___x_460_, 0, v_size_x27_463_);
v___x_474_ = v___x_460_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_size_x27_463_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v_val_472_);
v___x_474_ = v_reuseFailAlloc_476_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
lean_object* v___x_475_; 
v___x_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_458_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
return v___x_475_;
}
}
else
{
lean_object* v___x_478_; 
lean_dec_ref(v_x_436_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 1, v_buckets_x27_465_);
lean_ctor_set(v___x_460_, 0, v_size_x27_463_);
v___x_478_ = v___x_460_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_size_x27_463_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_buckets_x27_465_);
v___x_478_ = v_reuseFailAlloc_480_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v___x_479_; 
v___x_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_458_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
return v___x_479_;
}
}
}
}
else
{
lean_object* v___x_484_; 
lean_dec(v_b_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_x_436_);
v___x_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_458_);
lean_ctor_set(v___x_484_, 1, v_m_437_);
return v___x_484_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_485_, lean_object* v_00_u03b2_486_, lean_object* v_x_487_, lean_object* v_x_488_, lean_object* v_inst_489_, lean_object* v_m_490_, lean_object* v_a_491_, lean_object* v_b_492_){
_start:
{
lean_object* v_size_493_; lean_object* v_buckets_494_; lean_object* v___x_495_; lean_object* v___x_496_; uint64_t v___x_497_; uint64_t v___x_498_; uint64_t v___x_499_; uint64_t v___x_500_; uint64_t v_fold_501_; uint64_t v___x_502_; uint64_t v___x_503_; uint64_t v___x_504_; size_t v___x_505_; size_t v___x_506_; size_t v___x_507_; size_t v___x_508_; size_t v___x_509_; lean_object* v_bkt_510_; lean_object* v___x_511_; 
v_size_493_ = lean_ctor_get(v_m_490_, 0);
v_buckets_494_ = lean_ctor_get(v_m_490_, 1);
v___x_495_ = lean_array_get_size(v_buckets_494_);
lean_inc_ref(v_x_488_);
lean_inc_n(v_a_491_, 2);
v___x_496_ = lean_apply_1(v_x_488_, v_a_491_);
v___x_497_ = 32ULL;
v___x_498_ = lean_unbox_uint64(v___x_496_);
v___x_499_ = lean_uint64_shift_right(v___x_498_, v___x_497_);
v___x_500_ = lean_unbox_uint64(v___x_496_);
lean_dec_ref(v___x_496_);
v_fold_501_ = lean_uint64_xor(v___x_500_, v___x_499_);
v___x_502_ = 16ULL;
v___x_503_ = lean_uint64_shift_right(v_fold_501_, v___x_502_);
v___x_504_ = lean_uint64_xor(v_fold_501_, v___x_503_);
v___x_505_ = lean_uint64_to_usize(v___x_504_);
v___x_506_ = lean_usize_of_nat(v___x_495_);
v___x_507_ = ((size_t)1ULL);
v___x_508_ = lean_usize_sub(v___x_506_, v___x_507_);
v___x_509_ = lean_usize_land(v___x_505_, v___x_508_);
v_bkt_510_ = lean_array_uget_borrowed(v_buckets_494_, v___x_509_);
lean_inc(v_bkt_510_);
v___x_511_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(v_x_487_, v_a_491_, v_bkt_510_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_534_; 
lean_inc_ref(v_buckets_494_);
lean_inc(v_size_493_);
v_isSharedCheck_534_ = !lean_is_exclusive(v_m_490_);
if (v_isSharedCheck_534_ == 0)
{
lean_object* v_unused_535_; lean_object* v_unused_536_; 
v_unused_535_ = lean_ctor_get(v_m_490_, 1);
lean_dec(v_unused_535_);
v_unused_536_ = lean_ctor_get(v_m_490_, 0);
lean_dec(v_unused_536_);
v___x_513_ = v_m_490_;
v_isShared_514_ = v_isSharedCheck_534_;
goto v_resetjp_512_;
}
else
{
lean_dec(v_m_490_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_534_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_515_; lean_object* v_size_x27_516_; lean_object* v___x_517_; lean_object* v_buckets_x27_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_515_ = lean_unsigned_to_nat(1u);
v_size_x27_516_ = lean_nat_add(v_size_493_, v___x_515_);
lean_dec(v_size_493_);
lean_inc(v_bkt_510_);
v___x_517_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_517_, 0, v_a_491_);
lean_ctor_set(v___x_517_, 1, v_b_492_);
lean_ctor_set(v___x_517_, 2, v_bkt_510_);
v_buckets_x27_518_ = lean_array_uset(v_buckets_494_, v___x_509_, v___x_517_);
v___x_519_ = lean_unsigned_to_nat(4u);
v___x_520_ = lean_nat_mul(v_size_x27_516_, v___x_519_);
v___x_521_ = lean_unsigned_to_nat(3u);
v___x_522_ = lean_nat_div(v___x_520_, v___x_521_);
lean_dec(v___x_520_);
v___x_523_ = lean_array_get_size(v_buckets_x27_518_);
v___x_524_ = lean_nat_dec_le(v___x_522_, v___x_523_);
lean_dec(v___x_522_);
if (v___x_524_ == 0)
{
lean_object* v_val_525_; lean_object* v___x_527_; 
v_val_525_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_488_, v_buckets_x27_518_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 1, v_val_525_);
lean_ctor_set(v___x_513_, 0, v_size_x27_516_);
v___x_527_ = v___x_513_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_size_x27_516_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_val_525_);
v___x_527_ = v_reuseFailAlloc_529_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_528_; 
v___x_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_511_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
return v___x_528_;
}
}
else
{
lean_object* v___x_531_; 
lean_dec_ref(v_x_488_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 1, v_buckets_x27_518_);
lean_ctor_set(v___x_513_, 0, v_size_x27_516_);
v___x_531_ = v___x_513_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_size_x27_516_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_buckets_x27_518_);
v___x_531_ = v_reuseFailAlloc_533_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_532_; 
v___x_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_511_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
return v___x_532_;
}
}
}
}
else
{
lean_object* v___x_537_; 
lean_dec(v_b_492_);
lean_dec(v_a_491_);
lean_dec_ref(v_x_488_);
v___x_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_511_);
lean_ctor_set(v___x_537_, 1, v_m_490_);
return v___x_537_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x3f___redArg(lean_object* v_x_538_, lean_object* v_x_539_, lean_object* v_m_540_, lean_object* v_a_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_x_538_, v_x_539_, v_m_540_, v_a_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x3f___redArg___boxed(lean_object* v_x_543_, lean_object* v_x_544_, lean_object* v_m_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Std_ExtDHashMap_get_x3f___redArg(v_x_543_, v_x_544_, v_m_545_, v_a_546_);
lean_dec(v_m_545_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x3f(lean_object* v_00_u03b1_548_, lean_object* v_00_u03b2_549_, lean_object* v_x_550_, lean_object* v_x_551_, lean_object* v_inst_552_, lean_object* v_m_553_, lean_object* v_a_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_x_550_, v_x_551_, v_m_553_, v_a_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x3f___boxed(lean_object* v_00_u03b1_556_, lean_object* v_00_u03b2_557_, lean_object* v_x_558_, lean_object* v_x_559_, lean_object* v_inst_560_, lean_object* v_m_561_, lean_object* v_a_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Std_ExtDHashMap_get_x3f(v_00_u03b1_556_, v_00_u03b2_557_, v_x_558_, v_x_559_, v_inst_560_, v_m_561_, v_a_562_);
lean_dec(v_m_561_);
return v_res_563_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_contains___redArg(lean_object* v_x_564_, lean_object* v_x_565_, lean_object* v_m_566_, lean_object* v_a_567_){
_start:
{
uint8_t v___x_568_; 
v___x_568_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_564_, v_x_565_, v_m_566_, v_a_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_contains___redArg___boxed(lean_object* v_x_569_, lean_object* v_x_570_, lean_object* v_m_571_, lean_object* v_a_572_){
_start:
{
uint8_t v_res_573_; lean_object* v_r_574_; 
v_res_573_ = l_Std_ExtDHashMap_contains___redArg(v_x_569_, v_x_570_, v_m_571_, v_a_572_);
lean_dec(v_m_571_);
v_r_574_ = lean_box(v_res_573_);
return v_r_574_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_contains(lean_object* v_00_u03b1_575_, lean_object* v_00_u03b2_576_, lean_object* v_x_577_, lean_object* v_x_578_, lean_object* v_inst_579_, lean_object* v_inst_580_, lean_object* v_m_581_, lean_object* v_a_582_){
_start:
{
uint8_t v___x_583_; 
v___x_583_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_577_, v_x_578_, v_m_581_, v_a_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_contains___boxed(lean_object* v_00_u03b1_584_, lean_object* v_00_u03b2_585_, lean_object* v_x_586_, lean_object* v_x_587_, lean_object* v_inst_588_, lean_object* v_inst_589_, lean_object* v_m_590_, lean_object* v_a_591_){
_start:
{
uint8_t v_res_592_; lean_object* v_r_593_; 
v_res_592_ = l_Std_ExtDHashMap_contains(v_00_u03b1_584_, v_00_u03b2_585_, v_x_586_, v_x_587_, v_inst_588_, v_inst_589_, v_m_590_, v_a_591_);
lean_dec(v_m_590_);
v_r_593_ = lean_box(v_res_592_);
return v_r_593_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_594_, lean_object* v_00_u03b2_595_, lean_object* v_x_596_, lean_object* v_x_597_, lean_object* v_inst_598_, lean_object* v_inst_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = lean_box(0);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable___boxed(lean_object* v_00_u03b1_601_, lean_object* v_00_u03b2_602_, lean_object* v_x_603_, lean_object* v_x_604_, lean_object* v_inst_605_, lean_object* v_inst_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Std_ExtDHashMap_instMembershipOfEquivBEqOfLawfulHashable(v_00_u03b1_601_, v_00_u03b2_602_, v_x_603_, v_x_604_, v_inst_605_, v_inst_606_);
lean_dec_ref(v_x_604_);
lean_dec_ref(v_x_603_);
return v_res_607_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_instDecidableMem___redArg(lean_object* v_x_608_, lean_object* v_x_609_, lean_object* v_m_610_, lean_object* v_a_611_){
_start:
{
uint8_t v___x_612_; 
v___x_612_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_608_, v_x_609_, v_m_610_, v_a_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instDecidableMem___redArg___boxed(lean_object* v_x_613_, lean_object* v_x_614_, lean_object* v_m_615_, lean_object* v_a_616_){
_start:
{
uint8_t v_res_617_; lean_object* v_r_618_; 
v_res_617_ = l_Std_ExtDHashMap_instDecidableMem___redArg(v_x_613_, v_x_614_, v_m_615_, v_a_616_);
lean_dec(v_m_615_);
v_r_618_ = lean_box(v_res_617_);
return v_r_618_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_instDecidableMem(lean_object* v_00_u03b1_619_, lean_object* v_00_u03b2_620_, lean_object* v_x_621_, lean_object* v_x_622_, lean_object* v_inst_623_, lean_object* v_inst_624_, lean_object* v_m_625_, lean_object* v_a_626_){
_start:
{
uint8_t v___x_627_; 
v___x_627_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_621_, v_x_622_, v_m_625_, v_a_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instDecidableMem___boxed(lean_object* v_00_u03b1_628_, lean_object* v_00_u03b2_629_, lean_object* v_x_630_, lean_object* v_x_631_, lean_object* v_inst_632_, lean_object* v_inst_633_, lean_object* v_m_634_, lean_object* v_a_635_){
_start:
{
uint8_t v_res_636_; lean_object* v_r_637_; 
v_res_636_ = l_Std_ExtDHashMap_instDecidableMem(v_00_u03b1_628_, v_00_u03b2_629_, v_x_630_, v_x_631_, v_inst_632_, v_inst_633_, v_m_634_, v_a_635_);
lean_dec(v_m_634_);
v_r_637_ = lean_box(v_res_636_);
return v_r_637_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get___redArg(lean_object* v_x_638_, lean_object* v_x_639_, lean_object* v_m_640_, lean_object* v_a_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_x_638_, v_x_639_, v_m_640_, v_a_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get___redArg___boxed(lean_object* v_x_643_, lean_object* v_x_644_, lean_object* v_m_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Std_ExtDHashMap_get___redArg(v_x_643_, v_x_644_, v_m_645_, v_a_646_);
lean_dec(v_m_645_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get(lean_object* v_00_u03b1_648_, lean_object* v_00_u03b2_649_, lean_object* v_x_650_, lean_object* v_x_651_, lean_object* v_inst_652_, lean_object* v_m_653_, lean_object* v_a_654_, lean_object* v_h_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_x_650_, v_x_651_, v_m_653_, v_a_654_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get___boxed(lean_object* v_00_u03b1_657_, lean_object* v_00_u03b2_658_, lean_object* v_x_659_, lean_object* v_x_660_, lean_object* v_inst_661_, lean_object* v_m_662_, lean_object* v_a_663_, lean_object* v_h_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Std_ExtDHashMap_get(v_00_u03b1_657_, v_00_u03b2_658_, v_x_659_, v_x_660_, v_inst_661_, v_m_662_, v_a_663_, v_h_664_);
lean_dec(v_m_662_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x21___redArg(lean_object* v_x_666_, lean_object* v_x_667_, lean_object* v_m_668_, lean_object* v_a_669_, lean_object* v_inst_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(v_x_666_, v_x_667_, v_m_668_, v_a_669_, v_inst_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x21___redArg___boxed(lean_object* v_x_672_, lean_object* v_x_673_, lean_object* v_m_674_, lean_object* v_a_675_, lean_object* v_inst_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Std_ExtDHashMap_get_x21___redArg(v_x_672_, v_x_673_, v_m_674_, v_a_675_, v_inst_676_);
lean_dec(v_inst_676_);
lean_dec(v_m_674_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x21(lean_object* v_00_u03b1_678_, lean_object* v_00_u03b2_679_, lean_object* v_x_680_, lean_object* v_x_681_, lean_object* v_inst_682_, lean_object* v_m_683_, lean_object* v_a_684_, lean_object* v_inst_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(v_x_680_, v_x_681_, v_m_683_, v_a_684_, v_inst_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_get_x21___boxed(lean_object* v_00_u03b1_687_, lean_object* v_00_u03b2_688_, lean_object* v_x_689_, lean_object* v_x_690_, lean_object* v_inst_691_, lean_object* v_m_692_, lean_object* v_a_693_, lean_object* v_inst_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Std_ExtDHashMap_get_x21(v_00_u03b1_687_, v_00_u03b2_688_, v_x_689_, v_x_690_, v_inst_691_, v_m_692_, v_a_693_, v_inst_694_);
lean_dec(v_inst_694_);
lean_dec(v_m_692_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getD___redArg(lean_object* v_x_696_, lean_object* v_x_697_, lean_object* v_m_698_, lean_object* v_a_699_, lean_object* v_fallback_700_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(v_x_696_, v_x_697_, v_m_698_, v_a_699_, v_fallback_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getD___redArg___boxed(lean_object* v_x_702_, lean_object* v_x_703_, lean_object* v_m_704_, lean_object* v_a_705_, lean_object* v_fallback_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Std_ExtDHashMap_getD___redArg(v_x_702_, v_x_703_, v_m_704_, v_a_705_, v_fallback_706_);
lean_dec(v_fallback_706_);
lean_dec(v_m_704_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getD(lean_object* v_00_u03b1_708_, lean_object* v_00_u03b2_709_, lean_object* v_x_710_, lean_object* v_x_711_, lean_object* v_inst_712_, lean_object* v_m_713_, lean_object* v_a_714_, lean_object* v_fallback_715_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(v_x_710_, v_x_711_, v_m_713_, v_a_714_, v_fallback_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getD___boxed(lean_object* v_00_u03b1_717_, lean_object* v_00_u03b2_718_, lean_object* v_x_719_, lean_object* v_x_720_, lean_object* v_inst_721_, lean_object* v_m_722_, lean_object* v_a_723_, lean_object* v_fallback_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Std_ExtDHashMap_getD(v_00_u03b1_717_, v_00_u03b2_718_, v_x_719_, v_x_720_, v_inst_721_, v_m_722_, v_a_723_, v_fallback_724_);
lean_dec(v_fallback_724_);
lean_dec(v_m_722_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_erase___redArg(lean_object* v_x_726_, lean_object* v_x_727_, lean_object* v_m_728_, lean_object* v_a_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_726_, v_x_727_, v_m_728_, v_a_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_erase(lean_object* v_00_u03b1_731_, lean_object* v_00_u03b2_732_, lean_object* v_x_733_, lean_object* v_x_734_, lean_object* v_inst_735_, lean_object* v_inst_736_, lean_object* v_m_737_, lean_object* v_a_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_733_, v_x_734_, v_m_737_, v_a_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x3f___redArg(lean_object* v_x_740_, lean_object* v_x_741_, lean_object* v_m_742_, lean_object* v_a_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_740_, v_x_741_, v_m_742_, v_a_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x3f___redArg___boxed(lean_object* v_x_745_, lean_object* v_x_746_, lean_object* v_m_747_, lean_object* v_a_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Std_ExtDHashMap_Const_get_x3f___redArg(v_x_745_, v_x_746_, v_m_747_, v_a_748_);
lean_dec(v_m_747_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x3f(lean_object* v_00_u03b1_750_, lean_object* v_x_751_, lean_object* v_x_752_, lean_object* v_00_u03b2_753_, lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_m_756_, lean_object* v_a_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_751_, v_x_752_, v_m_756_, v_a_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x3f___boxed(lean_object* v_00_u03b1_759_, lean_object* v_x_760_, lean_object* v_x_761_, lean_object* v_00_u03b2_762_, lean_object* v_inst_763_, lean_object* v_inst_764_, lean_object* v_m_765_, lean_object* v_a_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Std_ExtDHashMap_Const_get_x3f(v_00_u03b1_759_, v_x_760_, v_x_761_, v_00_u03b2_762_, v_inst_763_, v_inst_764_, v_m_765_, v_a_766_);
lean_dec(v_m_765_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get___redArg(lean_object* v_x_768_, lean_object* v_x_769_, lean_object* v_m_770_, lean_object* v_a_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_x_768_, v_x_769_, v_m_770_, v_a_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get___redArg___boxed(lean_object* v_x_773_, lean_object* v_x_774_, lean_object* v_m_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Std_ExtDHashMap_Const_get___redArg(v_x_773_, v_x_774_, v_m_775_, v_a_776_);
lean_dec(v_m_775_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get(lean_object* v_00_u03b1_778_, lean_object* v_x_779_, lean_object* v_x_780_, lean_object* v_00_u03b2_781_, lean_object* v_inst_782_, lean_object* v_inst_783_, lean_object* v_m_784_, lean_object* v_a_785_, lean_object* v_h_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_x_779_, v_x_780_, v_m_784_, v_a_785_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get___boxed(lean_object* v_00_u03b1_788_, lean_object* v_x_789_, lean_object* v_x_790_, lean_object* v_00_u03b2_791_, lean_object* v_inst_792_, lean_object* v_inst_793_, lean_object* v_m_794_, lean_object* v_a_795_, lean_object* v_h_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Std_ExtDHashMap_Const_get(v_00_u03b1_788_, v_x_789_, v_x_790_, v_00_u03b2_791_, v_inst_792_, v_inst_793_, v_m_794_, v_a_795_, v_h_796_);
lean_dec(v_m_794_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getD___redArg(lean_object* v_x_798_, lean_object* v_x_799_, lean_object* v_m_800_, lean_object* v_a_801_, lean_object* v_fallback_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_x_798_, v_x_799_, v_m_800_, v_a_801_, v_fallback_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getD___redArg___boxed(lean_object* v_x_804_, lean_object* v_x_805_, lean_object* v_m_806_, lean_object* v_a_807_, lean_object* v_fallback_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Std_ExtDHashMap_Const_getD___redArg(v_x_804_, v_x_805_, v_m_806_, v_a_807_, v_fallback_808_);
lean_dec(v_fallback_808_);
lean_dec(v_m_806_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getD(lean_object* v_00_u03b1_810_, lean_object* v_x_811_, lean_object* v_x_812_, lean_object* v_00_u03b2_813_, lean_object* v_inst_814_, lean_object* v_inst_815_, lean_object* v_m_816_, lean_object* v_a_817_, lean_object* v_fallback_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_x_811_, v_x_812_, v_m_816_, v_a_817_, v_fallback_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getD___boxed(lean_object* v_00_u03b1_820_, lean_object* v_x_821_, lean_object* v_x_822_, lean_object* v_00_u03b2_823_, lean_object* v_inst_824_, lean_object* v_inst_825_, lean_object* v_m_826_, lean_object* v_a_827_, lean_object* v_fallback_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Std_ExtDHashMap_Const_getD(v_00_u03b1_820_, v_x_821_, v_x_822_, v_00_u03b2_823_, v_inst_824_, v_inst_825_, v_m_826_, v_a_827_, v_fallback_828_);
lean_dec(v_fallback_828_);
lean_dec(v_m_826_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x21___redArg(lean_object* v_x_830_, lean_object* v_x_831_, lean_object* v_inst_832_, lean_object* v_m_833_, lean_object* v_a_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_x_830_, v_x_831_, v_inst_832_, v_m_833_, v_a_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x21___redArg___boxed(lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v_inst_838_, lean_object* v_m_839_, lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Std_ExtDHashMap_Const_get_x21___redArg(v_x_836_, v_x_837_, v_inst_838_, v_m_839_, v_a_840_);
lean_dec(v_m_839_);
lean_dec(v_inst_838_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x21(lean_object* v_00_u03b1_842_, lean_object* v_x_843_, lean_object* v_x_844_, lean_object* v_00_u03b2_845_, lean_object* v_inst_846_, lean_object* v_inst_847_, lean_object* v_inst_848_, lean_object* v_m_849_, lean_object* v_a_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_x_843_, v_x_844_, v_inst_848_, v_m_849_, v_a_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_get_x21___boxed(lean_object* v_00_u03b1_852_, lean_object* v_x_853_, lean_object* v_x_854_, lean_object* v_00_u03b2_855_, lean_object* v_inst_856_, lean_object* v_inst_857_, lean_object* v_inst_858_, lean_object* v_m_859_, lean_object* v_a_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Std_ExtDHashMap_Const_get_x21(v_00_u03b1_852_, v_x_853_, v_x_854_, v_00_u03b2_855_, v_inst_856_, v_inst_857_, v_inst_858_, v_m_859_, v_a_860_);
lean_dec(v_m_859_);
lean_dec(v_inst_858_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getThenInsertIfNew_x3f___redArg(lean_object* v_x_862_, lean_object* v_x_863_, lean_object* v_m_864_, lean_object* v_a_865_, lean_object* v_b_866_){
_start:
{
lean_object* v_size_867_; lean_object* v_buckets_868_; lean_object* v___x_869_; lean_object* v___x_870_; uint64_t v___x_871_; uint64_t v___x_872_; uint64_t v___x_873_; uint64_t v___x_874_; uint64_t v_fold_875_; uint64_t v___x_876_; uint64_t v___x_877_; uint64_t v___x_878_; size_t v___x_879_; size_t v___x_880_; size_t v___x_881_; size_t v___x_882_; size_t v___x_883_; lean_object* v_bkt_884_; lean_object* v___x_885_; 
v_size_867_ = lean_ctor_get(v_m_864_, 0);
v_buckets_868_ = lean_ctor_get(v_m_864_, 1);
v___x_869_ = lean_array_get_size(v_buckets_868_);
lean_inc_ref(v_x_863_);
lean_inc_n(v_a_865_, 2);
v___x_870_ = lean_apply_1(v_x_863_, v_a_865_);
v___x_871_ = 32ULL;
v___x_872_ = lean_unbox_uint64(v___x_870_);
v___x_873_ = lean_uint64_shift_right(v___x_872_, v___x_871_);
v___x_874_ = lean_unbox_uint64(v___x_870_);
lean_dec_ref(v___x_870_);
v_fold_875_ = lean_uint64_xor(v___x_874_, v___x_873_);
v___x_876_ = 16ULL;
v___x_877_ = lean_uint64_shift_right(v_fold_875_, v___x_876_);
v___x_878_ = lean_uint64_xor(v_fold_875_, v___x_877_);
v___x_879_ = lean_uint64_to_usize(v___x_878_);
v___x_880_ = lean_usize_of_nat(v___x_869_);
v___x_881_ = ((size_t)1ULL);
v___x_882_ = lean_usize_sub(v___x_880_, v___x_881_);
v___x_883_ = lean_usize_land(v___x_879_, v___x_882_);
v_bkt_884_ = lean_array_uget_borrowed(v_buckets_868_, v___x_883_);
lean_inc(v_bkt_884_);
v___x_885_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_x_862_, v_a_865_, v_bkt_884_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_908_; 
lean_inc_ref(v_buckets_868_);
lean_inc(v_size_867_);
v_isSharedCheck_908_ = !lean_is_exclusive(v_m_864_);
if (v_isSharedCheck_908_ == 0)
{
lean_object* v_unused_909_; lean_object* v_unused_910_; 
v_unused_909_ = lean_ctor_get(v_m_864_, 1);
lean_dec(v_unused_909_);
v_unused_910_ = lean_ctor_get(v_m_864_, 0);
lean_dec(v_unused_910_);
v___x_887_ = v_m_864_;
v_isShared_888_ = v_isSharedCheck_908_;
goto v_resetjp_886_;
}
else
{
lean_dec(v_m_864_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_908_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_889_; lean_object* v_size_x27_890_; lean_object* v___x_891_; lean_object* v_buckets_x27_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_889_ = lean_unsigned_to_nat(1u);
v_size_x27_890_ = lean_nat_add(v_size_867_, v___x_889_);
lean_dec(v_size_867_);
lean_inc(v_bkt_884_);
v___x_891_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_891_, 0, v_a_865_);
lean_ctor_set(v___x_891_, 1, v_b_866_);
lean_ctor_set(v___x_891_, 2, v_bkt_884_);
v_buckets_x27_892_ = lean_array_uset(v_buckets_868_, v___x_883_, v___x_891_);
v___x_893_ = lean_unsigned_to_nat(4u);
v___x_894_ = lean_nat_mul(v_size_x27_890_, v___x_893_);
v___x_895_ = lean_unsigned_to_nat(3u);
v___x_896_ = lean_nat_div(v___x_894_, v___x_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_array_get_size(v_buckets_x27_892_);
v___x_898_ = lean_nat_dec_le(v___x_896_, v___x_897_);
lean_dec(v___x_896_);
if (v___x_898_ == 0)
{
lean_object* v_val_899_; lean_object* v___x_901_; 
v_val_899_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_863_, v_buckets_x27_892_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 1, v_val_899_);
lean_ctor_set(v___x_887_, 0, v_size_x27_890_);
v___x_901_ = v___x_887_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_size_x27_890_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_val_899_);
v___x_901_ = v_reuseFailAlloc_903_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
lean_object* v___x_902_; 
v___x_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_885_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
return v___x_902_;
}
}
else
{
lean_object* v___x_905_; 
lean_dec_ref(v_x_863_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 1, v_buckets_x27_892_);
lean_ctor_set(v___x_887_, 0, v_size_x27_890_);
v___x_905_ = v___x_887_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_size_x27_890_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_buckets_x27_892_);
v___x_905_ = v_reuseFailAlloc_907_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
lean_object* v___x_906_; 
v___x_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_885_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
return v___x_906_;
}
}
}
}
else
{
lean_object* v___x_911_; 
lean_dec(v_b_866_);
lean_dec(v_a_865_);
lean_dec_ref(v_x_863_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_885_);
lean_ctor_set(v___x_911_, 1, v_m_864_);
return v___x_911_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_912_, lean_object* v_x_913_, lean_object* v_x_914_, lean_object* v_00_u03b2_915_, lean_object* v_inst_916_, lean_object* v_inst_917_, lean_object* v_m_918_, lean_object* v_a_919_, lean_object* v_b_920_){
_start:
{
lean_object* v_size_921_; lean_object* v_buckets_922_; lean_object* v___x_923_; lean_object* v___x_924_; uint64_t v___x_925_; uint64_t v___x_926_; uint64_t v___x_927_; uint64_t v___x_928_; uint64_t v_fold_929_; uint64_t v___x_930_; uint64_t v___x_931_; uint64_t v___x_932_; size_t v___x_933_; size_t v___x_934_; size_t v___x_935_; size_t v___x_936_; size_t v___x_937_; lean_object* v_bkt_938_; lean_object* v___x_939_; 
v_size_921_ = lean_ctor_get(v_m_918_, 0);
v_buckets_922_ = lean_ctor_get(v_m_918_, 1);
v___x_923_ = lean_array_get_size(v_buckets_922_);
lean_inc_ref(v_x_914_);
lean_inc_n(v_a_919_, 2);
v___x_924_ = lean_apply_1(v_x_914_, v_a_919_);
v___x_925_ = 32ULL;
v___x_926_ = lean_unbox_uint64(v___x_924_);
v___x_927_ = lean_uint64_shift_right(v___x_926_, v___x_925_);
v___x_928_ = lean_unbox_uint64(v___x_924_);
lean_dec_ref(v___x_924_);
v_fold_929_ = lean_uint64_xor(v___x_928_, v___x_927_);
v___x_930_ = 16ULL;
v___x_931_ = lean_uint64_shift_right(v_fold_929_, v___x_930_);
v___x_932_ = lean_uint64_xor(v_fold_929_, v___x_931_);
v___x_933_ = lean_uint64_to_usize(v___x_932_);
v___x_934_ = lean_usize_of_nat(v___x_923_);
v___x_935_ = ((size_t)1ULL);
v___x_936_ = lean_usize_sub(v___x_934_, v___x_935_);
v___x_937_ = lean_usize_land(v___x_933_, v___x_936_);
v_bkt_938_ = lean_array_uget_borrowed(v_buckets_922_, v___x_937_);
lean_inc(v_bkt_938_);
v___x_939_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_x_913_, v_a_919_, v_bkt_938_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_962_; 
lean_inc_ref(v_buckets_922_);
lean_inc(v_size_921_);
v_isSharedCheck_962_ = !lean_is_exclusive(v_m_918_);
if (v_isSharedCheck_962_ == 0)
{
lean_object* v_unused_963_; lean_object* v_unused_964_; 
v_unused_963_ = lean_ctor_get(v_m_918_, 1);
lean_dec(v_unused_963_);
v_unused_964_ = lean_ctor_get(v_m_918_, 0);
lean_dec(v_unused_964_);
v___x_941_ = v_m_918_;
v_isShared_942_ = v_isSharedCheck_962_;
goto v_resetjp_940_;
}
else
{
lean_dec(v_m_918_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_962_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v_size_x27_944_; lean_object* v___x_945_; lean_object* v_buckets_x27_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; uint8_t v___x_952_; 
v___x_943_ = lean_unsigned_to_nat(1u);
v_size_x27_944_ = lean_nat_add(v_size_921_, v___x_943_);
lean_dec(v_size_921_);
lean_inc(v_bkt_938_);
v___x_945_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_945_, 0, v_a_919_);
lean_ctor_set(v___x_945_, 1, v_b_920_);
lean_ctor_set(v___x_945_, 2, v_bkt_938_);
v_buckets_x27_946_ = lean_array_uset(v_buckets_922_, v___x_937_, v___x_945_);
v___x_947_ = lean_unsigned_to_nat(4u);
v___x_948_ = lean_nat_mul(v_size_x27_944_, v___x_947_);
v___x_949_ = lean_unsigned_to_nat(3u);
v___x_950_ = lean_nat_div(v___x_948_, v___x_949_);
lean_dec(v___x_948_);
v___x_951_ = lean_array_get_size(v_buckets_x27_946_);
v___x_952_ = lean_nat_dec_le(v___x_950_, v___x_951_);
lean_dec(v___x_950_);
if (v___x_952_ == 0)
{
lean_object* v_val_953_; lean_object* v___x_955_; 
v_val_953_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_914_, v_buckets_x27_946_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 1, v_val_953_);
lean_ctor_set(v___x_941_, 0, v_size_x27_944_);
v___x_955_ = v___x_941_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_size_x27_944_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_val_953_);
v___x_955_ = v_reuseFailAlloc_957_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_956_; 
v___x_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_939_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
return v___x_956_;
}
}
else
{
lean_object* v___x_959_; 
lean_dec_ref(v_x_914_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 1, v_buckets_x27_946_);
lean_ctor_set(v___x_941_, 0, v_size_x27_944_);
v___x_959_ = v___x_941_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_size_x27_944_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_buckets_x27_946_);
v___x_959_ = v_reuseFailAlloc_961_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
lean_object* v___x_960_; 
v___x_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_939_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
return v___x_960_;
}
}
}
}
else
{
lean_object* v___x_965_; 
lean_dec(v_b_920_);
lean_dec(v_a_919_);
lean_dec_ref(v_x_914_);
v___x_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_939_);
lean_ctor_set(v___x_965_, 1, v_m_918_);
return v___x_965_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x3f___redArg(lean_object* v_x_966_, lean_object* v_x_967_, lean_object* v_m_968_, lean_object* v_a_969_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_966_, v_x_967_, v_m_968_, v_a_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x3f___redArg___boxed(lean_object* v_x_971_, lean_object* v_x_972_, lean_object* v_m_973_, lean_object* v_a_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Std_ExtDHashMap_getKey_x3f___redArg(v_x_971_, v_x_972_, v_m_973_, v_a_974_);
lean_dec(v_m_973_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x3f(lean_object* v_00_u03b1_976_, lean_object* v_00_u03b2_977_, lean_object* v_x_978_, lean_object* v_x_979_, lean_object* v_inst_980_, lean_object* v_inst_981_, lean_object* v_m_982_, lean_object* v_a_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_978_, v_x_979_, v_m_982_, v_a_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x3f___boxed(lean_object* v_00_u03b1_985_, lean_object* v_00_u03b2_986_, lean_object* v_x_987_, lean_object* v_x_988_, lean_object* v_inst_989_, lean_object* v_inst_990_, lean_object* v_m_991_, lean_object* v_a_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Std_ExtDHashMap_getKey_x3f(v_00_u03b1_985_, v_00_u03b2_986_, v_x_987_, v_x_988_, v_inst_989_, v_inst_990_, v_m_991_, v_a_992_);
lean_dec(v_m_991_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey___redArg(lean_object* v_x_994_, lean_object* v_x_995_, lean_object* v_m_996_, lean_object* v_a_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_x_994_, v_x_995_, v_m_996_, v_a_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey___redArg___boxed(lean_object* v_x_999_, lean_object* v_x_1000_, lean_object* v_m_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Std_ExtDHashMap_getKey___redArg(v_x_999_, v_x_1000_, v_m_1001_, v_a_1002_);
lean_dec(v_m_1001_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey(lean_object* v_00_u03b1_1004_, lean_object* v_00_u03b2_1005_, lean_object* v_x_1006_, lean_object* v_x_1007_, lean_object* v_inst_1008_, lean_object* v_inst_1009_, lean_object* v_m_1010_, lean_object* v_a_1011_, lean_object* v_h_1012_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_x_1006_, v_x_1007_, v_m_1010_, v_a_1011_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey___boxed(lean_object* v_00_u03b1_1014_, lean_object* v_00_u03b2_1015_, lean_object* v_x_1016_, lean_object* v_x_1017_, lean_object* v_inst_1018_, lean_object* v_inst_1019_, lean_object* v_m_1020_, lean_object* v_a_1021_, lean_object* v_h_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Std_ExtDHashMap_getKey(v_00_u03b1_1014_, v_00_u03b2_1015_, v_x_1016_, v_x_1017_, v_inst_1018_, v_inst_1019_, v_m_1020_, v_a_1021_, v_h_1022_);
lean_dec(v_m_1020_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x21___redArg(lean_object* v_x_1024_, lean_object* v_x_1025_, lean_object* v_inst_1026_, lean_object* v_m_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_1024_, v_x_1025_, v_inst_1026_, v_m_1027_, v_a_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x21___redArg___boxed(lean_object* v_x_1030_, lean_object* v_x_1031_, lean_object* v_inst_1032_, lean_object* v_m_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Std_ExtDHashMap_getKey_x21___redArg(v_x_1030_, v_x_1031_, v_inst_1032_, v_m_1033_, v_a_1034_);
lean_dec(v_m_1033_);
lean_dec(v_inst_1032_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x21(lean_object* v_00_u03b1_1036_, lean_object* v_00_u03b2_1037_, lean_object* v_x_1038_, lean_object* v_x_1039_, lean_object* v_inst_1040_, lean_object* v_inst_1041_, lean_object* v_inst_1042_, lean_object* v_m_1043_, lean_object* v_a_1044_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_1038_, v_x_1039_, v_inst_1042_, v_m_1043_, v_a_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKey_x21___boxed(lean_object* v_00_u03b1_1046_, lean_object* v_00_u03b2_1047_, lean_object* v_x_1048_, lean_object* v_x_1049_, lean_object* v_inst_1050_, lean_object* v_inst_1051_, lean_object* v_inst_1052_, lean_object* v_m_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Std_ExtDHashMap_getKey_x21(v_00_u03b1_1046_, v_00_u03b2_1047_, v_x_1048_, v_x_1049_, v_inst_1050_, v_inst_1051_, v_inst_1052_, v_m_1053_, v_a_1054_);
lean_dec(v_m_1053_);
lean_dec(v_inst_1052_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKeyD___redArg(lean_object* v_x_1056_, lean_object* v_x_1057_, lean_object* v_m_1058_, lean_object* v_a_1059_, lean_object* v_fallback_1060_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_1056_, v_x_1057_, v_m_1058_, v_a_1059_, v_fallback_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKeyD___redArg___boxed(lean_object* v_x_1062_, lean_object* v_x_1063_, lean_object* v_m_1064_, lean_object* v_a_1065_, lean_object* v_fallback_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Std_ExtDHashMap_getKeyD___redArg(v_x_1062_, v_x_1063_, v_m_1064_, v_a_1065_, v_fallback_1066_);
lean_dec(v_fallback_1066_);
lean_dec(v_m_1064_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKeyD(lean_object* v_00_u03b1_1068_, lean_object* v_00_u03b2_1069_, lean_object* v_x_1070_, lean_object* v_x_1071_, lean_object* v_inst_1072_, lean_object* v_inst_1073_, lean_object* v_m_1074_, lean_object* v_a_1075_, lean_object* v_fallback_1076_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_1070_, v_x_1071_, v_m_1074_, v_a_1075_, v_fallback_1076_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_getKeyD___boxed(lean_object* v_00_u03b1_1078_, lean_object* v_00_u03b2_1079_, lean_object* v_x_1080_, lean_object* v_x_1081_, lean_object* v_inst_1082_, lean_object* v_inst_1083_, lean_object* v_m_1084_, lean_object* v_a_1085_, lean_object* v_fallback_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Std_ExtDHashMap_getKeyD(v_00_u03b1_1078_, v_00_u03b2_1079_, v_x_1080_, v_x_1081_, v_inst_1082_, v_inst_1083_, v_m_1084_, v_a_1085_, v_fallback_1086_);
lean_dec(v_fallback_1086_);
lean_dec(v_m_1084_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_size___redArg(lean_object* v_m_1088_){
_start:
{
lean_object* v_size_1089_; 
v_size_1089_ = lean_ctor_get(v_m_1088_, 0);
lean_inc(v_size_1089_);
return v_size_1089_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_size___redArg___boxed(lean_object* v_m_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Std_ExtDHashMap_size___redArg(v_m_1090_);
lean_dec(v_m_1090_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_size(lean_object* v_00_u03b1_1092_, lean_object* v_00_u03b2_1093_, lean_object* v_x_1094_, lean_object* v_x_1095_, lean_object* v_inst_1096_, lean_object* v_inst_1097_, lean_object* v_m_1098_){
_start:
{
lean_object* v_size_1099_; 
v_size_1099_ = lean_ctor_get(v_m_1098_, 0);
lean_inc(v_size_1099_);
return v_size_1099_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_size___boxed(lean_object* v_00_u03b1_1100_, lean_object* v_00_u03b2_1101_, lean_object* v_x_1102_, lean_object* v_x_1103_, lean_object* v_inst_1104_, lean_object* v_inst_1105_, lean_object* v_m_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Std_ExtDHashMap_size(v_00_u03b1_1100_, v_00_u03b2_1101_, v_x_1102_, v_x_1103_, v_inst_1104_, v_inst_1105_, v_m_1106_);
lean_dec(v_m_1106_);
lean_dec_ref(v_x_1103_);
lean_dec_ref(v_x_1102_);
return v_res_1107_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_isEmpty___redArg(lean_object* v_m_1108_){
_start:
{
lean_object* v_size_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; 
v_size_1109_ = lean_ctor_get(v_m_1108_, 0);
v___x_1110_ = lean_unsigned_to_nat(0u);
v___x_1111_ = lean_nat_dec_eq(v_size_1109_, v___x_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_isEmpty___redArg___boxed(lean_object* v_m_1112_){
_start:
{
uint8_t v_res_1113_; lean_object* v_r_1114_; 
v_res_1113_ = l_Std_ExtDHashMap_isEmpty___redArg(v_m_1112_);
lean_dec(v_m_1112_);
v_r_1114_ = lean_box(v_res_1113_);
return v_r_1114_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_isEmpty(lean_object* v_00_u03b1_1115_, lean_object* v_00_u03b2_1116_, lean_object* v_x_1117_, lean_object* v_x_1118_, lean_object* v_inst_1119_, lean_object* v_inst_1120_, lean_object* v_m_1121_){
_start:
{
lean_object* v_size_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v_size_1122_ = lean_ctor_get(v_m_1121_, 0);
v___x_1123_ = lean_unsigned_to_nat(0u);
v___x_1124_ = lean_nat_dec_eq(v_size_1122_, v___x_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_isEmpty___boxed(lean_object* v_00_u03b1_1125_, lean_object* v_00_u03b2_1126_, lean_object* v_x_1127_, lean_object* v_x_1128_, lean_object* v_inst_1129_, lean_object* v_inst_1130_, lean_object* v_m_1131_){
_start:
{
uint8_t v_res_1132_; lean_object* v_r_1133_; 
v_res_1132_ = l_Std_ExtDHashMap_isEmpty(v_00_u03b1_1125_, v_00_u03b2_1126_, v_x_1127_, v_x_1128_, v_inst_1129_, v_inst_1130_, v_m_1131_);
lean_dec(v_m_1131_);
lean_dec_ref(v_x_1128_);
lean_dec_ref(v_x_1127_);
v_r_1133_ = lean_box(v_res_1132_);
return v_r_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filter___redArg(lean_object* v_f_1134_, lean_object* v_m_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1134_, v_m_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filter(lean_object* v_00_u03b1_1137_, lean_object* v_00_u03b2_1138_, lean_object* v_x_1139_, lean_object* v_x_1140_, lean_object* v_inst_1141_, lean_object* v_inst_1142_, lean_object* v_f_1143_, lean_object* v_m_1144_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1143_, v_m_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filter___boxed(lean_object* v_00_u03b1_1146_, lean_object* v_00_u03b2_1147_, lean_object* v_x_1148_, lean_object* v_x_1149_, lean_object* v_inst_1150_, lean_object* v_inst_1151_, lean_object* v_f_1152_, lean_object* v_m_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Std_ExtDHashMap_filter(v_00_u03b1_1146_, v_00_u03b2_1147_, v_x_1148_, v_x_1149_, v_inst_1150_, v_inst_1151_, v_f_1152_, v_m_1153_);
lean_dec_ref(v_x_1149_);
lean_dec_ref(v_x_1148_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_map___redArg(lean_object* v_f_1155_, lean_object* v_m_1156_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1155_, v_m_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_map(lean_object* v_00_u03b1_1158_, lean_object* v_00_u03b2_1159_, lean_object* v_00_u03b3_1160_, lean_object* v_x_1161_, lean_object* v_x_1162_, lean_object* v_inst_1163_, lean_object* v_inst_1164_, lean_object* v_f_1165_, lean_object* v_m_1166_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1165_, v_m_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_map___boxed(lean_object* v_00_u03b1_1168_, lean_object* v_00_u03b2_1169_, lean_object* v_00_u03b3_1170_, lean_object* v_x_1171_, lean_object* v_x_1172_, lean_object* v_inst_1173_, lean_object* v_inst_1174_, lean_object* v_f_1175_, lean_object* v_m_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Std_ExtDHashMap_map(v_00_u03b1_1168_, v_00_u03b2_1169_, v_00_u03b3_1170_, v_x_1171_, v_x_1172_, v_inst_1173_, v_inst_1174_, v_f_1175_, v_m_1176_);
lean_dec_ref(v_x_1172_);
lean_dec_ref(v_x_1171_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filterMap___redArg(lean_object* v_f_1178_, lean_object* v_m_1179_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1178_, v_m_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filterMap(lean_object* v_00_u03b1_1181_, lean_object* v_00_u03b2_1182_, lean_object* v_00_u03b3_1183_, lean_object* v_x_1184_, lean_object* v_x_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_, lean_object* v_f_1188_, lean_object* v_m_1189_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1188_, v_m_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_filterMap___boxed(lean_object* v_00_u03b1_1191_, lean_object* v_00_u03b2_1192_, lean_object* v_00_u03b3_1193_, lean_object* v_x_1194_, lean_object* v_x_1195_, lean_object* v_inst_1196_, lean_object* v_inst_1197_, lean_object* v_f_1198_, lean_object* v_m_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Std_ExtDHashMap_filterMap(v_00_u03b1_1191_, v_00_u03b2_1192_, v_00_u03b3_1193_, v_x_1194_, v_x_1195_, v_inst_1196_, v_inst_1197_, v_f_1198_, v_m_1199_);
lean_dec_ref(v_x_1195_);
lean_dec_ref(v_x_1194_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_modify___redArg(lean_object* v_x_1201_, lean_object* v_x_1202_, lean_object* v_m_1203_, lean_object* v_a_1204_, lean_object* v_f_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(v_x_1201_, v_x_1202_, v_m_1203_, v_a_1204_, v_f_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_modify(lean_object* v_00_u03b1_1207_, lean_object* v_00_u03b2_1208_, lean_object* v_x_1209_, lean_object* v_x_1210_, lean_object* v_inst_1211_, lean_object* v_m_1212_, lean_object* v_a_1213_, lean_object* v_f_1214_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(v_x_1209_, v_x_1210_, v_m_1212_, v_a_1213_, v_f_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_modify___redArg(lean_object* v_x_1216_, lean_object* v_x_1217_, lean_object* v_m_1218_, lean_object* v_a_1219_, lean_object* v_f_1220_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_x_1216_, v_x_1217_, v_m_1218_, v_a_1219_, v_f_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_modify(lean_object* v_00_u03b1_1222_, lean_object* v_x_1223_, lean_object* v_x_1224_, lean_object* v_inst_1225_, lean_object* v_inst_1226_, lean_object* v_00_u03b2_1227_, lean_object* v_m_1228_, lean_object* v_a_1229_, lean_object* v_f_1230_){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_x_1223_, v_x_1224_, v_m_1228_, v_a_1229_, v_f_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_alter___redArg(lean_object* v_x_1232_, lean_object* v_x_1233_, lean_object* v_m_1234_, lean_object* v_a_1235_, lean_object* v_f_1236_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(v_x_1232_, v_x_1233_, v_m_1234_, v_a_1235_, v_f_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_alter(lean_object* v_00_u03b1_1238_, lean_object* v_00_u03b2_1239_, lean_object* v_x_1240_, lean_object* v_x_1241_, lean_object* v_inst_1242_, lean_object* v_m_1243_, lean_object* v_a_1244_, lean_object* v_f_1245_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(v_x_1240_, v_x_1241_, v_m_1243_, v_a_1244_, v_f_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_alter___redArg(lean_object* v_x_1247_, lean_object* v_x_1248_, lean_object* v_m_1249_, lean_object* v_a_1250_, lean_object* v_f_1251_){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_x_1247_, v_x_1248_, v_m_1249_, v_a_1250_, v_f_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_alter(lean_object* v_00_u03b1_1253_, lean_object* v_x_1254_, lean_object* v_x_1255_, lean_object* v_inst_1256_, lean_object* v_inst_1257_, lean_object* v_00_u03b2_1258_, lean_object* v_m_1259_, lean_object* v_a_1260_, lean_object* v_f_1261_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_x_1254_, v_x_1255_, v_m_1259_, v_a_1260_, v_f_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insertMany___redArg___lam__0(lean_object* v_x_1263_, lean_object* v_x_1264_, lean_object* v_x_1265_, lean_object* v_____s_1266_){
_start:
{
lean_object* v_fst_1267_; lean_object* v_snd_1268_; lean_object* v_m_1269_; lean_object* v___x_1270_; 
v_fst_1267_ = lean_ctor_get(v_x_1265_, 0);
lean_inc(v_fst_1267_);
v_snd_1268_ = lean_ctor_get(v_x_1265_, 1);
lean_inc(v_snd_1268_);
lean_dec_ref(v_x_1265_);
v_m_1269_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1263_, v_x_1264_, v_____s_1266_, v_fst_1267_, v_snd_1268_);
v___x_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1270_, 0, v_m_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insertMany___redArg(lean_object* v_x_1271_, lean_object* v_x_1272_, lean_object* v_inst_1273_, lean_object* v_m_1274_, lean_object* v_l_1275_){
_start:
{
lean_object* v___f_1276_; lean_object* v___x_1277_; 
v___f_1276_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1276_, 0, v_x_1271_);
lean_closure_set(v___f_1276_, 1, v_x_1272_);
v___x_1277_ = lean_apply_4(v_inst_1273_, lean_box(0), v_l_1275_, v_m_1274_, v___f_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_insertMany(lean_object* v_00_u03b1_1278_, lean_object* v_00_u03b2_1279_, lean_object* v_x_1280_, lean_object* v_x_1281_, lean_object* v_inst_1282_, lean_object* v_inst_1283_, lean_object* v_00_u03c1_1284_, lean_object* v_inst_1285_, lean_object* v_m_1286_, lean_object* v_l_1287_){
_start:
{
lean_object* v___f_1288_; lean_object* v___x_1289_; 
v___f_1288_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1288_, 0, v_x_1280_);
lean_closure_set(v___f_1288_, 1, v_x_1281_);
v___x_1289_ = lean_apply_4(v_inst_1285_, lean_box(0), v_l_1287_, v_m_1286_, v___f_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertMany___redArg___lam__0(lean_object* v_x_1290_, lean_object* v_x_1291_, lean_object* v_x_1292_, lean_object* v_____s_1293_){
_start:
{
lean_object* v_fst_1294_; lean_object* v_snd_1295_; lean_object* v_m_1296_; lean_object* v___x_1297_; 
v_fst_1294_ = lean_ctor_get(v_x_1292_, 0);
lean_inc(v_fst_1294_);
v_snd_1295_ = lean_ctor_get(v_x_1292_, 1);
lean_inc(v_snd_1295_);
lean_dec_ref(v_x_1292_);
v_m_1296_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1290_, v_x_1291_, v_____s_1293_, v_fst_1294_, v_snd_1295_);
v___x_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1297_, 0, v_m_1296_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertMany___redArg(lean_object* v_x_1298_, lean_object* v_x_1299_, lean_object* v_inst_1300_, lean_object* v_m_1301_, lean_object* v_l_1302_){
_start:
{
lean_object* v___f_1303_; lean_object* v___x_1304_; 
v___f_1303_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_Const_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1303_, 0, v_x_1298_);
lean_closure_set(v___f_1303_, 1, v_x_1299_);
v___x_1304_ = lean_apply_4(v_inst_1300_, lean_box(0), v_l_1302_, v_m_1301_, v___f_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertMany(lean_object* v_00_u03b1_1305_, lean_object* v_x_1306_, lean_object* v_x_1307_, lean_object* v_inst_1308_, lean_object* v_inst_1309_, lean_object* v_00_u03b2_1310_, lean_object* v_00_u03c1_1311_, lean_object* v_inst_1312_, lean_object* v_m_1313_, lean_object* v_l_1314_){
_start:
{
lean_object* v___f_1315_; lean_object* v___x_1316_; 
v___f_1315_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_Const_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1315_, 0, v_x_1306_);
lean_closure_set(v___f_1315_, 1, v_x_1307_);
v___x_1316_ = lean_apply_4(v_inst_1312_, lean_box(0), v_l_1314_, v_m_1313_, v___f_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg___lam__0(lean_object* v_x_1317_, lean_object* v_x_1318_, lean_object* v_a_1319_, lean_object* v_____s_1320_){
_start:
{
lean_object* v___x_1321_; lean_object* v_m_1322_; lean_object* v___x_1323_; 
v___x_1321_ = lean_box(0);
v_m_1322_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_1317_, v_x_1318_, v_____s_1320_, v_a_1319_, v___x_1321_);
v___x_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1323_, 0, v_m_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg(lean_object* v_x_1324_, lean_object* v_x_1325_, lean_object* v_inst_1326_, lean_object* v_m_1327_, lean_object* v_l_1328_){
_start:
{
lean_object* v___f_1329_; lean_object* v___x_1330_; 
v___f_1329_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1329_, 0, v_x_1324_);
lean_closure_set(v___f_1329_, 1, v_x_1325_);
v___x_1330_ = lean_apply_4(v_inst_1326_, lean_box(0), v_l_1328_, v_m_1327_, v___f_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_insertManyIfNewUnit(lean_object* v_00_u03b1_1331_, lean_object* v_x_1332_, lean_object* v_x_1333_, lean_object* v_inst_1334_, lean_object* v_inst_1335_, lean_object* v_00_u03c1_1336_, lean_object* v_inst_1337_, lean_object* v_m_1338_, lean_object* v_l_1339_){
_start:
{
lean_object* v___f_1340_; lean_object* v___x_1341_; 
v___f_1340_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_Const_insertManyIfNewUnit___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1340_, 0, v_x_1332_);
lean_closure_set(v___f_1340_, 1, v_x_1333_);
v___x_1341_ = lean_apply_4(v_inst_1337_, lean_box(0), v_l_1339_, v_m_1338_, v___f_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_union___redArg___lam__0(lean_object* v_x_1342_, lean_object* v_x_1343_, lean_object* v_a_1344_, lean_object* v_b_1345_, lean_object* v_acc_1346_){
_start:
{
lean_object* v_r_1347_; lean_object* v___x_1348_; 
v_r_1347_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_1342_, v_x_1343_, v_acc_1346_, v_a_1344_, v_b_1345_);
v___x_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1348_, 0, v_r_1347_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_union___redArg___lam__1(lean_object* v___x_1349_, lean_object* v___f_1350_, lean_object* v_a_1351_, lean_object* v_x_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1349_, v___f_1350_, v_a_1351_, v___y_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_union___redArg(lean_object* v_x_1376_, lean_object* v_x_1377_, lean_object* v_m_u2081_1378_, lean_object* v_m_u2082_1379_){
_start:
{
lean_object* v_size_1380_; lean_object* v_buckets_1381_; lean_object* v_size_1382_; uint8_t v___x_1383_; 
v_size_1380_ = lean_ctor_get(v_m_u2081_1378_, 0);
v_buckets_1381_ = lean_ctor_get(v_m_u2081_1378_, 1);
v_size_1382_ = lean_ctor_get(v_m_u2082_1379_, 0);
v___x_1383_ = lean_nat_dec_le(v_size_1380_, v_size_1382_);
if (v___x_1383_ == 0)
{
lean_object* v___f_1384_; lean_object* v___x_1385_; 
v___f_1384_ = ((lean_object*)(l_Std_ExtDHashMap_union___redArg___closed__10));
v___x_1385_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1384_, v_x_1376_, v_x_1377_, v_m_u2081_1378_, v_m_u2082_1379_);
return v___x_1385_;
}
else
{
lean_object* v___f_1386_; lean_object* v___x_1387_; lean_object* v___f_1388_; size_t v_sz_1389_; size_t v___x_1390_; lean_object* v___x_1391_; 
lean_inc_ref(v_buckets_1381_);
lean_dec(v_m_u2081_1378_);
v___f_1386_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1386_, 0, v_x_1376_);
lean_closure_set(v___f_1386_, 1, v_x_1377_);
v___x_1387_ = ((lean_object*)(l_Std_ExtDHashMap_union___redArg___closed__9));
v___f_1388_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1388_, 0, v___x_1387_);
lean_closure_set(v___f_1388_, 1, v___f_1386_);
v_sz_1389_ = lean_array_size(v_buckets_1381_);
v___x_1390_ = ((size_t)0ULL);
v___x_1391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1387_, v_buckets_1381_, v___f_1388_, v_sz_1389_, v___x_1390_, v_m_u2082_1379_);
return v___x_1391_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_union(lean_object* v_00_u03b1_1392_, lean_object* v_00_u03b2_1393_, lean_object* v_x_1394_, lean_object* v_x_1395_, lean_object* v_inst_1396_, lean_object* v_inst_1397_, lean_object* v_m_u2081_1398_, lean_object* v_m_u2082_1399_){
_start:
{
lean_object* v_size_1400_; lean_object* v_buckets_1401_; lean_object* v_size_1402_; uint8_t v___x_1403_; 
v_size_1400_ = lean_ctor_get(v_m_u2081_1398_, 0);
v_buckets_1401_ = lean_ctor_get(v_m_u2081_1398_, 1);
v_size_1402_ = lean_ctor_get(v_m_u2082_1399_, 0);
v___x_1403_ = lean_nat_dec_le(v_size_1400_, v_size_1402_);
if (v___x_1403_ == 0)
{
lean_object* v___f_1404_; lean_object* v___x_1405_; 
v___f_1404_ = ((lean_object*)(l_Std_ExtDHashMap_union___redArg___closed__10));
v___x_1405_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1404_, v_x_1394_, v_x_1395_, v_m_u2081_1398_, v_m_u2082_1399_);
return v___x_1405_;
}
else
{
lean_object* v___f_1406_; lean_object* v___x_1407_; lean_object* v___f_1408_; size_t v_sz_1409_; size_t v___x_1410_; lean_object* v___x_1411_; 
lean_inc_ref(v_buckets_1401_);
lean_dec(v_m_u2081_1398_);
v___f_1406_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1406_, 0, v_x_1394_);
lean_closure_set(v___f_1406_, 1, v_x_1395_);
v___x_1407_ = ((lean_object*)(l_Std_ExtDHashMap_union___redArg___closed__9));
v___f_1408_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1408_, 0, v___x_1407_);
lean_closure_set(v___f_1408_, 1, v___f_1406_);
v_sz_1409_ = lean_array_size(v_buckets_1401_);
v___x_1410_ = ((size_t)0ULL);
v___x_1411_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1407_, v_buckets_1401_, v___f_1408_, v_sz_1409_, v___x_1410_, v_m_u2082_1399_);
return v___x_1411_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instUnionOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_1412_, lean_object* v_x_1413_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_union), 8, 6);
lean_closure_set(v___x_1414_, 0, lean_box(0));
lean_closure_set(v___x_1414_, 1, lean_box(0));
lean_closure_set(v___x_1414_, 2, v_x_1412_);
lean_closure_set(v___x_1414_, 3, v_x_1413_);
lean_closure_set(v___x_1414_, 4, lean_box(0));
lean_closure_set(v___x_1414_, 5, lean_box(0));
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instUnionOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1415_, lean_object* v_00_u03b2_1416_, lean_object* v_x_1417_, lean_object* v_x_1418_, lean_object* v_inst_1419_, lean_object* v_inst_1420_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_union), 8, 6);
lean_closure_set(v___x_1421_, 0, lean_box(0));
lean_closure_set(v___x_1421_, 1, lean_box(0));
lean_closure_set(v___x_1421_, 2, v_x_1417_);
lean_closure_set(v___x_1421_, 3, v_x_1418_);
lean_closure_set(v___x_1421_, 4, lean_box(0));
lean_closure_set(v___x_1421_, 5, lean_box(0));
return v___x_1421_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0(lean_object* v_x_1422_, lean_object* v_x_1423_, lean_object* v_inst_1424_, lean_object* v_m_u2081_1425_, lean_object* v_m_u2082_1426_){
_start:
{
uint8_t v___x_1427_; 
v___x_1427_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_x_1422_, v_x_1423_, v_inst_1424_, v_m_u2081_1425_, v_m_u2082_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0___boxed(lean_object* v_x_1428_, lean_object* v_x_1429_, lean_object* v_inst_1430_, lean_object* v_m_u2081_1431_, lean_object* v_m_u2082_1432_){
_start:
{
uint8_t v_res_1433_; lean_object* v_r_1434_; 
v_res_1433_ = l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0(v_x_1428_, v_x_1429_, v_inst_1430_, v_m_u2081_1431_, v_m_u2082_1432_);
v_r_1434_ = lean_box(v_res_1433_);
return v_r_1434_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg(lean_object* v_x_1435_, lean_object* v_x_1436_, lean_object* v_inst_1437_){
_start:
{
lean_object* v___f_1438_; 
v___f_1438_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1438_, 0, v_x_1435_);
lean_closure_set(v___f_1438_, 1, v_x_1436_);
lean_closure_set(v___f_1438_, 2, v_inst_1437_);
return v___f_1438_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instBEqOfLawfulBEq(lean_object* v_00_u03b1_1439_, lean_object* v_00_u03b2_1440_, lean_object* v_x_1441_, lean_object* v_x_1442_, lean_object* v_inst_1443_, lean_object* v_inst_1444_){
_start:
{
lean_object* v___f_1445_; 
v___f_1445_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_instBEqOfLawfulBEq___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1445_, 0, v_x_1441_);
lean_closure_set(v___f_1445_, 1, v_x_1442_);
lean_closure_set(v___f_1445_, 2, v_inst_1444_);
return v___f_1445_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___redArg(lean_object* v_inst_1446_, lean_object* v_inst_1447_, lean_object* v_inst_1448_, lean_object* v_x_1449_, lean_object* v_x_1450_){
_start:
{
uint8_t v___x_1451_; 
v___x_1451_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_inst_1446_, v_inst_1447_, v_inst_1448_, v_x_1449_, v_x_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___redArg___boxed(lean_object* v_inst_1452_, lean_object* v_inst_1453_, lean_object* v_inst_1454_, lean_object* v_x_1455_, lean_object* v_x_1456_){
_start:
{
uint8_t v_res_1457_; lean_object* v_r_1458_; 
v_res_1457_ = l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___redArg(v_inst_1452_, v_inst_1453_, v_inst_1454_, v_x_1455_, v_x_1456_);
v_r_1458_ = lean_box(v_res_1457_);
return v_r_1458_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq(lean_object* v_00_u03b1_1459_, lean_object* v_00_u03b2_1460_, lean_object* v_inst_1461_, lean_object* v_inst_1462_, lean_object* v_inst_1463_, lean_object* v_inst_1464_, lean_object* v_inst_1465_, lean_object* v_x_1466_, lean_object* v_x_1467_){
_start:
{
uint8_t v___x_1468_; 
v___x_1468_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_inst_1461_, v_inst_1463_, v_inst_1464_, v_x_1466_, v_x_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq___boxed(lean_object* v_00_u03b1_1469_, lean_object* v_00_u03b2_1470_, lean_object* v_inst_1471_, lean_object* v_inst_1472_, lean_object* v_inst_1473_, lean_object* v_inst_1474_, lean_object* v_inst_1475_, lean_object* v_x_1476_, lean_object* v_x_1477_){
_start:
{
uint8_t v_res_1478_; lean_object* v_r_1479_; 
v_res_1478_ = l_Std_ExtDHashMap_instDecidableEqOfLawfulBEq(v_00_u03b1_1469_, v_00_u03b2_1470_, v_inst_1471_, v_inst_1472_, v_inst_1473_, v_inst_1474_, v_inst_1475_, v_x_1476_, v_x_1477_);
v_r_1479_ = lean_box(v_res_1478_);
return v_r_1479_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_Const_beq___redArg(lean_object* v_x_1480_, lean_object* v_x_1481_, lean_object* v_inst_1482_, lean_object* v_m_u2081_1483_, lean_object* v_m_u2082_1484_){
_start:
{
uint8_t v___x_1485_; 
v___x_1485_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_x_1480_, v_x_1481_, v_inst_1482_, v_m_u2081_1483_, v_m_u2082_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_beq___redArg___boxed(lean_object* v_x_1486_, lean_object* v_x_1487_, lean_object* v_inst_1488_, lean_object* v_m_u2081_1489_, lean_object* v_m_u2082_1490_){
_start:
{
uint8_t v_res_1491_; lean_object* v_r_1492_; 
v_res_1491_ = l_Std_ExtDHashMap_Const_beq___redArg(v_x_1486_, v_x_1487_, v_inst_1488_, v_m_u2081_1489_, v_m_u2082_1490_);
v_r_1492_ = lean_box(v_res_1491_);
return v_r_1492_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_Const_beq(lean_object* v_00_u03b1_1493_, lean_object* v_x_1494_, lean_object* v_x_1495_, lean_object* v_00_u03b2_1496_, lean_object* v_inst_1497_, lean_object* v_inst_1498_, lean_object* v_inst_1499_, lean_object* v_m_u2081_1500_, lean_object* v_m_u2082_1501_){
_start:
{
uint8_t v___x_1502_; 
v___x_1502_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_x_1494_, v_x_1495_, v_inst_1499_, v_m_u2081_1500_, v_m_u2082_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_beq___boxed(lean_object* v_00_u03b1_1503_, lean_object* v_x_1504_, lean_object* v_x_1505_, lean_object* v_00_u03b2_1506_, lean_object* v_inst_1507_, lean_object* v_inst_1508_, lean_object* v_inst_1509_, lean_object* v_m_u2081_1510_, lean_object* v_m_u2082_1511_){
_start:
{
uint8_t v_res_1512_; lean_object* v_r_1513_; 
v_res_1512_ = l_Std_ExtDHashMap_Const_beq(v_00_u03b1_1503_, v_x_1504_, v_x_1505_, v_00_u03b2_1506_, v_inst_1507_, v_inst_1508_, v_inst_1509_, v_m_u2081_1510_, v_m_u2082_1511_);
v_r_1513_ = lean_box(v_res_1512_);
return v_r_1513_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_inter___redArg(lean_object* v_x_1514_, lean_object* v_x_1515_, lean_object* v_m_u2081_1516_, lean_object* v_m_u2082_1517_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_x_1514_, v_x_1515_, v_m_u2081_1516_, v_m_u2082_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_inter(lean_object* v_00_u03b1_1519_, lean_object* v_00_u03b2_1520_, lean_object* v_x_1521_, lean_object* v_x_1522_, lean_object* v_inst_1523_, lean_object* v_inst_1524_, lean_object* v_m_u2081_1525_, lean_object* v_m_u2082_1526_){
_start:
{
lean_object* v___x_1527_; 
v___x_1527_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_x_1521_, v_x_1522_, v_m_u2081_1525_, v_m_u2082_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInterOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_1528_, lean_object* v_x_1529_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_inter), 8, 6);
lean_closure_set(v___x_1530_, 0, lean_box(0));
lean_closure_set(v___x_1530_, 1, lean_box(0));
lean_closure_set(v___x_1530_, 2, v_x_1528_);
lean_closure_set(v___x_1530_, 3, v_x_1529_);
lean_closure_set(v___x_1530_, 4, lean_box(0));
lean_closure_set(v___x_1530_, 5, lean_box(0));
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instInterOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1531_, lean_object* v_00_u03b2_1532_, lean_object* v_x_1533_, lean_object* v_x_1534_, lean_object* v_inst_1535_, lean_object* v_inst_1536_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_inter), 8, 6);
lean_closure_set(v___x_1537_, 0, lean_box(0));
lean_closure_set(v___x_1537_, 1, lean_box(0));
lean_closure_set(v___x_1537_, 2, v_x_1533_);
lean_closure_set(v___x_1537_, 3, v_x_1534_);
lean_closure_set(v___x_1537_, 4, lean_box(0));
lean_closure_set(v___x_1537_, 5, lean_box(0));
return v___x_1537_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtDHashMap_diff___redArg___lam__0(lean_object* v_x_1538_, lean_object* v_x_1539_, lean_object* v_m_u2082_1540_, uint8_t v___x_1541_, lean_object* v_k_1542_, lean_object* v_x_1543_){
_start:
{
uint8_t v___x_1544_; 
v___x_1544_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_1538_, v_x_1539_, v_m_u2082_1540_, v_k_1542_);
if (v___x_1544_ == 0)
{
return v___x_1541_;
}
else
{
uint8_t v___x_1545_; 
v___x_1545_ = 0;
return v___x_1545_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_diff___redArg___lam__0___boxed(lean_object* v_x_1546_, lean_object* v_x_1547_, lean_object* v_m_u2082_1548_, lean_object* v___x_1549_, lean_object* v_k_1550_, lean_object* v_x_1551_){
_start:
{
uint8_t v___x_108__boxed_1552_; uint8_t v_res_1553_; lean_object* v_r_1554_; 
v___x_108__boxed_1552_ = lean_unbox(v___x_1549_);
v_res_1553_ = l_Std_ExtDHashMap_diff___redArg___lam__0(v_x_1546_, v_x_1547_, v_m_u2082_1548_, v___x_108__boxed_1552_, v_k_1550_, v_x_1551_);
lean_dec(v_x_1551_);
lean_dec(v_m_u2082_1548_);
v_r_1554_ = lean_box(v_res_1553_);
return v_r_1554_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_diff___redArg(lean_object* v_x_1555_, lean_object* v_x_1556_, lean_object* v_m_u2081_1557_, lean_object* v_m_u2082_1558_){
_start:
{
lean_object* v_size_1559_; lean_object* v_size_1560_; uint8_t v___x_1561_; 
v_size_1559_ = lean_ctor_get(v_m_u2081_1557_, 0);
v_size_1560_ = lean_ctor_get(v_m_u2082_1558_, 0);
v___x_1561_ = lean_nat_dec_le(v_size_1559_, v_size_1560_);
if (v___x_1561_ == 0)
{
lean_object* v___f_1562_; lean_object* v___x_1563_; 
v___f_1562_ = ((lean_object*)(l_Std_ExtDHashMap_union___redArg___closed__10));
v___x_1563_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1562_, v_x_1555_, v_x_1556_, v_m_u2081_1557_, v_m_u2082_1558_);
return v___x_1563_;
}
else
{
lean_object* v___x_1564_; lean_object* v___f_1565_; lean_object* v___x_1566_; 
v___x_1564_ = lean_box(v___x_1561_);
v___f_1565_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1565_, 0, v_x_1555_);
lean_closure_set(v___f_1565_, 1, v_x_1556_);
lean_closure_set(v___f_1565_, 2, v_m_u2082_1558_);
lean_closure_set(v___f_1565_, 3, v___x_1564_);
v___x_1566_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1565_, v_m_u2081_1557_);
return v___x_1566_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_diff(lean_object* v_00_u03b1_1567_, lean_object* v_00_u03b2_1568_, lean_object* v_x_1569_, lean_object* v_x_1570_, lean_object* v_inst_1571_, lean_object* v_inst_1572_, lean_object* v_m_u2081_1573_, lean_object* v_m_u2082_1574_){
_start:
{
lean_object* v_size_1575_; lean_object* v_size_1576_; uint8_t v___x_1577_; 
v_size_1575_ = lean_ctor_get(v_m_u2081_1573_, 0);
v_size_1576_ = lean_ctor_get(v_m_u2082_1574_, 0);
v___x_1577_ = lean_nat_dec_le(v_size_1575_, v_size_1576_);
if (v___x_1577_ == 0)
{
lean_object* v___f_1578_; lean_object* v___x_1579_; 
v___f_1578_ = ((lean_object*)(l_Std_ExtDHashMap_union___redArg___closed__10));
v___x_1579_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1578_, v_x_1569_, v_x_1570_, v_m_u2081_1573_, v_m_u2082_1574_);
return v___x_1579_;
}
else
{
lean_object* v___x_1580_; lean_object* v___f_1581_; lean_object* v___x_1582_; 
v___x_1580_ = lean_box(v___x_1577_);
v___f_1581_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1581_, 0, v_x_1569_);
lean_closure_set(v___f_1581_, 1, v_x_1570_);
lean_closure_set(v___f_1581_, 2, v_m_u2082_1574_);
lean_closure_set(v___f_1581_, 3, v___x_1580_);
v___x_1582_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1581_, v_m_u2081_1573_);
return v___x_1582_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instSDiffOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_1583_, lean_object* v_x_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_diff), 8, 6);
lean_closure_set(v___x_1585_, 0, lean_box(0));
lean_closure_set(v___x_1585_, 1, lean_box(0));
lean_closure_set(v___x_1585_, 2, v_x_1583_);
lean_closure_set(v___x_1585_, 3, v_x_1584_);
lean_closure_set(v___x_1585_, 4, lean_box(0));
lean_closure_set(v___x_1585_, 5, lean_box(0));
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_instSDiffOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1586_, lean_object* v_00_u03b2_1587_, lean_object* v_x_1588_, lean_object* v_x_1589_, lean_object* v_inst_1590_, lean_object* v_inst_1591_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = lean_alloc_closure((void*)(l_Std_ExtDHashMap_diff), 8, 6);
lean_closure_set(v___x_1592_, 0, lean_box(0));
lean_closure_set(v___x_1592_, 1, lean_box(0));
lean_closure_set(v___x_1592_, 2, v_x_1588_);
lean_closure_set(v___x_1592_, 3, v_x_1589_);
lean_closure_set(v___x_1592_, 4, lean_box(0));
lean_closure_set(v___x_1592_, 5, lean_box(0));
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_unitOfArray___redArg(lean_object* v_inst_1597_, lean_object* v_inst_1598_, lean_object* v_l_1599_){
_start:
{
lean_object* v___f_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___f_1600_ = ((lean_object*)(l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__1));
v___x_1601_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1);
v___x_1602_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1600_, v_inst_1597_, v_inst_1598_, v___x_1601_, v_l_1599_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_unitOfArray(lean_object* v_00_u03b1_1603_, lean_object* v_inst_1604_, lean_object* v_inst_1605_, lean_object* v_l_1606_){
_start:
{
lean_object* v___f_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___f_1607_ = ((lean_object*)(l_Std_ExtDHashMap_Const_unitOfArray___redArg___closed__1));
v___x_1608_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1);
v___x_1609_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1607_, v_inst_1604_, v_inst_1605_, v___x_1608_, v_l_1606_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_ofList___redArg(lean_object* v_inst_1614_, lean_object* v_inst_1615_, lean_object* v_l_1616_){
_start:
{
lean_object* v___f_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___f_1617_ = ((lean_object*)(l_Std_ExtDHashMap_ofList___redArg___closed__1));
v___x_1618_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1);
v___x_1619_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1617_, v_inst_1614_, v_inst_1615_, v___x_1618_, v_l_1616_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_ofList(lean_object* v_00_u03b1_1620_, lean_object* v_00_u03b2_1621_, lean_object* v_inst_1622_, lean_object* v_inst_1623_, lean_object* v_l_1624_){
_start:
{
lean_object* v___f_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___f_1625_ = ((lean_object*)(l_Std_ExtDHashMap_ofList___redArg___closed__1));
v___x_1626_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1);
v___x_1627_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1625_, v_inst_1622_, v_inst_1623_, v___x_1626_, v_l_1624_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_ofList___redArg(lean_object* v_inst_1628_, lean_object* v_inst_1629_, lean_object* v_l_1630_){
_start:
{
lean_object* v___f_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___f_1631_ = ((lean_object*)(l_Std_ExtDHashMap_ofList___redArg___closed__1));
v___x_1632_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1);
v___x_1633_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1631_, v_inst_1628_, v_inst_1629_, v___x_1632_, v_l_1630_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_ofList(lean_object* v_00_u03b1_1634_, lean_object* v_00_u03b2_1635_, lean_object* v_inst_1636_, lean_object* v_inst_1637_, lean_object* v_l_1638_){
_start:
{
lean_object* v___f_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___f_1639_ = ((lean_object*)(l_Std_ExtDHashMap_ofList___redArg___closed__1));
v___x_1640_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1);
v___x_1641_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1639_, v_inst_1636_, v_inst_1637_, v___x_1640_, v_l_1638_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_unitOfList___redArg(lean_object* v_inst_1642_, lean_object* v_inst_1643_, lean_object* v_l_1644_){
_start:
{
lean_object* v___f_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___f_1645_ = ((lean_object*)(l_Std_ExtDHashMap_ofList___redArg___closed__1));
v___x_1646_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1);
v___x_1647_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1645_, v_inst_1642_, v_inst_1643_, v___x_1646_, v_l_1644_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtDHashMap_Const_unitOfList(lean_object* v_00_u03b1_1648_, lean_object* v_inst_1649_, lean_object* v_inst_1650_, lean_object* v_l_1651_){
_start:
{
lean_object* v___f_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___f_1652_ = ((lean_object*)(l_Std_ExtDHashMap_ofList___redArg___closed__1));
v___x_1653_ = lean_obj_once(&l_Std_ExtDHashMap_instEmptyCollection___closed__1, &l_Std_ExtDHashMap_instEmptyCollection___closed__1_once, _init_l_Std_ExtDHashMap_instEmptyCollection___closed__1);
v___x_1654_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1652_, v_inst_1649_, v_inst_1650_, v___x_1653_, v_l_1651_);
return v___x_1654_;
}
}
lean_object* runtime_initialize_Std_Data_DHashMap_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_ExtDHashMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
