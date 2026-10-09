// Lean compiler output
// Module: Std.Data.ExtHashSet.Basic
// Imports: public import Std.Data.ExtHashMap.Basic
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
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_instDecidableEqPUnit___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instForInOfForIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_emptyWithCapacity___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_emptyWithCapacity___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_emptyWithCapacity(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_emptyWithCapacity___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_ExtHashSet_instEmptyCollection___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtHashSet_instEmptyCollection___redArg___closed__0;
static lean_once_cell_t l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instEmptyCollection___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_ExtHashSet_instEmptyCollection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtHashSet_instEmptyCollection___closed__0;
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instEmptyCollection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInhabited___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_ExtHashSet_instInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtHashSet_instInhabited___closed__0;
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInhabited(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInhabited___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInsertOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInsertOfEquivBEqOfLawfulHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInsertOfEquivBEqOfLawfulHashable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_containsThenInsert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_containsThenInsert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtHashSet_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_contains___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtHashSet_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instMembershipOfEquivBEqOfLawfulHashable___redArg();
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instMembershipOfEquivBEqOfLawfulHashable___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instMembershipOfEquivBEqOfLawfulHashable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instMembershipOfEquivBEqOfLawfulHashable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtHashSet_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instDecidableMem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtHashSet_instDecidableMem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instDecidableMem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_size(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtHashSet_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtHashSet_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtHashSet_ofList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtHashSet_ofList___redArg___closed__0 = (const lean_object*)&l_Std_ExtHashSet_ofList___redArg___closed__0_value;
static const lean_closure_object l_Std_ExtHashSet_ofList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtHashSet_ofList___redArg___closed__1 = (const lean_object*)&l_Std_ExtHashSet_ofList___redArg___closed__1_value;
static const lean_closure_object l_Std_ExtHashSet_ofList___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtHashSet_ofList___redArg___closed__2 = (const lean_object*)&l_Std_ExtHashSet_ofList___redArg___closed__2_value;
static const lean_closure_object l_Std_ExtHashSet_ofList___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtHashSet_ofList___redArg___closed__3 = (const lean_object*)&l_Std_ExtHashSet_ofList___redArg___closed__3_value;
static const lean_closure_object l_Std_ExtHashSet_ofList___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtHashSet_ofList___redArg___closed__4 = (const lean_object*)&l_Std_ExtHashSet_ofList___redArg___closed__4_value;
static const lean_closure_object l_Std_ExtHashSet_ofList___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtHashSet_ofList___redArg___closed__5 = (const lean_object*)&l_Std_ExtHashSet_ofList___redArg___closed__5_value;
static const lean_closure_object l_Std_ExtHashSet_ofList___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_ExtHashSet_ofList___redArg___closed__6 = (const lean_object*)&l_Std_ExtHashSet_ofList___redArg___closed__6_value;
static const lean_ctor_object l_Std_ExtHashSet_ofList___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_ExtHashSet_ofList___redArg___closed__0_value),((lean_object*)&l_Std_ExtHashSet_ofList___redArg___closed__1_value)}};
static const lean_object* l_Std_ExtHashSet_ofList___redArg___closed__7 = (const lean_object*)&l_Std_ExtHashSet_ofList___redArg___closed__7_value;
static const lean_ctor_object l_Std_ExtHashSet_ofList___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_ExtHashSet_ofList___redArg___closed__7_value),((lean_object*)&l_Std_ExtHashSet_ofList___redArg___closed__2_value),((lean_object*)&l_Std_ExtHashSet_ofList___redArg___closed__3_value),((lean_object*)&l_Std_ExtHashSet_ofList___redArg___closed__4_value),((lean_object*)&l_Std_ExtHashSet_ofList___redArg___closed__5_value)}};
static const lean_object* l_Std_ExtHashSet_ofList___redArg___closed__8 = (const lean_object*)&l_Std_ExtHashSet_ofList___redArg___closed__8_value;
static const lean_ctor_object l_Std_ExtHashSet_ofList___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_ExtHashSet_ofList___redArg___closed__8_value),((lean_object*)&l_Std_ExtHashSet_ofList___redArg___closed__6_value)}};
static const lean_object* l_Std_ExtHashSet_ofList___redArg___closed__9 = (const lean_object*)&l_Std_ExtHashSet_ofList___redArg___closed__9_value;
static const lean_closure_object l_Std_ExtHashSet_ofList___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_ExtHashSet_ofList___redArg___closed__9_value)} };
static const lean_object* l_Std_ExtHashSet_ofList___redArg___closed__10 = (const lean_object*)&l_Std_ExtHashSet_ofList___redArg___closed__10_value;
static const lean_closure_object l_Std_ExtHashSet_ofList___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_ExtHashSet_ofList___redArg___closed__10_value)} };
static const lean_object* l_Std_ExtHashSet_ofList___redArg___closed__11 = (const lean_object*)&l_Std_ExtHashSet_ofList___redArg___closed__11_value;
LEAN_EXPORT lean_object* l_Std_ExtHashSet_ofList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_ofList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtHashSet_filter___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_filter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_filter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_filter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insertMany___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_union___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_union___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtHashSet_union___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_ExtHashSet_ofList___redArg___closed__9_value)} };
static const lean_object* l_Std_ExtHashSet_union___redArg___closed__0 = (const lean_object*)&l_Std_ExtHashSet_union___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_ExtHashSet_union___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_union(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instUnionOfEquivBEqOfLawfulHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instUnionOfEquivBEqOfLawfulHashable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0;
LEAN_EXPORT uint8_t l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtHashSet_instDecidableEqOfLawfulBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_inter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInterOfEquivBEqOfLawfulHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInterOfEquivBEqOfLawfulHashable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_ExtHashSet_diff___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_diff___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_diff___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_diff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instSDiffOfEquivBEqOfLawfulHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instSDiffOfEquivBEqOfLawfulHashable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_ExtHashSet_ofArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_ExtHashSet_ofList___redArg___closed__9_value)} };
static const lean_object* l_Std_ExtHashSet_ofArray___redArg___closed__0 = (const lean_object*)&l_Std_ExtHashSet_ofArray___redArg___closed__0_value;
static const lean_closure_object l_Std_ExtHashSet_ofArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_ExtHashSet_ofArray___redArg___closed__0_value)} };
static const lean_object* l_Std_ExtHashSet_ofArray___redArg___closed__1 = (const lean_object*)&l_Std_ExtHashSet_ofArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_ExtHashSet_ofArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_ofArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_emptyWithCapacity___redArg(lean_object* v_capacity_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_2_ = lean_unsigned_to_nat(0u);
v___x_3_ = lean_unsigned_to_nat(4u);
v___x_4_ = lean_nat_mul(v_capacity_1_, v___x_3_);
v___x_5_ = lean_unsigned_to_nat(3u);
v___x_6_ = lean_nat_div(v___x_4_, v___x_5_);
lean_dec(v___x_4_);
v___x_7_ = l_Nat_nextPowerOfTwo(v___x_6_);
lean_dec(v___x_6_);
v___x_8_ = lean_box(0);
v___x_9_ = lean_mk_array(v___x_7_, v___x_8_);
v___x_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_10_, 0, v___x_2_);
lean_ctor_set(v___x_10_, 1, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_emptyWithCapacity___redArg___boxed(lean_object* v_capacity_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_ExtHashSet_emptyWithCapacity___redArg(v_capacity_11_);
lean_dec(v_capacity_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_emptyWithCapacity(lean_object* v_00_u03b1_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_capacity_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_17_ = lean_unsigned_to_nat(0u);
v___x_18_ = lean_unsigned_to_nat(4u);
v___x_19_ = lean_nat_mul(v_capacity_16_, v___x_18_);
v___x_20_ = lean_unsigned_to_nat(3u);
v___x_21_ = lean_nat_div(v___x_19_, v___x_20_);
lean_dec(v___x_19_);
v___x_22_ = l_Nat_nextPowerOfTwo(v___x_21_);
lean_dec(v___x_21_);
v___x_23_ = lean_box(0);
v___x_24_ = lean_mk_array(v___x_22_, v___x_23_);
v___x_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_25_, 0, v___x_17_);
lean_ctor_set(v___x_25_, 1, v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_emptyWithCapacity___boxed(lean_object* v_00_u03b1_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_capacity_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Std_ExtHashSet_emptyWithCapacity(v_00_u03b1_26_, v_inst_27_, v_inst_28_, v_capacity_29_);
lean_dec(v_capacity_29_);
lean_dec_ref(v_inst_28_);
lean_dec_ref(v_inst_27_);
return v_res_30_;
}
}
static lean_object* _init_l_Std_ExtHashSet_instEmptyCollection___redArg___closed__0(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_31_ = lean_box(0);
v___x_32_ = lean_unsigned_to_nat(16u);
v___x_33_ = lean_mk_array(v___x_32_, v___x_31_);
return v___x_33_;
}
}
static lean_object* _init_l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___redArg___closed__0, &l_Std_ExtHashSet_instEmptyCollection___redArg___closed__0_once, _init_l_Std_ExtHashSet_instEmptyCollection___redArg___closed__0);
v___x_35_ = lean_unsigned_to_nat(0u);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
lean_ctor_set(v___x_36_, 1, v___x_34_);
return v___x_36_;
}
}
lean_object* l_Std_ExtHashSet_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1);
return v___x_38_;
}
}
LEAN_EXPORT void l_Std_ExtHashSet_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_39_;
v_res_39_ = l_Std_ExtHashSet_instEmptyCollection___redArg();
stack->m_obj
 = v_res_39_;
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instEmptyCollection___redArg___boxed(lean_object* v___dummy_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Std_ExtHashSet_instEmptyCollection___redArg();
return v_res_41_;
}
}
static lean_object* _init_l_Std_ExtHashSet_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Std_ExtHashSet_instEmptyCollection___redArg();
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instEmptyCollection(lean_object* v_00_u03b1_43_, lean_object* v_inst_44_, lean_object* v_inst_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___closed__0, &l_Std_ExtHashSet_instEmptyCollection___closed__0_once, _init_l_Std_ExtHashSet_instEmptyCollection___closed__0);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instEmptyCollection___boxed(lean_object* v_00_u03b1_47_, lean_object* v_inst_48_, lean_object* v_inst_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Std_ExtHashSet_instEmptyCollection(v_00_u03b1_47_, v_inst_48_, v_inst_49_);
lean_dec_ref(v_inst_49_);
lean_dec_ref(v_inst_48_);
return v_res_50_;
}
}
lean_object* l_Std_ExtHashSet_instInhabited___redArg(){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1);
return v___x_52_;
}
}
LEAN_EXPORT void l_Std_ExtHashSet_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_53_;
v_res_53_ = l_Std_ExtHashSet_instInhabited___redArg();
stack->m_obj
 = v_res_53_;
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInhabited___redArg___boxed(lean_object* v___dummy_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Std_ExtHashSet_instInhabited___redArg();
return v_res_55_;
}
}
static lean_object* _init_l_Std_ExtHashSet_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Std_ExtHashSet_instInhabited___redArg();
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInhabited(lean_object* v_00_u03b1_57_, lean_object* v_inst_58_, lean_object* v_inst_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lean_obj_once(&l_Std_ExtHashSet_instInhabited___closed__0, &l_Std_ExtHashSet_instInhabited___closed__0_once, _init_l_Std_ExtHashSet_instInhabited___closed__0);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInhabited___boxed(lean_object* v_00_u03b1_61_, lean_object* v_inst_62_, lean_object* v_inst_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Std_ExtHashSet_instInhabited(v_00_u03b1_61_, v_inst_62_, v_inst_63_);
lean_dec_ref(v_inst_63_);
lean_dec_ref(v_inst_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insert___redArg(lean_object* v_x_65_, lean_object* v_x_66_, lean_object* v_m_67_, lean_object* v_a_68_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_box(0);
v___x_70_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_65_, v_x_66_, v_m_67_, v_a_68_, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insert(lean_object* v_00_u03b1_71_, lean_object* v_x_72_, lean_object* v_x_73_, lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_m_76_, lean_object* v_a_77_){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_box(0);
v___x_79_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_72_, v_x_73_, v_m_76_, v_a_77_, v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_80_, lean_object* v_x_81_, lean_object* v_a_82_){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_83_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1);
v___x_84_ = lean_box(0);
v___x_85_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_80_, v_x_81_, v___x_83_, v_a_82_, v___x_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_86_, lean_object* v_x_87_){
_start:
{
lean_object* v___f_88_; 
v___f_88_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_88_, 0, v_x_86_);
lean_closure_set(v___f_88_, 1, v_x_87_);
return v___f_88_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_89_, lean_object* v_x_90_, lean_object* v_x_91_, lean_object* v_inst_92_, lean_object* v_inst_93_){
_start:
{
lean_object* v___f_94_; 
v___f_94_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_94_, 0, v_x_90_);
lean_closure_set(v___f_94_, 1, v_x_91_);
return v___f_94_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInsertOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_95_, lean_object* v_x_96_, lean_object* v_a_97_, lean_object* v_s_98_){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = lean_box(0);
v___x_100_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_95_, v_x_96_, v_s_98_, v_a_97_, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInsertOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_101_, lean_object* v_x_102_){
_start:
{
lean_object* v___f_103_; 
v___f_103_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_instInsertOfEquivBEqOfLawfulHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_103_, 0, v_x_101_);
lean_closure_set(v___f_103_, 1, v_x_102_);
return v___f_103_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInsertOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_104_, lean_object* v_x_105_, lean_object* v_x_106_, lean_object* v_inst_107_, lean_object* v_inst_108_){
_start:
{
lean_object* v___f_109_; 
v___f_109_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_instInsertOfEquivBEqOfLawfulHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_109_, 0, v_x_105_);
lean_closure_set(v___f_109_, 1, v_x_106_);
return v___f_109_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_containsThenInsert___redArg(lean_object* v_x_110_, lean_object* v_x_111_, lean_object* v_m_112_, lean_object* v_a_113_){
_start:
{
lean_object* v_size_114_; lean_object* v_buckets_115_; lean_object* v___x_116_; lean_object* v___x_117_; uint64_t v___x_118_; uint64_t v___x_119_; uint64_t v___x_120_; uint64_t v___x_121_; uint64_t v_fold_122_; uint64_t v___x_123_; uint64_t v___x_124_; uint64_t v___x_125_; size_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; lean_object* v_bkt_131_; uint8_t v___x_132_; 
v_size_114_ = lean_ctor_get(v_m_112_, 0);
v_buckets_115_ = lean_ctor_get(v_m_112_, 1);
v___x_116_ = lean_array_get_size(v_buckets_115_);
lean_inc_ref(v_x_111_);
lean_inc_n(v_a_113_, 2);
v___x_117_ = lean_apply_1(v_x_111_, v_a_113_);
v___x_118_ = 32ULL;
v___x_119_ = lean_unbox_uint64(v___x_117_);
v___x_120_ = lean_uint64_shift_right(v___x_119_, v___x_118_);
v___x_121_ = lean_unbox_uint64(v___x_117_);
lean_dec_ref(v___x_117_);
v_fold_122_ = lean_uint64_xor(v___x_121_, v___x_120_);
v___x_123_ = 16ULL;
v___x_124_ = lean_uint64_shift_right(v_fold_122_, v___x_123_);
v___x_125_ = lean_uint64_xor(v_fold_122_, v___x_124_);
v___x_126_ = lean_uint64_to_usize(v___x_125_);
v___x_127_ = lean_usize_of_nat(v___x_116_);
v___x_128_ = ((size_t)1ULL);
v___x_129_ = lean_usize_sub(v___x_127_, v___x_128_);
v___x_130_ = lean_usize_land(v___x_126_, v___x_129_);
v_bkt_131_ = lean_array_uget_borrowed(v_buckets_115_, v___x_130_);
lean_inc(v_bkt_131_);
v___x_132_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_110_, v_a_113_, v_bkt_131_);
if (v___x_132_ == 0)
{
lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_158_; 
lean_inc_ref(v_buckets_115_);
lean_inc(v_size_114_);
v_isSharedCheck_158_ = !lean_is_exclusive(v_m_112_);
if (v_isSharedCheck_158_ == 0)
{
lean_object* v_unused_159_; lean_object* v_unused_160_; 
v_unused_159_ = lean_ctor_get(v_m_112_, 1);
lean_dec(v_unused_159_);
v_unused_160_ = lean_ctor_get(v_m_112_, 0);
lean_dec(v_unused_160_);
v___x_134_ = v_m_112_;
v_isShared_135_ = v_isSharedCheck_158_;
goto v_resetjp_133_;
}
else
{
lean_dec(v_m_112_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_158_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v_size_x27_138_; lean_object* v___x_139_; lean_object* v_buckets_x27_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; uint8_t v___x_146_; 
v___x_136_ = lean_box(0);
v___x_137_ = lean_unsigned_to_nat(1u);
v_size_x27_138_ = lean_nat_add(v_size_114_, v___x_137_);
lean_dec(v_size_114_);
lean_inc(v_bkt_131_);
v___x_139_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_139_, 0, v_a_113_);
lean_ctor_set(v___x_139_, 1, v___x_136_);
lean_ctor_set(v___x_139_, 2, v_bkt_131_);
v_buckets_x27_140_ = lean_array_uset(v_buckets_115_, v___x_130_, v___x_139_);
v___x_141_ = lean_unsigned_to_nat(4u);
v___x_142_ = lean_nat_mul(v_size_x27_138_, v___x_141_);
v___x_143_ = lean_unsigned_to_nat(3u);
v___x_144_ = lean_nat_div(v___x_142_, v___x_143_);
lean_dec(v___x_142_);
v___x_145_ = lean_array_get_size(v_buckets_x27_140_);
v___x_146_ = lean_nat_dec_le(v___x_144_, v___x_145_);
lean_dec(v___x_144_);
if (v___x_146_ == 0)
{
lean_object* v_val_147_; lean_object* v___x_149_; 
v_val_147_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_111_, v_buckets_x27_140_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 1, v_val_147_);
lean_ctor_set(v___x_134_, 0, v_size_x27_138_);
v___x_149_ = v___x_134_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_size_x27_138_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_val_147_);
v___x_149_ = v_reuseFailAlloc_152_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_box(v___x_132_);
v___x_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v___x_149_);
return v___x_151_;
}
}
else
{
lean_object* v___x_154_; 
lean_dec_ref(v_x_111_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 1, v_buckets_x27_140_);
lean_ctor_set(v___x_134_, 0, v_size_x27_138_);
v___x_154_ = v___x_134_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_size_x27_138_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_buckets_x27_140_);
v___x_154_ = v_reuseFailAlloc_157_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_box(v___x_132_);
v___x_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
lean_ctor_set(v___x_156_, 1, v___x_154_);
return v___x_156_;
}
}
}
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; 
lean_dec(v_a_113_);
lean_dec_ref(v_x_111_);
v___x_161_ = lean_box(v___x_132_);
v___x_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v_m_112_);
return v___x_162_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_containsThenInsert(lean_object* v_00_u03b1_163_, lean_object* v_x_164_, lean_object* v_x_165_, lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_m_168_, lean_object* v_a_169_){
_start:
{
lean_object* v_size_170_; lean_object* v_buckets_171_; lean_object* v___x_172_; lean_object* v___x_173_; uint64_t v___x_174_; uint64_t v___x_175_; uint64_t v___x_176_; uint64_t v___x_177_; uint64_t v_fold_178_; uint64_t v___x_179_; uint64_t v___x_180_; uint64_t v___x_181_; size_t v___x_182_; size_t v___x_183_; size_t v___x_184_; size_t v___x_185_; size_t v___x_186_; lean_object* v_bkt_187_; uint8_t v___x_188_; 
v_size_170_ = lean_ctor_get(v_m_168_, 0);
v_buckets_171_ = lean_ctor_get(v_m_168_, 1);
v___x_172_ = lean_array_get_size(v_buckets_171_);
lean_inc_ref(v_x_165_);
lean_inc_n(v_a_169_, 2);
v___x_173_ = lean_apply_1(v_x_165_, v_a_169_);
v___x_174_ = 32ULL;
v___x_175_ = lean_unbox_uint64(v___x_173_);
v___x_176_ = lean_uint64_shift_right(v___x_175_, v___x_174_);
v___x_177_ = lean_unbox_uint64(v___x_173_);
lean_dec_ref(v___x_173_);
v_fold_178_ = lean_uint64_xor(v___x_177_, v___x_176_);
v___x_179_ = 16ULL;
v___x_180_ = lean_uint64_shift_right(v_fold_178_, v___x_179_);
v___x_181_ = lean_uint64_xor(v_fold_178_, v___x_180_);
v___x_182_ = lean_uint64_to_usize(v___x_181_);
v___x_183_ = lean_usize_of_nat(v___x_172_);
v___x_184_ = ((size_t)1ULL);
v___x_185_ = lean_usize_sub(v___x_183_, v___x_184_);
v___x_186_ = lean_usize_land(v___x_182_, v___x_185_);
v_bkt_187_ = lean_array_uget_borrowed(v_buckets_171_, v___x_186_);
lean_inc(v_bkt_187_);
v___x_188_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_164_, v_a_169_, v_bkt_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_214_; 
lean_inc_ref(v_buckets_171_);
lean_inc(v_size_170_);
v_isSharedCheck_214_ = !lean_is_exclusive(v_m_168_);
if (v_isSharedCheck_214_ == 0)
{
lean_object* v_unused_215_; lean_object* v_unused_216_; 
v_unused_215_ = lean_ctor_get(v_m_168_, 1);
lean_dec(v_unused_215_);
v_unused_216_ = lean_ctor_get(v_m_168_, 0);
lean_dec(v_unused_216_);
v___x_190_ = v_m_168_;
v_isShared_191_ = v_isSharedCheck_214_;
goto v_resetjp_189_;
}
else
{
lean_dec(v_m_168_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_214_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v_size_x27_194_; lean_object* v___x_195_; lean_object* v_buckets_x27_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v___x_192_ = lean_box(0);
v___x_193_ = lean_unsigned_to_nat(1u);
v_size_x27_194_ = lean_nat_add(v_size_170_, v___x_193_);
lean_dec(v_size_170_);
lean_inc(v_bkt_187_);
v___x_195_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_195_, 0, v_a_169_);
lean_ctor_set(v___x_195_, 1, v___x_192_);
lean_ctor_set(v___x_195_, 2, v_bkt_187_);
v_buckets_x27_196_ = lean_array_uset(v_buckets_171_, v___x_186_, v___x_195_);
v___x_197_ = lean_unsigned_to_nat(4u);
v___x_198_ = lean_nat_mul(v_size_x27_194_, v___x_197_);
v___x_199_ = lean_unsigned_to_nat(3u);
v___x_200_ = lean_nat_div(v___x_198_, v___x_199_);
lean_dec(v___x_198_);
v___x_201_ = lean_array_get_size(v_buckets_x27_196_);
v___x_202_ = lean_nat_dec_le(v___x_200_, v___x_201_);
lean_dec(v___x_200_);
if (v___x_202_ == 0)
{
lean_object* v_val_203_; lean_object* v___x_205_; 
v_val_203_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_165_, v_buckets_x27_196_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 1, v_val_203_);
lean_ctor_set(v___x_190_, 0, v_size_x27_194_);
v___x_205_ = v___x_190_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_size_x27_194_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v_val_203_);
v___x_205_ = v_reuseFailAlloc_208_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_box(v___x_188_);
v___x_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v___x_205_);
return v___x_207_;
}
}
else
{
lean_object* v___x_210_; 
lean_dec_ref(v_x_165_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 1, v_buckets_x27_196_);
lean_ctor_set(v___x_190_, 0, v_size_x27_194_);
v___x_210_ = v___x_190_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_size_x27_194_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v_buckets_x27_196_);
v___x_210_ = v_reuseFailAlloc_213_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_box(v___x_188_);
v___x_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v___x_210_);
return v___x_212_;
}
}
}
}
else
{
lean_object* v___x_217_; lean_object* v___x_218_; 
lean_dec(v_a_169_);
lean_dec_ref(v_x_165_);
v___x_217_ = lean_box(v___x_188_);
v___x_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
lean_ctor_set(v___x_218_, 1, v_m_168_);
return v___x_218_;
}
}
}
uint8_t l_Std_ExtHashSet_contains___redArg(lean_object* v_x_219_, lean_object* v_x_220_, lean_object* v_m_221_, lean_object* v_a_222_){
_start:
{
uint8_t v___x_223_; 
v___x_223_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_219_, v_x_220_, v_m_221_, v_a_222_);
return v___x_223_;
}
}
LEAN_EXPORT void l_Std_ExtHashSet_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_219_ = stack[0].m_obj;
lean_object* v_x_220_ = stack[1].m_obj;
lean_object* v_m_221_ = stack[2].m_obj;
lean_object* v_a_222_ = stack[3].m_obj;
uint8_t v_res_224_;
v_res_224_ = l_Std_ExtHashSet_contains___redArg(v_x_219_, v_x_220_, v_m_221_, v_a_222_);
stack->m_num = v_res_224_;
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_contains___redArg___boxed(lean_object* v_x_225_, lean_object* v_x_226_, lean_object* v_m_227_, lean_object* v_a_228_){
_start:
{
uint8_t v_res_229_; lean_object* v_r_230_; 
v_res_229_ = l_Std_ExtHashSet_contains___redArg(v_x_225_, v_x_226_, v_m_227_, v_a_228_);
lean_dec(v_m_227_);
v_r_230_ = lean_box(v_res_229_);
return v_r_230_;
}
}
uint8_t l_Std_ExtHashSet_contains(lean_object* v_00_u03b1_231_, lean_object* v_x_232_, lean_object* v_x_233_, lean_object* v_inst_234_, lean_object* v_inst_235_, lean_object* v_m_236_, lean_object* v_a_237_){
_start:
{
uint8_t v___x_238_; 
v___x_238_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_232_, v_x_233_, v_m_236_, v_a_237_);
return v___x_238_;
}
}
LEAN_EXPORT void l_Std_ExtHashSet_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_232_ = stack[1].m_obj;
lean_object* v_x_233_ = stack[2].m_obj;
lean_object* v_m_236_ = stack[5].m_obj;
lean_object* v_a_237_ = stack[6].m_obj;
uint8_t v_res_239_;
v_res_239_ = l_Std_ExtHashSet_contains(lean_box(0), v_x_232_, v_x_233_, lean_box(0), lean_box(0), v_m_236_, v_a_237_);
stack->m_num = v_res_239_;
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_contains___boxed(lean_object* v_00_u03b1_240_, lean_object* v_x_241_, lean_object* v_x_242_, lean_object* v_inst_243_, lean_object* v_inst_244_, lean_object* v_m_245_, lean_object* v_a_246_){
_start:
{
uint8_t v_res_247_; lean_object* v_r_248_; 
v_res_247_ = l_Std_ExtHashSet_contains(v_00_u03b1_240_, v_x_241_, v_x_242_, v_inst_243_, v_inst_244_, v_m_245_, v_a_246_);
lean_dec(v_m_245_);
v_r_248_ = lean_box(v_res_247_);
return v_r_248_;
}
}
lean_object* l_Std_ExtHashSet_instMembershipOfEquivBEqOfLawfulHashable___redArg(){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = lean_box(0);
return v___x_250_;
}
}
LEAN_EXPORT void l_Std_ExtHashSet_instMembershipOfEquivBEqOfLawfulHashable___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_251_;
v_res_251_ = l_Std_ExtHashSet_instMembershipOfEquivBEqOfLawfulHashable___redArg();
stack->m_obj
 = v_res_251_;
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instMembershipOfEquivBEqOfLawfulHashable___redArg___boxed(lean_object* v___dummy_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Std_ExtHashSet_instMembershipOfEquivBEqOfLawfulHashable___redArg();
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instMembershipOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_254_, lean_object* v_inst_255_, lean_object* v_inst_256_, lean_object* v_inst_257_, lean_object* v_inst_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = lean_box(0);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instMembershipOfEquivBEqOfLawfulHashable___boxed(lean_object* v_00_u03b1_260_, lean_object* v_inst_261_, lean_object* v_inst_262_, lean_object* v_inst_263_, lean_object* v_inst_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Std_ExtHashSet_instMembershipOfEquivBEqOfLawfulHashable(v_00_u03b1_260_, v_inst_261_, v_inst_262_, v_inst_263_, v_inst_264_);
lean_dec_ref(v_inst_262_);
lean_dec_ref(v_inst_261_);
return v_res_265_;
}
}
uint8_t l_Std_ExtHashSet_instDecidableMem___redArg(lean_object* v_inst_266_, lean_object* v_inst_267_, lean_object* v_m_268_, lean_object* v_a_269_){
_start:
{
uint8_t v___x_270_; 
v___x_270_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_266_, v_inst_267_, v_m_268_, v_a_269_);
return v___x_270_;
}
}
LEAN_EXPORT void l_Std_ExtHashSet_instDecidableMem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_266_ = stack[0].m_obj;
lean_object* v_inst_267_ = stack[1].m_obj;
lean_object* v_m_268_ = stack[2].m_obj;
lean_object* v_a_269_ = stack[3].m_obj;
uint8_t v_res_271_;
v_res_271_ = l_Std_ExtHashSet_instDecidableMem___redArg(v_inst_266_, v_inst_267_, v_m_268_, v_a_269_);
stack->m_num = v_res_271_;
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instDecidableMem___redArg___boxed(lean_object* v_inst_272_, lean_object* v_inst_273_, lean_object* v_m_274_, lean_object* v_a_275_){
_start:
{
uint8_t v_res_276_; lean_object* v_r_277_; 
v_res_276_ = l_Std_ExtHashSet_instDecidableMem___redArg(v_inst_272_, v_inst_273_, v_m_274_, v_a_275_);
lean_dec(v_m_274_);
v_r_277_ = lean_box(v_res_276_);
return v_r_277_;
}
}
uint8_t l_Std_ExtHashSet_instDecidableMem(lean_object* v_00_u03b1_278_, lean_object* v_inst_279_, lean_object* v_inst_280_, lean_object* v_inst_281_, lean_object* v_inst_282_, lean_object* v_m_283_, lean_object* v_a_284_){
_start:
{
uint8_t v___x_285_; 
v___x_285_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_279_, v_inst_280_, v_m_283_, v_a_284_);
return v___x_285_;
}
}
LEAN_EXPORT void l_Std_ExtHashSet_instDecidableMem_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_279_ = stack[1].m_obj;
lean_object* v_inst_280_ = stack[2].m_obj;
lean_object* v_m_283_ = stack[5].m_obj;
lean_object* v_a_284_ = stack[6].m_obj;
uint8_t v_res_286_;
v_res_286_ = l_Std_ExtHashSet_instDecidableMem(lean_box(0), v_inst_279_, v_inst_280_, lean_box(0), lean_box(0), v_m_283_, v_a_284_);
stack->m_num = v_res_286_;
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instDecidableMem___boxed(lean_object* v_00_u03b1_287_, lean_object* v_inst_288_, lean_object* v_inst_289_, lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v_m_292_, lean_object* v_a_293_){
_start:
{
uint8_t v_res_294_; lean_object* v_r_295_; 
v_res_294_ = l_Std_ExtHashSet_instDecidableMem(v_00_u03b1_287_, v_inst_288_, v_inst_289_, v_inst_290_, v_inst_291_, v_m_292_, v_a_293_);
lean_dec(v_m_292_);
v_r_295_ = lean_box(v_res_294_);
return v_r_295_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_erase___redArg(lean_object* v_x_296_, lean_object* v_x_297_, lean_object* v_m_298_, lean_object* v_a_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_296_, v_x_297_, v_m_298_, v_a_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_erase(lean_object* v_00_u03b1_301_, lean_object* v_x_302_, lean_object* v_x_303_, lean_object* v_inst_304_, lean_object* v_inst_305_, lean_object* v_m_306_, lean_object* v_a_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_302_, v_x_303_, v_m_306_, v_a_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_size___redArg(lean_object* v_m_309_){
_start:
{
lean_object* v_size_310_; 
v_size_310_ = lean_ctor_get(v_m_309_, 0);
lean_inc(v_size_310_);
return v_size_310_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_size___redArg___boxed(lean_object* v_m_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Std_ExtHashSet_size___redArg(v_m_311_);
lean_dec(v_m_311_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_size(lean_object* v_00_u03b1_313_, lean_object* v_x_314_, lean_object* v_x_315_, lean_object* v_inst_316_, lean_object* v_inst_317_, lean_object* v_m_318_){
_start:
{
lean_object* v_size_319_; 
v_size_319_ = lean_ctor_get(v_m_318_, 0);
lean_inc(v_size_319_);
return v_size_319_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_size___boxed(lean_object* v_00_u03b1_320_, lean_object* v_x_321_, lean_object* v_x_322_, lean_object* v_inst_323_, lean_object* v_inst_324_, lean_object* v_m_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Std_ExtHashSet_size(v_00_u03b1_320_, v_x_321_, v_x_322_, v_inst_323_, v_inst_324_, v_m_325_);
lean_dec(v_m_325_);
lean_dec_ref(v_x_322_);
lean_dec_ref(v_x_321_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x3f___redArg(lean_object* v_x_327_, lean_object* v_x_328_, lean_object* v_m_329_, lean_object* v_a_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_327_, v_x_328_, v_m_329_, v_a_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x3f___redArg___boxed(lean_object* v_x_332_, lean_object* v_x_333_, lean_object* v_m_334_, lean_object* v_a_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Std_ExtHashSet_get_x3f___redArg(v_x_332_, v_x_333_, v_m_334_, v_a_335_);
lean_dec(v_m_334_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x3f(lean_object* v_00_u03b1_337_, lean_object* v_x_338_, lean_object* v_x_339_, lean_object* v_inst_340_, lean_object* v_inst_341_, lean_object* v_m_342_, lean_object* v_a_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_338_, v_x_339_, v_m_342_, v_a_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x3f___boxed(lean_object* v_00_u03b1_345_, lean_object* v_x_346_, lean_object* v_x_347_, lean_object* v_inst_348_, lean_object* v_inst_349_, lean_object* v_m_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Std_ExtHashSet_get_x3f(v_00_u03b1_345_, v_x_346_, v_x_347_, v_inst_348_, v_inst_349_, v_m_350_, v_a_351_);
lean_dec(v_m_350_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get___redArg(lean_object* v_x_353_, lean_object* v_x_354_, lean_object* v_m_355_, lean_object* v_a_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_x_353_, v_x_354_, v_m_355_, v_a_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get___redArg___boxed(lean_object* v_x_358_, lean_object* v_x_359_, lean_object* v_m_360_, lean_object* v_a_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Std_ExtHashSet_get___redArg(v_x_358_, v_x_359_, v_m_360_, v_a_361_);
lean_dec(v_m_360_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get(lean_object* v_00_u03b1_363_, lean_object* v_x_364_, lean_object* v_x_365_, lean_object* v_inst_366_, lean_object* v_inst_367_, lean_object* v_m_368_, lean_object* v_a_369_, lean_object* v_h_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_x_364_, v_x_365_, v_m_368_, v_a_369_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get___boxed(lean_object* v_00_u03b1_372_, lean_object* v_x_373_, lean_object* v_x_374_, lean_object* v_inst_375_, lean_object* v_inst_376_, lean_object* v_m_377_, lean_object* v_a_378_, lean_object* v_h_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Std_ExtHashSet_get(v_00_u03b1_372_, v_x_373_, v_x_374_, v_inst_375_, v_inst_376_, v_m_377_, v_a_378_, v_h_379_);
lean_dec(v_m_377_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_getD___redArg(lean_object* v_x_381_, lean_object* v_x_382_, lean_object* v_m_383_, lean_object* v_a_384_, lean_object* v_fallback_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_381_, v_x_382_, v_m_383_, v_a_384_, v_fallback_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_getD___redArg___boxed(lean_object* v_x_387_, lean_object* v_x_388_, lean_object* v_m_389_, lean_object* v_a_390_, lean_object* v_fallback_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Std_ExtHashSet_getD___redArg(v_x_387_, v_x_388_, v_m_389_, v_a_390_, v_fallback_391_);
lean_dec(v_fallback_391_);
lean_dec(v_m_389_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_getD(lean_object* v_00_u03b1_393_, lean_object* v_x_394_, lean_object* v_x_395_, lean_object* v_inst_396_, lean_object* v_inst_397_, lean_object* v_m_398_, lean_object* v_a_399_, lean_object* v_fallback_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_394_, v_x_395_, v_m_398_, v_a_399_, v_fallback_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_getD___boxed(lean_object* v_00_u03b1_402_, lean_object* v_x_403_, lean_object* v_x_404_, lean_object* v_inst_405_, lean_object* v_inst_406_, lean_object* v_m_407_, lean_object* v_a_408_, lean_object* v_fallback_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Std_ExtHashSet_getD(v_00_u03b1_402_, v_x_403_, v_x_404_, v_inst_405_, v_inst_406_, v_m_407_, v_a_408_, v_fallback_409_);
lean_dec(v_fallback_409_);
lean_dec(v_m_407_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x21___redArg(lean_object* v_x_411_, lean_object* v_x_412_, lean_object* v_inst_413_, lean_object* v_m_414_, lean_object* v_a_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_411_, v_x_412_, v_inst_413_, v_m_414_, v_a_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x21___redArg___boxed(lean_object* v_x_417_, lean_object* v_x_418_, lean_object* v_inst_419_, lean_object* v_m_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Std_ExtHashSet_get_x21___redArg(v_x_417_, v_x_418_, v_inst_419_, v_m_420_, v_a_421_);
lean_dec(v_m_420_);
lean_dec(v_inst_419_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x21(lean_object* v_00_u03b1_423_, lean_object* v_x_424_, lean_object* v_x_425_, lean_object* v_inst_426_, lean_object* v_inst_427_, lean_object* v_inst_428_, lean_object* v_m_429_, lean_object* v_a_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_424_, v_x_425_, v_inst_428_, v_m_429_, v_a_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x21___boxed(lean_object* v_00_u03b1_432_, lean_object* v_x_433_, lean_object* v_x_434_, lean_object* v_inst_435_, lean_object* v_inst_436_, lean_object* v_inst_437_, lean_object* v_m_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Std_ExtHashSet_get_x21(v_00_u03b1_432_, v_x_433_, v_x_434_, v_inst_435_, v_inst_436_, v_inst_437_, v_m_438_, v_a_439_);
lean_dec(v_m_438_);
lean_dec(v_inst_437_);
return v_res_440_;
}
}
uint8_t l_Std_ExtHashSet_isEmpty___redArg(lean_object* v_m_441_){
_start:
{
lean_object* v_size_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v_size_442_ = lean_ctor_get(v_m_441_, 0);
v___x_443_ = lean_unsigned_to_nat(0u);
v___x_444_ = lean_nat_dec_eq(v_size_442_, v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT void l_Std_ExtHashSet_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_441_ = stack[0].m_obj;
uint8_t v_res_445_;
v_res_445_ = l_Std_ExtHashSet_isEmpty___redArg(v_m_441_);
stack->m_num = v_res_445_;
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_isEmpty___redArg___boxed(lean_object* v_m_446_){
_start:
{
uint8_t v_res_447_; lean_object* v_r_448_; 
v_res_447_ = l_Std_ExtHashSet_isEmpty___redArg(v_m_446_);
lean_dec(v_m_446_);
v_r_448_ = lean_box(v_res_447_);
return v_r_448_;
}
}
uint8_t l_Std_ExtHashSet_isEmpty(lean_object* v_00_u03b1_449_, lean_object* v_x_450_, lean_object* v_x_451_, lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_m_454_){
_start:
{
lean_object* v_size_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v_size_455_ = lean_ctor_get(v_m_454_, 0);
v___x_456_ = lean_unsigned_to_nat(0u);
v___x_457_ = lean_nat_dec_eq(v_size_455_, v___x_456_);
return v___x_457_;
}
}
LEAN_EXPORT void l_Std_ExtHashSet_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_450_ = stack[1].m_obj;
lean_object* v_x_451_ = stack[2].m_obj;
lean_object* v_m_454_ = stack[5].m_obj;
uint8_t v_res_458_;
v_res_458_ = l_Std_ExtHashSet_isEmpty(lean_box(0), v_x_450_, v_x_451_, lean_box(0), lean_box(0), v_m_454_);
stack->m_num = v_res_458_;
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_isEmpty___boxed(lean_object* v_00_u03b1_459_, lean_object* v_x_460_, lean_object* v_x_461_, lean_object* v_inst_462_, lean_object* v_inst_463_, lean_object* v_m_464_){
_start:
{
uint8_t v_res_465_; lean_object* v_r_466_; 
v_res_465_ = l_Std_ExtHashSet_isEmpty(v_00_u03b1_459_, v_x_460_, v_x_461_, v_inst_462_, v_inst_463_, v_m_464_);
lean_dec(v_m_464_);
lean_dec_ref(v_x_461_);
lean_dec_ref(v_x_460_);
v_r_466_ = lean_box(v_res_465_);
return v_r_466_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_ofList___redArg(lean_object* v_inst_490_, lean_object* v_inst_491_, lean_object* v_l_492_){
_start:
{
lean_object* v___f_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___f_493_ = ((lean_object*)(l_Std_ExtHashSet_ofList___redArg___closed__11));
v___x_494_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1);
v___x_495_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_493_, v_inst_490_, v_inst_491_, v___x_494_, v_l_492_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_ofList(lean_object* v_00_u03b1_496_, lean_object* v_inst_497_, lean_object* v_inst_498_, lean_object* v_l_499_){
_start:
{
lean_object* v___f_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___f_500_ = ((lean_object*)(l_Std_ExtHashSet_ofList___redArg___closed__11));
v___x_501_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1);
v___x_502_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_500_, v_inst_497_, v_inst_498_, v___x_501_, v_l_499_);
return v___x_502_;
}
}
uint8_t l_Std_ExtHashSet_filter___redArg___lam__0(lean_object* v_f_503_, lean_object* v_a_504_, lean_object* v_x_505_){
_start:
{
lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_506_ = lean_apply_1(v_f_503_, v_a_504_);
v___x_507_ = lean_unbox(v___x_506_);
return v___x_507_;
}
}
LEAN_EXPORT void l_Std_ExtHashSet_filter___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_503_ = stack[0].m_obj;
lean_object* v_a_504_ = stack[1].m_obj;
lean_object* v_x_505_ = stack[2].m_obj;
uint8_t v_res_508_;
v_res_508_ = l_Std_ExtHashSet_filter___redArg___lam__0(v_f_503_, v_a_504_, v_x_505_);
stack->m_num = v_res_508_;
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_filter___redArg___lam__0___boxed(lean_object* v_f_509_, lean_object* v_a_510_, lean_object* v_x_511_){
_start:
{
uint8_t v_res_512_; lean_object* v_r_513_; 
v_res_512_ = l_Std_ExtHashSet_filter___redArg___lam__0(v_f_509_, v_a_510_, v_x_511_);
v_r_513_ = lean_box(v_res_512_);
return v_r_513_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_filter___redArg(lean_object* v_f_514_, lean_object* v_m_515_){
_start:
{
lean_object* v___f_516_; lean_object* v___x_517_; 
v___f_516_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_516_, 0, v_f_514_);
v___x_517_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_516_, v_m_515_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_filter(lean_object* v_00_u03b1_518_, lean_object* v_x_519_, lean_object* v_x_520_, lean_object* v_inst_521_, lean_object* v_inst_522_, lean_object* v_f_523_, lean_object* v_m_524_){
_start:
{
lean_object* v___f_525_; lean_object* v___x_526_; 
v___f_525_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_525_, 0, v_f_523_);
v___x_526_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_525_, v_m_524_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_filter___boxed(lean_object* v_00_u03b1_527_, lean_object* v_x_528_, lean_object* v_x_529_, lean_object* v_inst_530_, lean_object* v_inst_531_, lean_object* v_f_532_, lean_object* v_m_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Std_ExtHashSet_filter(v_00_u03b1_527_, v_x_528_, v_x_529_, v_inst_530_, v_inst_531_, v_f_532_, v_m_533_);
lean_dec_ref(v_x_529_);
lean_dec_ref(v_x_528_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insertMany___redArg___lam__0(lean_object* v_x_535_, lean_object* v_x_536_, lean_object* v_a_537_, lean_object* v_____s_538_){
_start:
{
lean_object* v___x_539_; lean_object* v_m_540_; lean_object* v___x_541_; 
v___x_539_ = lean_box(0);
v_m_540_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_535_, v_x_536_, v_____s_538_, v_a_537_, v___x_539_);
v___x_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_541_, 0, v_m_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insertMany___redArg(lean_object* v_x_542_, lean_object* v_x_543_, lean_object* v_inst_544_, lean_object* v_m_545_, lean_object* v_l_546_){
_start:
{
lean_object* v___f_547_; lean_object* v___x_548_; 
v___f_547_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_547_, 0, v_x_542_);
lean_closure_set(v___f_547_, 1, v_x_543_);
v___x_548_ = lean_apply_4(v_inst_544_, lean_box(0), v_l_546_, v_m_545_, v___f_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insertMany(lean_object* v_00_u03b1_549_, lean_object* v_x_550_, lean_object* v_x_551_, lean_object* v_inst_552_, lean_object* v_inst_553_, lean_object* v_00_u03c1_554_, lean_object* v_inst_555_, lean_object* v_m_556_, lean_object* v_l_557_){
_start:
{
lean_object* v___f_558_; lean_object* v___x_559_; 
v___f_558_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_558_, 0, v_x_550_);
lean_closure_set(v___f_558_, 1, v_x_551_);
v___x_559_ = lean_apply_4(v_inst_555_, lean_box(0), v_l_557_, v_m_556_, v___f_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_union___redArg___lam__0(lean_object* v_x_560_, lean_object* v_x_561_, lean_object* v_a_562_, lean_object* v_b_563_, lean_object* v_acc_564_){
_start:
{
lean_object* v_r_565_; lean_object* v___x_566_; 
v_r_565_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_560_, v_x_561_, v_acc_564_, v_a_562_, v_b_563_);
v___x_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_566_, 0, v_r_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_union___redArg___lam__1(lean_object* v___x_567_, lean_object* v___f_568_, lean_object* v_a_569_, lean_object* v_x_570_, lean_object* v___y_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_567_, v___f_568_, v_a_569_, v___y_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_union___redArg(lean_object* v_x_575_, lean_object* v_x_576_, lean_object* v_m_u2081_577_, lean_object* v_m_u2082_578_){
_start:
{
lean_object* v___x_579_; lean_object* v_size_580_; lean_object* v_buckets_581_; lean_object* v_size_582_; uint8_t v___x_583_; 
v___x_579_ = ((lean_object*)(l_Std_ExtHashSet_ofList___redArg___closed__9));
v_size_580_ = lean_ctor_get(v_m_u2081_577_, 0);
v_buckets_581_ = lean_ctor_get(v_m_u2081_577_, 1);
v_size_582_ = lean_ctor_get(v_m_u2082_578_, 0);
v___x_583_ = lean_nat_dec_le(v_size_580_, v_size_582_);
if (v___x_583_ == 0)
{
lean_object* v___f_584_; lean_object* v___x_585_; 
v___f_584_ = ((lean_object*)(l_Std_ExtHashSet_union___redArg___closed__0));
v___x_585_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_584_, v_x_575_, v_x_576_, v_m_u2081_577_, v_m_u2082_578_);
return v___x_585_;
}
else
{
lean_object* v___f_586_; lean_object* v___f_587_; size_t v_sz_588_; size_t v___x_589_; lean_object* v___x_590_; 
lean_inc_ref(v_buckets_581_);
lean_dec(v_m_u2081_577_);
v___f_586_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_586_, 0, v_x_575_);
lean_closure_set(v___f_586_, 1, v_x_576_);
v___f_587_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_587_, 0, v___x_579_);
lean_closure_set(v___f_587_, 1, v___f_586_);
v_sz_588_ = lean_array_size(v_buckets_581_);
v___x_589_ = ((size_t)0ULL);
v___x_590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_579_, v_buckets_581_, v___f_587_, v_sz_588_, v___x_589_, v_m_u2082_578_);
return v___x_590_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_union(lean_object* v_00_u03b1_591_, lean_object* v_x_592_, lean_object* v_x_593_, lean_object* v_inst_594_, lean_object* v_inst_595_, lean_object* v_m_u2081_596_, lean_object* v_m_u2082_597_){
_start:
{
lean_object* v___x_598_; lean_object* v_size_599_; lean_object* v_buckets_600_; lean_object* v_size_601_; uint8_t v___x_602_; 
v___x_598_ = ((lean_object*)(l_Std_ExtHashSet_ofList___redArg___closed__9));
v_size_599_ = lean_ctor_get(v_m_u2081_596_, 0);
v_buckets_600_ = lean_ctor_get(v_m_u2081_596_, 1);
v_size_601_ = lean_ctor_get(v_m_u2082_597_, 0);
v___x_602_ = lean_nat_dec_le(v_size_599_, v_size_601_);
if (v___x_602_ == 0)
{
lean_object* v___f_603_; lean_object* v___x_604_; 
v___f_603_ = ((lean_object*)(l_Std_ExtHashSet_union___redArg___closed__0));
v___x_604_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_603_, v_x_592_, v_x_593_, v_m_u2081_596_, v_m_u2082_597_);
return v___x_604_;
}
else
{
lean_object* v___f_605_; lean_object* v___f_606_; size_t v_sz_607_; size_t v___x_608_; lean_object* v___x_609_; 
lean_inc_ref(v_buckets_600_);
lean_dec(v_m_u2081_596_);
v___f_605_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_605_, 0, v_x_592_);
lean_closure_set(v___f_605_, 1, v_x_593_);
v___f_606_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_606_, 0, v___x_598_);
lean_closure_set(v___f_606_, 1, v___f_605_);
v_sz_607_ = lean_array_size(v_buckets_600_);
v___x_608_ = ((size_t)0ULL);
v___x_609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_598_, v_buckets_600_, v___f_606_, v_sz_607_, v___x_608_, v_m_u2082_597_);
return v___x_609_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instUnionOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_610_, lean_object* v_x_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_union), 7, 5);
lean_closure_set(v___x_612_, 0, lean_box(0));
lean_closure_set(v___x_612_, 1, v_x_610_);
lean_closure_set(v___x_612_, 2, v_x_611_);
lean_closure_set(v___x_612_, 3, lean_box(0));
lean_closure_set(v___x_612_, 4, lean_box(0));
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instUnionOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_613_, lean_object* v_x_614_, lean_object* v_x_615_, lean_object* v_inst_616_, lean_object* v_inst_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_union), 7, 5);
lean_closure_set(v___x_618_, 0, lean_box(0));
lean_closure_set(v___x_618_, 1, v_x_614_);
lean_closure_set(v___x_618_, 2, v_x_615_);
lean_closure_set(v___x_618_, 3, lean_box(0));
lean_closure_set(v___x_618_, 4, lean_box(0));
return v___x_618_;
}
}
static lean_object* _init_l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_619_; lean_object* v___f_620_; 
v___x_619_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_620_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_620_, 0, v___x_619_);
return v___f_620_;
}
}
uint8_t l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_621_, lean_object* v_x_622_, lean_object* v_m_u2081_623_, lean_object* v_m_u2082_624_){
_start:
{
lean_object* v___f_625_; uint8_t v___x_626_; 
v___f_625_ = lean_obj_once(&l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0, &l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0_once, _init_l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0);
v___x_626_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_x_621_, v_x_622_, v___f_625_, v_m_u2081_623_, v_m_u2082_624_);
return v___x_626_;
}
}
LEAN_EXPORT void l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_621_ = stack[0].m_obj;
lean_object* v_x_622_ = stack[1].m_obj;
lean_object* v_m_u2081_623_ = stack[2].m_obj;
lean_object* v_m_u2082_624_ = stack[3].m_obj;
uint8_t v_res_627_;
v_res_627_ = l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0(v_x_621_, v_x_622_, v_m_u2081_623_, v_m_u2082_624_);
stack->m_num = v_res_627_;
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed(lean_object* v_x_628_, lean_object* v_x_629_, lean_object* v_m_u2081_630_, lean_object* v_m_u2082_631_){
_start:
{
uint8_t v_res_632_; lean_object* v_r_633_; 
v_res_632_ = l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0(v_x_628_, v_x_629_, v_m_u2081_630_, v_m_u2082_631_);
v_r_633_ = lean_box(v_res_632_);
return v_r_633_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_634_, lean_object* v_x_635_){
_start:
{
lean_object* v___f_636_; 
v___f_636_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_636_, 0, v_x_634_);
lean_closure_set(v___f_636_, 1, v_x_635_);
return v___f_636_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_637_, lean_object* v_x_638_, lean_object* v_x_639_, lean_object* v_inst_640_, lean_object* v_inst_641_){
_start:
{
lean_object* v___f_642_; 
v___f_642_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_642_, 0, v_x_638_);
lean_closure_set(v___f_642_, 1, v_x_639_);
return v___f_642_;
}
}
uint8_t l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___redArg(lean_object* v_inst_643_, lean_object* v_inst_644_, lean_object* v_x_645_, lean_object* v_x_646_){
_start:
{
lean_object* v___f_647_; uint8_t v___x_648_; 
v___f_647_ = lean_obj_once(&l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0, &l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0_once, _init_l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0);
v___x_648_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_643_, v_inst_644_, v___f_647_, v_x_645_, v_x_646_);
return v___x_648_;
}
}
LEAN_EXPORT void l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_643_ = stack[0].m_obj;
lean_object* v_inst_644_ = stack[1].m_obj;
lean_object* v_x_645_ = stack[2].m_obj;
lean_object* v_x_646_ = stack[3].m_obj;
uint8_t v_res_649_;
v_res_649_ = l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___redArg(v_inst_643_, v_inst_644_, v_x_645_, v_x_646_);
stack->m_num = v_res_649_;
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___redArg___boxed(lean_object* v_inst_650_, lean_object* v_inst_651_, lean_object* v_x_652_, lean_object* v_x_653_){
_start:
{
uint8_t v_res_654_; lean_object* v_r_655_; 
v_res_654_ = l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___redArg(v_inst_650_, v_inst_651_, v_x_652_, v_x_653_);
v_r_655_ = lean_box(v_res_654_);
return v_r_655_;
}
}
uint8_t l_Std_ExtHashSet_instDecidableEqOfLawfulBEq(lean_object* v_00_u03b1_656_, lean_object* v_inst_657_, lean_object* v_inst_658_, lean_object* v_inst_659_, lean_object* v_x_660_, lean_object* v_x_661_){
_start:
{
uint8_t v___x_662_; 
v___x_662_ = l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___redArg(v_inst_657_, v_inst_659_, v_x_660_, v_x_661_);
return v___x_662_;
}
}
LEAN_EXPORT void l_Std_ExtHashSet_instDecidableEqOfLawfulBEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_657_ = stack[1].m_obj;
lean_object* v_inst_659_ = stack[3].m_obj;
lean_object* v_x_660_ = stack[4].m_obj;
lean_object* v_x_661_ = stack[5].m_obj;
uint8_t v_res_663_;
v_res_663_ = l_Std_ExtHashSet_instDecidableEqOfLawfulBEq(lean_box(0), v_inst_657_, lean_box(0), v_inst_659_, v_x_660_, v_x_661_);
stack->m_num = v_res_663_;
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___boxed(lean_object* v_00_u03b1_664_, lean_object* v_inst_665_, lean_object* v_inst_666_, lean_object* v_inst_667_, lean_object* v_x_668_, lean_object* v_x_669_){
_start:
{
uint8_t v_res_670_; lean_object* v_r_671_; 
v_res_670_ = l_Std_ExtHashSet_instDecidableEqOfLawfulBEq(v_00_u03b1_664_, v_inst_665_, v_inst_666_, v_inst_667_, v_x_668_, v_x_669_);
v_r_671_ = lean_box(v_res_670_);
return v_r_671_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_inter___redArg(lean_object* v_x_672_, lean_object* v_x_673_, lean_object* v_m_u2081_674_, lean_object* v_m_u2082_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_x_672_, v_x_673_, v_m_u2081_674_, v_m_u2082_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_inter(lean_object* v_00_u03b1_677_, lean_object* v_x_678_, lean_object* v_x_679_, lean_object* v_inst_680_, lean_object* v_inst_681_, lean_object* v_m_u2081_682_, lean_object* v_m_u2082_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_x_678_, v_x_679_, v_m_u2081_682_, v_m_u2082_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInterOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_685_, lean_object* v_x_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_inter), 7, 5);
lean_closure_set(v___x_687_, 0, lean_box(0));
lean_closure_set(v___x_687_, 1, v_x_685_);
lean_closure_set(v___x_687_, 2, v_x_686_);
lean_closure_set(v___x_687_, 3, lean_box(0));
lean_closure_set(v___x_687_, 4, lean_box(0));
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInterOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_688_, lean_object* v_x_689_, lean_object* v_x_690_, lean_object* v_inst_691_, lean_object* v_inst_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_inter), 7, 5);
lean_closure_set(v___x_693_, 0, lean_box(0));
lean_closure_set(v___x_693_, 1, v_x_689_);
lean_closure_set(v___x_693_, 2, v_x_690_);
lean_closure_set(v___x_693_, 3, lean_box(0));
lean_closure_set(v___x_693_, 4, lean_box(0));
return v___x_693_;
}
}
uint8_t l_Std_ExtHashSet_diff___redArg___lam__0(lean_object* v_x_694_, lean_object* v_x_695_, lean_object* v_m_u2082_696_, uint8_t v___x_697_, lean_object* v_k_698_, lean_object* v_x_699_){
_start:
{
uint8_t v___x_700_; 
v___x_700_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_694_, v_x_695_, v_m_u2082_696_, v_k_698_);
if (v___x_700_ == 0)
{
return v___x_697_;
}
else
{
uint8_t v___x_701_; 
v___x_701_ = 0;
return v___x_701_;
}
}
}
LEAN_EXPORT void l_Std_ExtHashSet_diff___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_694_ = stack[0].m_obj;
lean_object* v_x_695_ = stack[1].m_obj;
lean_object* v_m_u2082_696_ = stack[2].m_obj;
uint8_t v___x_697_ = stack[3].m_num;
lean_object* v_k_698_ = stack[4].m_obj;
lean_object* v_x_699_ = stack[5].m_obj;
uint8_t v_res_702_;
v_res_702_ = l_Std_ExtHashSet_diff___redArg___lam__0(v_x_694_, v_x_695_, v_m_u2082_696_, v___x_697_, v_k_698_, v_x_699_);
stack->m_num = v_res_702_;
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_diff___redArg___lam__0___boxed(lean_object* v_x_703_, lean_object* v_x_704_, lean_object* v_m_u2082_705_, lean_object* v___x_706_, lean_object* v_k_707_, lean_object* v_x_708_){
_start:
{
uint8_t v___x_110__boxed_709_; uint8_t v_res_710_; lean_object* v_r_711_; 
v___x_110__boxed_709_ = lean_unbox(v___x_706_);
v_res_710_ = l_Std_ExtHashSet_diff___redArg___lam__0(v_x_703_, v_x_704_, v_m_u2082_705_, v___x_110__boxed_709_, v_k_707_, v_x_708_);
lean_dec(v_m_u2082_705_);
v_r_711_ = lean_box(v_res_710_);
return v_r_711_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_diff___redArg(lean_object* v_x_712_, lean_object* v_x_713_, lean_object* v_m_u2081_714_, lean_object* v_m_u2082_715_){
_start:
{
lean_object* v_size_716_; lean_object* v_size_717_; uint8_t v___x_718_; 
v_size_716_ = lean_ctor_get(v_m_u2081_714_, 0);
v_size_717_ = lean_ctor_get(v_m_u2082_715_, 0);
v___x_718_ = lean_nat_dec_le(v_size_716_, v_size_717_);
if (v___x_718_ == 0)
{
lean_object* v___f_719_; lean_object* v___x_720_; 
v___f_719_ = ((lean_object*)(l_Std_ExtHashSet_union___redArg___closed__0));
v___x_720_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_719_, v_x_712_, v_x_713_, v_m_u2081_714_, v_m_u2082_715_);
return v___x_720_;
}
else
{
lean_object* v___x_721_; lean_object* v___f_722_; lean_object* v___x_723_; 
v___x_721_ = lean_box(v___x_718_);
v___f_722_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_722_, 0, v_x_712_);
lean_closure_set(v___f_722_, 1, v_x_713_);
lean_closure_set(v___f_722_, 2, v_m_u2082_715_);
lean_closure_set(v___f_722_, 3, v___x_721_);
v___x_723_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_722_, v_m_u2081_714_);
return v___x_723_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_diff(lean_object* v_00_u03b1_724_, lean_object* v_x_725_, lean_object* v_x_726_, lean_object* v_inst_727_, lean_object* v_inst_728_, lean_object* v_m_u2081_729_, lean_object* v_m_u2082_730_){
_start:
{
lean_object* v_size_731_; lean_object* v_size_732_; uint8_t v___x_733_; 
v_size_731_ = lean_ctor_get(v_m_u2081_729_, 0);
v_size_732_ = lean_ctor_get(v_m_u2082_730_, 0);
v___x_733_ = lean_nat_dec_le(v_size_731_, v_size_732_);
if (v___x_733_ == 0)
{
lean_object* v___f_734_; lean_object* v___x_735_; 
v___f_734_ = ((lean_object*)(l_Std_ExtHashSet_union___redArg___closed__0));
v___x_735_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_734_, v_x_725_, v_x_726_, v_m_u2081_729_, v_m_u2082_730_);
return v___x_735_;
}
else
{
lean_object* v___x_736_; lean_object* v___f_737_; lean_object* v___x_738_; 
v___x_736_ = lean_box(v___x_733_);
v___f_737_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_737_, 0, v_x_725_);
lean_closure_set(v___f_737_, 1, v_x_726_);
lean_closure_set(v___f_737_, 2, v_m_u2082_730_);
lean_closure_set(v___f_737_, 3, v___x_736_);
v___x_738_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_737_, v_m_u2081_729_);
return v___x_738_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instSDiffOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_739_, lean_object* v_x_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_diff), 7, 5);
lean_closure_set(v___x_741_, 0, lean_box(0));
lean_closure_set(v___x_741_, 1, v_x_739_);
lean_closure_set(v___x_741_, 2, v_x_740_);
lean_closure_set(v___x_741_, 3, lean_box(0));
lean_closure_set(v___x_741_, 4, lean_box(0));
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instSDiffOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_742_, lean_object* v_x_743_, lean_object* v_x_744_, lean_object* v_inst_745_, lean_object* v_inst_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_diff), 7, 5);
lean_closure_set(v___x_747_, 0, lean_box(0));
lean_closure_set(v___x_747_, 1, v_x_743_);
lean_closure_set(v___x_747_, 2, v_x_744_);
lean_closure_set(v___x_747_, 3, lean_box(0));
lean_closure_set(v___x_747_, 4, lean_box(0));
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_ofArray___redArg(lean_object* v_inst_752_, lean_object* v_inst_753_, lean_object* v_l_754_){
_start:
{
lean_object* v___f_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___f_755_ = ((lean_object*)(l_Std_ExtHashSet_ofArray___redArg___closed__1));
v___x_756_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1);
v___x_757_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_755_, v_inst_752_, v_inst_753_, v___x_756_, v_l_754_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_ofArray(lean_object* v_00_u03b1_758_, lean_object* v_inst_759_, lean_object* v_inst_760_, lean_object* v_l_761_){
_start:
{
lean_object* v___f_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___f_762_ = ((lean_object*)(l_Std_ExtHashSet_ofArray___redArg___closed__1));
v___x_763_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1);
v___x_764_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_762_, v_inst_759_, v_inst_760_, v___x_763_, v_l_761_);
return v___x_764_;
}
}
lean_object* runtime_initialize_Std_Data_ExtHashMap_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_ExtHashSet_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_ExtHashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_ExtHashSet_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_ExtHashMap_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_ExtHashSet_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_ExtHashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_ExtHashSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_ExtHashSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_ExtHashSet_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
