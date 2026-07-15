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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_ExtHashSet_instEmptyCollection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtHashSet_instEmptyCollection___closed__0;
static lean_once_cell_t l_Std_ExtHashSet_instEmptyCollection___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_ExtHashSet_instEmptyCollection___closed__1;
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instEmptyCollection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Std_ExtHashSet_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_31_ = lean_box(0);
v___x_32_ = lean_unsigned_to_nat(16u);
v___x_33_ = lean_mk_array(v___x_32_, v___x_31_);
return v___x_33_;
}
}
static lean_object* _init_l_Std_ExtHashSet_instEmptyCollection___closed__1(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___closed__0, &l_Std_ExtHashSet_instEmptyCollection___closed__0_once, _init_l_Std_ExtHashSet_instEmptyCollection___closed__0);
v___x_35_ = lean_unsigned_to_nat(0u);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
lean_ctor_set(v___x_36_, 1, v___x_34_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instEmptyCollection(lean_object* v_00_u03b1_37_, lean_object* v_inst_38_, lean_object* v_inst_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___closed__1, &l_Std_ExtHashSet_instEmptyCollection___closed__1_once, _init_l_Std_ExtHashSet_instEmptyCollection___closed__1);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instEmptyCollection___boxed(lean_object* v_00_u03b1_41_, lean_object* v_inst_42_, lean_object* v_inst_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Std_ExtHashSet_instEmptyCollection(v_00_u03b1_41_, v_inst_42_, v_inst_43_);
lean_dec_ref(v_inst_43_);
lean_dec_ref(v_inst_42_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInhabited(lean_object* v_00_u03b1_45_, lean_object* v_inst_46_, lean_object* v_inst_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___closed__1, &l_Std_ExtHashSet_instEmptyCollection___closed__1_once, _init_l_Std_ExtHashSet_instEmptyCollection___closed__1);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInhabited___boxed(lean_object* v_00_u03b1_49_, lean_object* v_inst_50_, lean_object* v_inst_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Std_ExtHashSet_instInhabited(v_00_u03b1_49_, v_inst_50_, v_inst_51_);
lean_dec_ref(v_inst_51_);
lean_dec_ref(v_inst_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insert___redArg(lean_object* v_x_53_, lean_object* v_x_54_, lean_object* v_m_55_, lean_object* v_a_56_){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = lean_box(0);
v___x_58_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_53_, v_x_54_, v_m_55_, v_a_56_, v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insert(lean_object* v_00_u03b1_59_, lean_object* v_x_60_, lean_object* v_x_61_, lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_m_64_, lean_object* v_a_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = lean_box(0);
v___x_67_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_60_, v_x_61_, v_m_64_, v_a_65_, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_68_, lean_object* v_x_69_, lean_object* v_a_70_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_71_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___closed__1, &l_Std_ExtHashSet_instEmptyCollection___closed__1_once, _init_l_Std_ExtHashSet_instEmptyCollection___closed__1);
v___x_72_ = lean_box(0);
v___x_73_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_68_, v_x_69_, v___x_71_, v_a_70_, v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_74_, lean_object* v_x_75_){
_start:
{
lean_object* v___f_76_; 
v___f_76_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_76_, 0, v_x_74_);
lean_closure_set(v___f_76_, 1, v_x_75_);
return v___f_76_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_77_, lean_object* v_x_78_, lean_object* v_x_79_, lean_object* v_inst_80_, lean_object* v_inst_81_){
_start:
{
lean_object* v___f_82_; 
v___f_82_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_82_, 0, v_x_78_);
lean_closure_set(v___f_82_, 1, v_x_79_);
return v___f_82_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInsertOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_83_, lean_object* v_x_84_, lean_object* v_a_85_, lean_object* v_s_86_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_box(0);
v___x_88_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_83_, v_x_84_, v_s_86_, v_a_85_, v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInsertOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_89_, lean_object* v_x_90_){
_start:
{
lean_object* v___f_91_; 
v___f_91_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_instInsertOfEquivBEqOfLawfulHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_91_, 0, v_x_89_);
lean_closure_set(v___f_91_, 1, v_x_90_);
return v___f_91_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInsertOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_92_, lean_object* v_x_93_, lean_object* v_x_94_, lean_object* v_inst_95_, lean_object* v_inst_96_){
_start:
{
lean_object* v___f_97_; 
v___f_97_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_instInsertOfEquivBEqOfLawfulHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_97_, 0, v_x_93_);
lean_closure_set(v___f_97_, 1, v_x_94_);
return v___f_97_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_containsThenInsert___redArg(lean_object* v_x_98_, lean_object* v_x_99_, lean_object* v_m_100_, lean_object* v_a_101_){
_start:
{
lean_object* v_size_102_; lean_object* v_buckets_103_; lean_object* v___x_104_; lean_object* v___x_105_; uint64_t v___x_106_; uint64_t v___x_107_; uint64_t v___x_108_; uint64_t v___x_109_; uint64_t v_fold_110_; uint64_t v___x_111_; uint64_t v___x_112_; uint64_t v___x_113_; size_t v___x_114_; size_t v___x_115_; size_t v___x_116_; size_t v___x_117_; size_t v___x_118_; lean_object* v_bkt_119_; uint8_t v___x_120_; 
v_size_102_ = lean_ctor_get(v_m_100_, 0);
v_buckets_103_ = lean_ctor_get(v_m_100_, 1);
v___x_104_ = lean_array_get_size(v_buckets_103_);
lean_inc_ref(v_x_99_);
lean_inc_n(v_a_101_, 2);
v___x_105_ = lean_apply_1(v_x_99_, v_a_101_);
v___x_106_ = 32ULL;
v___x_107_ = lean_unbox_uint64(v___x_105_);
v___x_108_ = lean_uint64_shift_right(v___x_107_, v___x_106_);
v___x_109_ = lean_unbox_uint64(v___x_105_);
lean_dec_ref(v___x_105_);
v_fold_110_ = lean_uint64_xor(v___x_109_, v___x_108_);
v___x_111_ = 16ULL;
v___x_112_ = lean_uint64_shift_right(v_fold_110_, v___x_111_);
v___x_113_ = lean_uint64_xor(v_fold_110_, v___x_112_);
v___x_114_ = lean_uint64_to_usize(v___x_113_);
v___x_115_ = lean_usize_of_nat(v___x_104_);
v___x_116_ = ((size_t)1ULL);
v___x_117_ = lean_usize_sub(v___x_115_, v___x_116_);
v___x_118_ = lean_usize_land(v___x_114_, v___x_117_);
v_bkt_119_ = lean_array_uget_borrowed(v_buckets_103_, v___x_118_);
lean_inc(v_bkt_119_);
v___x_120_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_98_, v_a_101_, v_bkt_119_);
if (v___x_120_ == 0)
{
lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_146_; 
lean_inc_ref(v_buckets_103_);
lean_inc(v_size_102_);
v_isSharedCheck_146_ = !lean_is_exclusive(v_m_100_);
if (v_isSharedCheck_146_ == 0)
{
lean_object* v_unused_147_; lean_object* v_unused_148_; 
v_unused_147_ = lean_ctor_get(v_m_100_, 1);
lean_dec(v_unused_147_);
v_unused_148_ = lean_ctor_get(v_m_100_, 0);
lean_dec(v_unused_148_);
v___x_122_ = v_m_100_;
v_isShared_123_ = v_isSharedCheck_146_;
goto v_resetjp_121_;
}
else
{
lean_dec(v_m_100_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_146_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v_size_x27_126_; lean_object* v___x_127_; lean_object* v_buckets_x27_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_124_ = lean_box(0);
v___x_125_ = lean_unsigned_to_nat(1u);
v_size_x27_126_ = lean_nat_add(v_size_102_, v___x_125_);
lean_dec(v_size_102_);
lean_inc(v_bkt_119_);
v___x_127_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_127_, 0, v_a_101_);
lean_ctor_set(v___x_127_, 1, v___x_124_);
lean_ctor_set(v___x_127_, 2, v_bkt_119_);
v_buckets_x27_128_ = lean_array_uset(v_buckets_103_, v___x_118_, v___x_127_);
v___x_129_ = lean_unsigned_to_nat(4u);
v___x_130_ = lean_nat_mul(v_size_x27_126_, v___x_129_);
v___x_131_ = lean_unsigned_to_nat(3u);
v___x_132_ = lean_nat_div(v___x_130_, v___x_131_);
lean_dec(v___x_130_);
v___x_133_ = lean_array_get_size(v_buckets_x27_128_);
v___x_134_ = lean_nat_dec_le(v___x_132_, v___x_133_);
lean_dec(v___x_132_);
if (v___x_134_ == 0)
{
lean_object* v_val_135_; lean_object* v___x_137_; 
v_val_135_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_99_, v_buckets_x27_128_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v_val_135_);
lean_ctor_set(v___x_122_, 0, v_size_x27_126_);
v___x_137_ = v___x_122_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_size_x27_126_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v_val_135_);
v___x_137_ = v_reuseFailAlloc_140_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_box(v___x_120_);
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v___x_137_);
return v___x_139_;
}
}
else
{
lean_object* v___x_142_; 
lean_dec_ref(v_x_99_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v_buckets_x27_128_);
lean_ctor_set(v___x_122_, 0, v_size_x27_126_);
v___x_142_ = v___x_122_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_size_x27_126_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v_buckets_x27_128_);
v___x_142_ = v_reuseFailAlloc_145_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = lean_box(v___x_120_);
v___x_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v___x_142_);
return v___x_144_;
}
}
}
}
else
{
lean_object* v___x_149_; lean_object* v___x_150_; 
lean_dec(v_a_101_);
lean_dec_ref(v_x_99_);
v___x_149_ = lean_box(v___x_120_);
v___x_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v_m_100_);
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_containsThenInsert(lean_object* v_00_u03b1_151_, lean_object* v_x_152_, lean_object* v_x_153_, lean_object* v_inst_154_, lean_object* v_inst_155_, lean_object* v_m_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_size_158_; lean_object* v_buckets_159_; lean_object* v___x_160_; lean_object* v___x_161_; uint64_t v___x_162_; uint64_t v___x_163_; uint64_t v___x_164_; uint64_t v___x_165_; uint64_t v_fold_166_; uint64_t v___x_167_; uint64_t v___x_168_; uint64_t v___x_169_; size_t v___x_170_; size_t v___x_171_; size_t v___x_172_; size_t v___x_173_; size_t v___x_174_; lean_object* v_bkt_175_; uint8_t v___x_176_; 
v_size_158_ = lean_ctor_get(v_m_156_, 0);
v_buckets_159_ = lean_ctor_get(v_m_156_, 1);
v___x_160_ = lean_array_get_size(v_buckets_159_);
lean_inc_ref(v_x_153_);
lean_inc_n(v_a_157_, 2);
v___x_161_ = lean_apply_1(v_x_153_, v_a_157_);
v___x_162_ = 32ULL;
v___x_163_ = lean_unbox_uint64(v___x_161_);
v___x_164_ = lean_uint64_shift_right(v___x_163_, v___x_162_);
v___x_165_ = lean_unbox_uint64(v___x_161_);
lean_dec_ref(v___x_161_);
v_fold_166_ = lean_uint64_xor(v___x_165_, v___x_164_);
v___x_167_ = 16ULL;
v___x_168_ = lean_uint64_shift_right(v_fold_166_, v___x_167_);
v___x_169_ = lean_uint64_xor(v_fold_166_, v___x_168_);
v___x_170_ = lean_uint64_to_usize(v___x_169_);
v___x_171_ = lean_usize_of_nat(v___x_160_);
v___x_172_ = ((size_t)1ULL);
v___x_173_ = lean_usize_sub(v___x_171_, v___x_172_);
v___x_174_ = lean_usize_land(v___x_170_, v___x_173_);
v_bkt_175_ = lean_array_uget_borrowed(v_buckets_159_, v___x_174_);
lean_inc(v_bkt_175_);
v___x_176_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_152_, v_a_157_, v_bkt_175_);
if (v___x_176_ == 0)
{
lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_202_; 
lean_inc_ref(v_buckets_159_);
lean_inc(v_size_158_);
v_isSharedCheck_202_ = !lean_is_exclusive(v_m_156_);
if (v_isSharedCheck_202_ == 0)
{
lean_object* v_unused_203_; lean_object* v_unused_204_; 
v_unused_203_ = lean_ctor_get(v_m_156_, 1);
lean_dec(v_unused_203_);
v_unused_204_ = lean_ctor_get(v_m_156_, 0);
lean_dec(v_unused_204_);
v___x_178_ = v_m_156_;
v_isShared_179_ = v_isSharedCheck_202_;
goto v_resetjp_177_;
}
else
{
lean_dec(v_m_156_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_202_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v_size_x27_182_; lean_object* v___x_183_; lean_object* v_buckets_x27_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_180_ = lean_box(0);
v___x_181_ = lean_unsigned_to_nat(1u);
v_size_x27_182_ = lean_nat_add(v_size_158_, v___x_181_);
lean_dec(v_size_158_);
lean_inc(v_bkt_175_);
v___x_183_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_183_, 0, v_a_157_);
lean_ctor_set(v___x_183_, 1, v___x_180_);
lean_ctor_set(v___x_183_, 2, v_bkt_175_);
v_buckets_x27_184_ = lean_array_uset(v_buckets_159_, v___x_174_, v___x_183_);
v___x_185_ = lean_unsigned_to_nat(4u);
v___x_186_ = lean_nat_mul(v_size_x27_182_, v___x_185_);
v___x_187_ = lean_unsigned_to_nat(3u);
v___x_188_ = lean_nat_div(v___x_186_, v___x_187_);
lean_dec(v___x_186_);
v___x_189_ = lean_array_get_size(v_buckets_x27_184_);
v___x_190_ = lean_nat_dec_le(v___x_188_, v___x_189_);
lean_dec(v___x_188_);
if (v___x_190_ == 0)
{
lean_object* v_val_191_; lean_object* v___x_193_; 
v_val_191_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_153_, v_buckets_x27_184_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v_val_191_);
lean_ctor_set(v___x_178_, 0, v_size_x27_182_);
v___x_193_ = v___x_178_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_size_x27_182_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_val_191_);
v___x_193_ = v_reuseFailAlloc_196_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_box(v___x_176_);
v___x_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v___x_193_);
return v___x_195_;
}
}
else
{
lean_object* v___x_198_; 
lean_dec_ref(v_x_153_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v_buckets_x27_184_);
lean_ctor_set(v___x_178_, 0, v_size_x27_182_);
v___x_198_ = v___x_178_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_size_x27_182_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_buckets_x27_184_);
v___x_198_ = v_reuseFailAlloc_201_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_box(v___x_176_);
v___x_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v___x_198_);
return v___x_200_;
}
}
}
}
else
{
lean_object* v___x_205_; lean_object* v___x_206_; 
lean_dec(v_a_157_);
lean_dec_ref(v_x_153_);
v___x_205_ = lean_box(v___x_176_);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v_m_156_);
return v___x_206_;
}
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_contains___redArg(lean_object* v_x_207_, lean_object* v_x_208_, lean_object* v_m_209_, lean_object* v_a_210_){
_start:
{
uint8_t v___x_211_; 
v___x_211_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_207_, v_x_208_, v_m_209_, v_a_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_contains___redArg___boxed(lean_object* v_x_212_, lean_object* v_x_213_, lean_object* v_m_214_, lean_object* v_a_215_){
_start:
{
uint8_t v_res_216_; lean_object* v_r_217_; 
v_res_216_ = l_Std_ExtHashSet_contains___redArg(v_x_212_, v_x_213_, v_m_214_, v_a_215_);
lean_dec(v_m_214_);
v_r_217_ = lean_box(v_res_216_);
return v_r_217_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_contains(lean_object* v_00_u03b1_218_, lean_object* v_x_219_, lean_object* v_x_220_, lean_object* v_inst_221_, lean_object* v_inst_222_, lean_object* v_m_223_, lean_object* v_a_224_){
_start:
{
uint8_t v___x_225_; 
v___x_225_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_219_, v_x_220_, v_m_223_, v_a_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_contains___boxed(lean_object* v_00_u03b1_226_, lean_object* v_x_227_, lean_object* v_x_228_, lean_object* v_inst_229_, lean_object* v_inst_230_, lean_object* v_m_231_, lean_object* v_a_232_){
_start:
{
uint8_t v_res_233_; lean_object* v_r_234_; 
v_res_233_ = l_Std_ExtHashSet_contains(v_00_u03b1_226_, v_x_227_, v_x_228_, v_inst_229_, v_inst_230_, v_m_231_, v_a_232_);
lean_dec(v_m_231_);
v_r_234_ = lean_box(v_res_233_);
return v_r_234_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instMembershipOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_235_, lean_object* v_inst_236_, lean_object* v_inst_237_, lean_object* v_inst_238_, lean_object* v_inst_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = lean_box(0);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instMembershipOfEquivBEqOfLawfulHashable___boxed(lean_object* v_00_u03b1_241_, lean_object* v_inst_242_, lean_object* v_inst_243_, lean_object* v_inst_244_, lean_object* v_inst_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Std_ExtHashSet_instMembershipOfEquivBEqOfLawfulHashable(v_00_u03b1_241_, v_inst_242_, v_inst_243_, v_inst_244_, v_inst_245_);
lean_dec_ref(v_inst_243_);
lean_dec_ref(v_inst_242_);
return v_res_246_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_instDecidableMem___redArg(lean_object* v_inst_247_, lean_object* v_inst_248_, lean_object* v_m_249_, lean_object* v_a_250_){
_start:
{
uint8_t v___x_251_; 
v___x_251_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_247_, v_inst_248_, v_m_249_, v_a_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instDecidableMem___redArg___boxed(lean_object* v_inst_252_, lean_object* v_inst_253_, lean_object* v_m_254_, lean_object* v_a_255_){
_start:
{
uint8_t v_res_256_; lean_object* v_r_257_; 
v_res_256_ = l_Std_ExtHashSet_instDecidableMem___redArg(v_inst_252_, v_inst_253_, v_m_254_, v_a_255_);
lean_dec(v_m_254_);
v_r_257_ = lean_box(v_res_256_);
return v_r_257_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_instDecidableMem(lean_object* v_00_u03b1_258_, lean_object* v_inst_259_, lean_object* v_inst_260_, lean_object* v_inst_261_, lean_object* v_inst_262_, lean_object* v_m_263_, lean_object* v_a_264_){
_start:
{
uint8_t v___x_265_; 
v___x_265_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_259_, v_inst_260_, v_m_263_, v_a_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instDecidableMem___boxed(lean_object* v_00_u03b1_266_, lean_object* v_inst_267_, lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_inst_270_, lean_object* v_m_271_, lean_object* v_a_272_){
_start:
{
uint8_t v_res_273_; lean_object* v_r_274_; 
v_res_273_ = l_Std_ExtHashSet_instDecidableMem(v_00_u03b1_266_, v_inst_267_, v_inst_268_, v_inst_269_, v_inst_270_, v_m_271_, v_a_272_);
lean_dec(v_m_271_);
v_r_274_ = lean_box(v_res_273_);
return v_r_274_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_erase___redArg(lean_object* v_x_275_, lean_object* v_x_276_, lean_object* v_m_277_, lean_object* v_a_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_275_, v_x_276_, v_m_277_, v_a_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_erase(lean_object* v_00_u03b1_280_, lean_object* v_x_281_, lean_object* v_x_282_, lean_object* v_inst_283_, lean_object* v_inst_284_, lean_object* v_m_285_, lean_object* v_a_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_281_, v_x_282_, v_m_285_, v_a_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_size___redArg(lean_object* v_m_288_){
_start:
{
lean_object* v_size_289_; 
v_size_289_ = lean_ctor_get(v_m_288_, 0);
lean_inc(v_size_289_);
return v_size_289_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_size___redArg___boxed(lean_object* v_m_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Std_ExtHashSet_size___redArg(v_m_290_);
lean_dec(v_m_290_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_size(lean_object* v_00_u03b1_292_, lean_object* v_x_293_, lean_object* v_x_294_, lean_object* v_inst_295_, lean_object* v_inst_296_, lean_object* v_m_297_){
_start:
{
lean_object* v_size_298_; 
v_size_298_ = lean_ctor_get(v_m_297_, 0);
lean_inc(v_size_298_);
return v_size_298_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_size___boxed(lean_object* v_00_u03b1_299_, lean_object* v_x_300_, lean_object* v_x_301_, lean_object* v_inst_302_, lean_object* v_inst_303_, lean_object* v_m_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Std_ExtHashSet_size(v_00_u03b1_299_, v_x_300_, v_x_301_, v_inst_302_, v_inst_303_, v_m_304_);
lean_dec(v_m_304_);
lean_dec_ref(v_x_301_);
lean_dec_ref(v_x_300_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x3f___redArg(lean_object* v_x_306_, lean_object* v_x_307_, lean_object* v_m_308_, lean_object* v_a_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_306_, v_x_307_, v_m_308_, v_a_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x3f___redArg___boxed(lean_object* v_x_311_, lean_object* v_x_312_, lean_object* v_m_313_, lean_object* v_a_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Std_ExtHashSet_get_x3f___redArg(v_x_311_, v_x_312_, v_m_313_, v_a_314_);
lean_dec(v_m_313_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x3f(lean_object* v_00_u03b1_316_, lean_object* v_x_317_, lean_object* v_x_318_, lean_object* v_inst_319_, lean_object* v_inst_320_, lean_object* v_m_321_, lean_object* v_a_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_317_, v_x_318_, v_m_321_, v_a_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x3f___boxed(lean_object* v_00_u03b1_324_, lean_object* v_x_325_, lean_object* v_x_326_, lean_object* v_inst_327_, lean_object* v_inst_328_, lean_object* v_m_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_ExtHashSet_get_x3f(v_00_u03b1_324_, v_x_325_, v_x_326_, v_inst_327_, v_inst_328_, v_m_329_, v_a_330_);
lean_dec(v_m_329_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get___redArg(lean_object* v_x_332_, lean_object* v_x_333_, lean_object* v_m_334_, lean_object* v_a_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_x_332_, v_x_333_, v_m_334_, v_a_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get___redArg___boxed(lean_object* v_x_337_, lean_object* v_x_338_, lean_object* v_m_339_, lean_object* v_a_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Std_ExtHashSet_get___redArg(v_x_337_, v_x_338_, v_m_339_, v_a_340_);
lean_dec(v_m_339_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get(lean_object* v_00_u03b1_342_, lean_object* v_x_343_, lean_object* v_x_344_, lean_object* v_inst_345_, lean_object* v_inst_346_, lean_object* v_m_347_, lean_object* v_a_348_, lean_object* v_h_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_x_343_, v_x_344_, v_m_347_, v_a_348_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get___boxed(lean_object* v_00_u03b1_351_, lean_object* v_x_352_, lean_object* v_x_353_, lean_object* v_inst_354_, lean_object* v_inst_355_, lean_object* v_m_356_, lean_object* v_a_357_, lean_object* v_h_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Std_ExtHashSet_get(v_00_u03b1_351_, v_x_352_, v_x_353_, v_inst_354_, v_inst_355_, v_m_356_, v_a_357_, v_h_358_);
lean_dec(v_m_356_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_getD___redArg(lean_object* v_x_360_, lean_object* v_x_361_, lean_object* v_m_362_, lean_object* v_a_363_, lean_object* v_fallback_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_360_, v_x_361_, v_m_362_, v_a_363_, v_fallback_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_getD___redArg___boxed(lean_object* v_x_366_, lean_object* v_x_367_, lean_object* v_m_368_, lean_object* v_a_369_, lean_object* v_fallback_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Std_ExtHashSet_getD___redArg(v_x_366_, v_x_367_, v_m_368_, v_a_369_, v_fallback_370_);
lean_dec(v_fallback_370_);
lean_dec(v_m_368_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_getD(lean_object* v_00_u03b1_372_, lean_object* v_x_373_, lean_object* v_x_374_, lean_object* v_inst_375_, lean_object* v_inst_376_, lean_object* v_m_377_, lean_object* v_a_378_, lean_object* v_fallback_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_373_, v_x_374_, v_m_377_, v_a_378_, v_fallback_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_getD___boxed(lean_object* v_00_u03b1_381_, lean_object* v_x_382_, lean_object* v_x_383_, lean_object* v_inst_384_, lean_object* v_inst_385_, lean_object* v_m_386_, lean_object* v_a_387_, lean_object* v_fallback_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Std_ExtHashSet_getD(v_00_u03b1_381_, v_x_382_, v_x_383_, v_inst_384_, v_inst_385_, v_m_386_, v_a_387_, v_fallback_388_);
lean_dec(v_fallback_388_);
lean_dec(v_m_386_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x21___redArg(lean_object* v_x_390_, lean_object* v_x_391_, lean_object* v_inst_392_, lean_object* v_m_393_, lean_object* v_a_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_390_, v_x_391_, v_inst_392_, v_m_393_, v_a_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x21___redArg___boxed(lean_object* v_x_396_, lean_object* v_x_397_, lean_object* v_inst_398_, lean_object* v_m_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Std_ExtHashSet_get_x21___redArg(v_x_396_, v_x_397_, v_inst_398_, v_m_399_, v_a_400_);
lean_dec(v_m_399_);
lean_dec(v_inst_398_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x21(lean_object* v_00_u03b1_402_, lean_object* v_x_403_, lean_object* v_x_404_, lean_object* v_inst_405_, lean_object* v_inst_406_, lean_object* v_inst_407_, lean_object* v_m_408_, lean_object* v_a_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_403_, v_x_404_, v_inst_407_, v_m_408_, v_a_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x21___boxed(lean_object* v_00_u03b1_411_, lean_object* v_x_412_, lean_object* v_x_413_, lean_object* v_inst_414_, lean_object* v_inst_415_, lean_object* v_inst_416_, lean_object* v_m_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Std_ExtHashSet_get_x21(v_00_u03b1_411_, v_x_412_, v_x_413_, v_inst_414_, v_inst_415_, v_inst_416_, v_m_417_, v_a_418_);
lean_dec(v_m_417_);
lean_dec(v_inst_416_);
return v_res_419_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_isEmpty___redArg(lean_object* v_m_420_){
_start:
{
lean_object* v_size_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
v_size_421_ = lean_ctor_get(v_m_420_, 0);
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = lean_nat_dec_eq(v_size_421_, v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_isEmpty___redArg___boxed(lean_object* v_m_424_){
_start:
{
uint8_t v_res_425_; lean_object* v_r_426_; 
v_res_425_ = l_Std_ExtHashSet_isEmpty___redArg(v_m_424_);
lean_dec(v_m_424_);
v_r_426_ = lean_box(v_res_425_);
return v_r_426_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_isEmpty(lean_object* v_00_u03b1_427_, lean_object* v_x_428_, lean_object* v_x_429_, lean_object* v_inst_430_, lean_object* v_inst_431_, lean_object* v_m_432_){
_start:
{
lean_object* v_size_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v_size_433_ = lean_ctor_get(v_m_432_, 0);
v___x_434_ = lean_unsigned_to_nat(0u);
v___x_435_ = lean_nat_dec_eq(v_size_433_, v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_isEmpty___boxed(lean_object* v_00_u03b1_436_, lean_object* v_x_437_, lean_object* v_x_438_, lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_m_441_){
_start:
{
uint8_t v_res_442_; lean_object* v_r_443_; 
v_res_442_ = l_Std_ExtHashSet_isEmpty(v_00_u03b1_436_, v_x_437_, v_x_438_, v_inst_439_, v_inst_440_, v_m_441_);
lean_dec(v_m_441_);
lean_dec_ref(v_x_438_);
lean_dec_ref(v_x_437_);
v_r_443_ = lean_box(v_res_442_);
return v_r_443_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_ofList___redArg(lean_object* v_inst_467_, lean_object* v_inst_468_, lean_object* v_l_469_){
_start:
{
lean_object* v___f_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___f_470_ = ((lean_object*)(l_Std_ExtHashSet_ofList___redArg___closed__11));
v___x_471_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___closed__1, &l_Std_ExtHashSet_instEmptyCollection___closed__1_once, _init_l_Std_ExtHashSet_instEmptyCollection___closed__1);
v___x_472_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_470_, v_inst_467_, v_inst_468_, v___x_471_, v_l_469_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_ofList(lean_object* v_00_u03b1_473_, lean_object* v_inst_474_, lean_object* v_inst_475_, lean_object* v_l_476_){
_start:
{
lean_object* v___f_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___f_477_ = ((lean_object*)(l_Std_ExtHashSet_ofList___redArg___closed__11));
v___x_478_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___closed__1, &l_Std_ExtHashSet_instEmptyCollection___closed__1_once, _init_l_Std_ExtHashSet_instEmptyCollection___closed__1);
v___x_479_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_477_, v_inst_474_, v_inst_475_, v___x_478_, v_l_476_);
return v___x_479_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_filter___redArg___lam__0(lean_object* v_f_480_, lean_object* v_a_481_, lean_object* v_x_482_){
_start:
{
lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_483_ = lean_apply_1(v_f_480_, v_a_481_);
v___x_484_ = lean_unbox(v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_filter___redArg___lam__0___boxed(lean_object* v_f_485_, lean_object* v_a_486_, lean_object* v_x_487_){
_start:
{
uint8_t v_res_488_; lean_object* v_r_489_; 
v_res_488_ = l_Std_ExtHashSet_filter___redArg___lam__0(v_f_485_, v_a_486_, v_x_487_);
v_r_489_ = lean_box(v_res_488_);
return v_r_489_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_filter___redArg(lean_object* v_f_490_, lean_object* v_m_491_){
_start:
{
lean_object* v___f_492_; lean_object* v___x_493_; 
v___f_492_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_492_, 0, v_f_490_);
v___x_493_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_492_, v_m_491_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_filter(lean_object* v_00_u03b1_494_, lean_object* v_x_495_, lean_object* v_x_496_, lean_object* v_inst_497_, lean_object* v_inst_498_, lean_object* v_f_499_, lean_object* v_m_500_){
_start:
{
lean_object* v___f_501_; lean_object* v___x_502_; 
v___f_501_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_501_, 0, v_f_499_);
v___x_502_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_501_, v_m_500_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_filter___boxed(lean_object* v_00_u03b1_503_, lean_object* v_x_504_, lean_object* v_x_505_, lean_object* v_inst_506_, lean_object* v_inst_507_, lean_object* v_f_508_, lean_object* v_m_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Std_ExtHashSet_filter(v_00_u03b1_503_, v_x_504_, v_x_505_, v_inst_506_, v_inst_507_, v_f_508_, v_m_509_);
lean_dec_ref(v_x_505_);
lean_dec_ref(v_x_504_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insertMany___redArg___lam__0(lean_object* v_x_511_, lean_object* v_x_512_, lean_object* v_a_513_, lean_object* v_____s_514_){
_start:
{
lean_object* v___x_515_; lean_object* v_m_516_; lean_object* v___x_517_; 
v___x_515_ = lean_box(0);
v_m_516_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_511_, v_x_512_, v_____s_514_, v_a_513_, v___x_515_);
v___x_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_517_, 0, v_m_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insertMany___redArg(lean_object* v_x_518_, lean_object* v_x_519_, lean_object* v_inst_520_, lean_object* v_m_521_, lean_object* v_l_522_){
_start:
{
lean_object* v___f_523_; lean_object* v___x_524_; 
v___f_523_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_523_, 0, v_x_518_);
lean_closure_set(v___f_523_, 1, v_x_519_);
v___x_524_ = lean_apply_4(v_inst_520_, lean_box(0), v_l_522_, v_m_521_, v___f_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insertMany(lean_object* v_00_u03b1_525_, lean_object* v_x_526_, lean_object* v_x_527_, lean_object* v_inst_528_, lean_object* v_inst_529_, lean_object* v_00_u03c1_530_, lean_object* v_inst_531_, lean_object* v_m_532_, lean_object* v_l_533_){
_start:
{
lean_object* v___f_534_; lean_object* v___x_535_; 
v___f_534_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_534_, 0, v_x_526_);
lean_closure_set(v___f_534_, 1, v_x_527_);
v___x_535_ = lean_apply_4(v_inst_531_, lean_box(0), v_l_533_, v_m_532_, v___f_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_union___redArg___lam__0(lean_object* v_x_536_, lean_object* v_x_537_, lean_object* v_a_538_, lean_object* v_b_539_, lean_object* v_acc_540_){
_start:
{
lean_object* v_r_541_; lean_object* v___x_542_; 
v_r_541_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_536_, v_x_537_, v_acc_540_, v_a_538_, v_b_539_);
v___x_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_542_, 0, v_r_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_union___redArg___lam__1(lean_object* v___x_543_, lean_object* v___f_544_, lean_object* v_a_545_, lean_object* v_x_546_, lean_object* v___y_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_543_, v___f_544_, v_a_545_, v___y_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_union___redArg(lean_object* v_x_551_, lean_object* v_x_552_, lean_object* v_m_u2081_553_, lean_object* v_m_u2082_554_){
_start:
{
lean_object* v_size_555_; lean_object* v_buckets_556_; lean_object* v_size_557_; uint8_t v___x_558_; 
v_size_555_ = lean_ctor_get(v_m_u2081_553_, 0);
v_buckets_556_ = lean_ctor_get(v_m_u2081_553_, 1);
v_size_557_ = lean_ctor_get(v_m_u2082_554_, 0);
v___x_558_ = lean_nat_dec_le(v_size_555_, v_size_557_);
if (v___x_558_ == 0)
{
lean_object* v___f_559_; lean_object* v___x_560_; 
v___f_559_ = ((lean_object*)(l_Std_ExtHashSet_union___redArg___closed__0));
v___x_560_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_559_, v_x_551_, v_x_552_, v_m_u2081_553_, v_m_u2082_554_);
return v___x_560_;
}
else
{
lean_object* v___f_561_; lean_object* v___x_562_; lean_object* v___f_563_; size_t v_sz_564_; size_t v___x_565_; lean_object* v___x_566_; 
lean_inc_ref(v_buckets_556_);
lean_dec(v_m_u2081_553_);
v___f_561_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_561_, 0, v_x_551_);
lean_closure_set(v___f_561_, 1, v_x_552_);
v___x_562_ = ((lean_object*)(l_Std_ExtHashSet_ofList___redArg___closed__9));
v___f_563_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_563_, 0, v___x_562_);
lean_closure_set(v___f_563_, 1, v___f_561_);
v_sz_564_ = lean_array_size(v_buckets_556_);
v___x_565_ = ((size_t)0ULL);
v___x_566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_562_, v_buckets_556_, v___f_563_, v_sz_564_, v___x_565_, v_m_u2082_554_);
return v___x_566_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_union(lean_object* v_00_u03b1_567_, lean_object* v_x_568_, lean_object* v_x_569_, lean_object* v_inst_570_, lean_object* v_inst_571_, lean_object* v_m_u2081_572_, lean_object* v_m_u2082_573_){
_start:
{
lean_object* v_size_574_; lean_object* v_buckets_575_; lean_object* v_size_576_; uint8_t v___x_577_; 
v_size_574_ = lean_ctor_get(v_m_u2081_572_, 0);
v_buckets_575_ = lean_ctor_get(v_m_u2081_572_, 1);
v_size_576_ = lean_ctor_get(v_m_u2082_573_, 0);
v___x_577_ = lean_nat_dec_le(v_size_574_, v_size_576_);
if (v___x_577_ == 0)
{
lean_object* v___f_578_; lean_object* v___x_579_; 
v___f_578_ = ((lean_object*)(l_Std_ExtHashSet_union___redArg___closed__0));
v___x_579_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_578_, v_x_568_, v_x_569_, v_m_u2081_572_, v_m_u2082_573_);
return v___x_579_;
}
else
{
lean_object* v___f_580_; lean_object* v___x_581_; lean_object* v___f_582_; size_t v_sz_583_; size_t v___x_584_; lean_object* v___x_585_; 
lean_inc_ref(v_buckets_575_);
lean_dec(v_m_u2081_572_);
v___f_580_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_580_, 0, v_x_568_);
lean_closure_set(v___f_580_, 1, v_x_569_);
v___x_581_ = ((lean_object*)(l_Std_ExtHashSet_ofList___redArg___closed__9));
v___f_582_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_582_, 0, v___x_581_);
lean_closure_set(v___f_582_, 1, v___f_580_);
v_sz_583_ = lean_array_size(v_buckets_575_);
v___x_584_ = ((size_t)0ULL);
v___x_585_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_581_, v_buckets_575_, v___f_582_, v_sz_583_, v___x_584_, v_m_u2082_573_);
return v___x_585_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instUnionOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_586_, lean_object* v_x_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_union), 7, 5);
lean_closure_set(v___x_588_, 0, lean_box(0));
lean_closure_set(v___x_588_, 1, v_x_586_);
lean_closure_set(v___x_588_, 2, v_x_587_);
lean_closure_set(v___x_588_, 3, lean_box(0));
lean_closure_set(v___x_588_, 4, lean_box(0));
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instUnionOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_589_, lean_object* v_x_590_, lean_object* v_x_591_, lean_object* v_inst_592_, lean_object* v_inst_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_union), 7, 5);
lean_closure_set(v___x_594_, 0, lean_box(0));
lean_closure_set(v___x_594_, 1, v_x_590_);
lean_closure_set(v___x_594_, 2, v_x_591_);
lean_closure_set(v___x_594_, 3, lean_box(0));
lean_closure_set(v___x_594_, 4, lean_box(0));
return v___x_594_;
}
}
static lean_object* _init_l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_595_; lean_object* v___f_596_; 
v___x_595_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_596_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_596_, 0, v___x_595_);
return v___f_596_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_597_, lean_object* v_x_598_, lean_object* v_m_u2081_599_, lean_object* v_m_u2082_600_){
_start:
{
lean_object* v___f_601_; uint8_t v___x_602_; 
v___f_601_ = lean_obj_once(&l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0, &l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0_once, _init_l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0);
v___x_602_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_x_597_, v_x_598_, v___f_601_, v_m_u2081_599_, v_m_u2082_600_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed(lean_object* v_x_603_, lean_object* v_x_604_, lean_object* v_m_u2081_605_, lean_object* v_m_u2082_606_){
_start:
{
uint8_t v_res_607_; lean_object* v_r_608_; 
v_res_607_ = l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0(v_x_603_, v_x_604_, v_m_u2081_605_, v_m_u2082_606_);
v_r_608_ = lean_box(v_res_607_);
return v_r_608_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_609_, lean_object* v_x_610_){
_start:
{
lean_object* v___f_611_; 
v___f_611_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_611_, 0, v_x_609_);
lean_closure_set(v___f_611_, 1, v_x_610_);
return v___f_611_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_612_, lean_object* v_x_613_, lean_object* v_x_614_, lean_object* v_inst_615_, lean_object* v_inst_616_){
_start:
{
lean_object* v___f_617_; 
v___f_617_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_617_, 0, v_x_613_);
lean_closure_set(v___f_617_, 1, v_x_614_);
return v___f_617_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___redArg(lean_object* v_inst_618_, lean_object* v_inst_619_, lean_object* v_x_620_, lean_object* v_x_621_){
_start:
{
lean_object* v___f_622_; uint8_t v___x_623_; 
v___f_622_ = lean_obj_once(&l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0, &l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0_once, _init_l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0);
v___x_623_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_618_, v_inst_619_, v___f_622_, v_x_620_, v_x_621_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___redArg___boxed(lean_object* v_inst_624_, lean_object* v_inst_625_, lean_object* v_x_626_, lean_object* v_x_627_){
_start:
{
uint8_t v_res_628_; lean_object* v_r_629_; 
v_res_628_ = l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___redArg(v_inst_624_, v_inst_625_, v_x_626_, v_x_627_);
v_r_629_ = lean_box(v_res_628_);
return v_r_629_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_instDecidableEqOfLawfulBEq(lean_object* v_00_u03b1_630_, lean_object* v_inst_631_, lean_object* v_inst_632_, lean_object* v_inst_633_, lean_object* v_x_634_, lean_object* v_x_635_){
_start:
{
uint8_t v___x_636_; 
v___x_636_ = l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___redArg(v_inst_631_, v_inst_633_, v_x_634_, v_x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___boxed(lean_object* v_00_u03b1_637_, lean_object* v_inst_638_, lean_object* v_inst_639_, lean_object* v_inst_640_, lean_object* v_x_641_, lean_object* v_x_642_){
_start:
{
uint8_t v_res_643_; lean_object* v_r_644_; 
v_res_643_ = l_Std_ExtHashSet_instDecidableEqOfLawfulBEq(v_00_u03b1_637_, v_inst_638_, v_inst_639_, v_inst_640_, v_x_641_, v_x_642_);
v_r_644_ = lean_box(v_res_643_);
return v_r_644_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_inter___redArg(lean_object* v_x_645_, lean_object* v_x_646_, lean_object* v_m_u2081_647_, lean_object* v_m_u2082_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_x_645_, v_x_646_, v_m_u2081_647_, v_m_u2082_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_inter(lean_object* v_00_u03b1_650_, lean_object* v_x_651_, lean_object* v_x_652_, lean_object* v_inst_653_, lean_object* v_inst_654_, lean_object* v_m_u2081_655_, lean_object* v_m_u2082_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_x_651_, v_x_652_, v_m_u2081_655_, v_m_u2082_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInterOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_658_, lean_object* v_x_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_inter), 7, 5);
lean_closure_set(v___x_660_, 0, lean_box(0));
lean_closure_set(v___x_660_, 1, v_x_658_);
lean_closure_set(v___x_660_, 2, v_x_659_);
lean_closure_set(v___x_660_, 3, lean_box(0));
lean_closure_set(v___x_660_, 4, lean_box(0));
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInterOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_661_, lean_object* v_x_662_, lean_object* v_x_663_, lean_object* v_inst_664_, lean_object* v_inst_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_inter), 7, 5);
lean_closure_set(v___x_666_, 0, lean_box(0));
lean_closure_set(v___x_666_, 1, v_x_662_);
lean_closure_set(v___x_666_, 2, v_x_663_);
lean_closure_set(v___x_666_, 3, lean_box(0));
lean_closure_set(v___x_666_, 4, lean_box(0));
return v___x_666_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_diff___redArg___lam__0(lean_object* v_x_667_, lean_object* v_x_668_, lean_object* v_m_u2082_669_, uint8_t v___x_670_, lean_object* v_k_671_, lean_object* v_x_672_){
_start:
{
uint8_t v___x_673_; 
v___x_673_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_667_, v_x_668_, v_m_u2082_669_, v_k_671_);
if (v___x_673_ == 0)
{
return v___x_670_;
}
else
{
uint8_t v___x_674_; 
v___x_674_ = 0;
return v___x_674_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_diff___redArg___lam__0___boxed(lean_object* v_x_675_, lean_object* v_x_676_, lean_object* v_m_u2082_677_, lean_object* v___x_678_, lean_object* v_k_679_, lean_object* v_x_680_){
_start:
{
uint8_t v___x_109__boxed_681_; uint8_t v_res_682_; lean_object* v_r_683_; 
v___x_109__boxed_681_ = lean_unbox(v___x_678_);
v_res_682_ = l_Std_ExtHashSet_diff___redArg___lam__0(v_x_675_, v_x_676_, v_m_u2082_677_, v___x_109__boxed_681_, v_k_679_, v_x_680_);
lean_dec(v_m_u2082_677_);
v_r_683_ = lean_box(v_res_682_);
return v_r_683_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_diff___redArg(lean_object* v_x_684_, lean_object* v_x_685_, lean_object* v_m_u2081_686_, lean_object* v_m_u2082_687_){
_start:
{
lean_object* v_size_688_; lean_object* v_size_689_; uint8_t v___x_690_; 
v_size_688_ = lean_ctor_get(v_m_u2081_686_, 0);
v_size_689_ = lean_ctor_get(v_m_u2082_687_, 0);
v___x_690_ = lean_nat_dec_le(v_size_688_, v_size_689_);
if (v___x_690_ == 0)
{
lean_object* v___f_691_; lean_object* v___x_692_; 
v___f_691_ = ((lean_object*)(l_Std_ExtHashSet_union___redArg___closed__0));
v___x_692_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_691_, v_x_684_, v_x_685_, v_m_u2081_686_, v_m_u2082_687_);
return v___x_692_;
}
else
{
lean_object* v___x_693_; lean_object* v___f_694_; lean_object* v___x_695_; 
v___x_693_ = lean_box(v___x_690_);
v___f_694_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_694_, 0, v_x_684_);
lean_closure_set(v___f_694_, 1, v_x_685_);
lean_closure_set(v___f_694_, 2, v_m_u2082_687_);
lean_closure_set(v___f_694_, 3, v___x_693_);
v___x_695_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_694_, v_m_u2081_686_);
return v___x_695_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_diff(lean_object* v_00_u03b1_696_, lean_object* v_x_697_, lean_object* v_x_698_, lean_object* v_inst_699_, lean_object* v_inst_700_, lean_object* v_m_u2081_701_, lean_object* v_m_u2082_702_){
_start:
{
lean_object* v_size_703_; lean_object* v_size_704_; uint8_t v___x_705_; 
v_size_703_ = lean_ctor_get(v_m_u2081_701_, 0);
v_size_704_ = lean_ctor_get(v_m_u2082_702_, 0);
v___x_705_ = lean_nat_dec_le(v_size_703_, v_size_704_);
if (v___x_705_ == 0)
{
lean_object* v___f_706_; lean_object* v___x_707_; 
v___f_706_ = ((lean_object*)(l_Std_ExtHashSet_union___redArg___closed__0));
v___x_707_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_706_, v_x_697_, v_x_698_, v_m_u2081_701_, v_m_u2082_702_);
return v___x_707_;
}
else
{
lean_object* v___x_708_; lean_object* v___f_709_; lean_object* v___x_710_; 
v___x_708_ = lean_box(v___x_705_);
v___f_709_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_709_, 0, v_x_697_);
lean_closure_set(v___f_709_, 1, v_x_698_);
lean_closure_set(v___f_709_, 2, v_m_u2082_702_);
lean_closure_set(v___f_709_, 3, v___x_708_);
v___x_710_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_709_, v_m_u2081_701_);
return v___x_710_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instSDiffOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_711_, lean_object* v_x_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_diff), 7, 5);
lean_closure_set(v___x_713_, 0, lean_box(0));
lean_closure_set(v___x_713_, 1, v_x_711_);
lean_closure_set(v___x_713_, 2, v_x_712_);
lean_closure_set(v___x_713_, 3, lean_box(0));
lean_closure_set(v___x_713_, 4, lean_box(0));
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instSDiffOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_714_, lean_object* v_x_715_, lean_object* v_x_716_, lean_object* v_inst_717_, lean_object* v_inst_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_diff), 7, 5);
lean_closure_set(v___x_719_, 0, lean_box(0));
lean_closure_set(v___x_719_, 1, v_x_715_);
lean_closure_set(v___x_719_, 2, v_x_716_);
lean_closure_set(v___x_719_, 3, lean_box(0));
lean_closure_set(v___x_719_, 4, lean_box(0));
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_ofArray___redArg(lean_object* v_inst_724_, lean_object* v_inst_725_, lean_object* v_l_726_){
_start:
{
lean_object* v___f_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___f_727_ = ((lean_object*)(l_Std_ExtHashSet_ofArray___redArg___closed__1));
v___x_728_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___closed__1, &l_Std_ExtHashSet_instEmptyCollection___closed__1_once, _init_l_Std_ExtHashSet_instEmptyCollection___closed__1);
v___x_729_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_727_, v_inst_724_, v_inst_725_, v___x_728_, v_l_726_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_ofArray(lean_object* v_00_u03b1_730_, lean_object* v_inst_731_, lean_object* v_inst_732_, lean_object* v_l_733_){
_start:
{
lean_object* v___f_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___f_734_ = ((lean_object*)(l_Std_ExtHashSet_ofArray___redArg___closed__1));
v___x_735_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___closed__1, &l_Std_ExtHashSet_instEmptyCollection___closed__1_once, _init_l_Std_ExtHashSet_instEmptyCollection___closed__1);
v___x_736_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_734_, v_inst_731_, v_inst_732_, v___x_735_, v_l_733_);
return v___x_736_;
}
}
lean_object* runtime_initialize_Std_Data_ExtHashMap_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_ExtHashSet_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
