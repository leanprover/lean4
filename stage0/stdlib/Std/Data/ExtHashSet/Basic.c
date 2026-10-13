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
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instEmptyCollection___redArg___boxed(lean_object* v___dummy_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_ExtHashSet_instEmptyCollection___redArg();
return v_res_40_;
}
}
static lean_object* _init_l_Std_ExtHashSet_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Std_ExtHashSet_instEmptyCollection___redArg();
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instEmptyCollection(lean_object* v_00_u03b1_42_, lean_object* v_inst_43_, lean_object* v_inst_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___closed__0, &l_Std_ExtHashSet_instEmptyCollection___closed__0_once, _init_l_Std_ExtHashSet_instEmptyCollection___closed__0);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instEmptyCollection___boxed(lean_object* v_00_u03b1_46_, lean_object* v_inst_47_, lean_object* v_inst_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Std_ExtHashSet_instEmptyCollection(v_00_u03b1_46_, v_inst_47_, v_inst_48_);
lean_dec_ref(v_inst_48_);
lean_dec_ref(v_inst_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInhabited___redArg(){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInhabited___redArg___boxed(lean_object* v___dummy_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Std_ExtHashSet_instInhabited___redArg();
return v_res_53_;
}
}
static lean_object* _init_l_Std_ExtHashSet_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_Std_ExtHashSet_instInhabited___redArg();
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInhabited(lean_object* v_00_u03b1_55_, lean_object* v_inst_56_, lean_object* v_inst_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lean_obj_once(&l_Std_ExtHashSet_instInhabited___closed__0, &l_Std_ExtHashSet_instInhabited___closed__0_once, _init_l_Std_ExtHashSet_instInhabited___closed__0);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInhabited___boxed(lean_object* v_00_u03b1_59_, lean_object* v_inst_60_, lean_object* v_inst_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Std_ExtHashSet_instInhabited(v_00_u03b1_59_, v_inst_60_, v_inst_61_);
lean_dec_ref(v_inst_61_);
lean_dec_ref(v_inst_60_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insert___redArg(lean_object* v_x_63_, lean_object* v_x_64_, lean_object* v_m_65_, lean_object* v_a_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_box(0);
v___x_68_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_63_, v_x_64_, v_m_65_, v_a_66_, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insert(lean_object* v_00_u03b1_69_, lean_object* v_x_70_, lean_object* v_x_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_m_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = lean_box(0);
v___x_77_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_70_, v_x_71_, v_m_74_, v_a_75_, v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_78_, lean_object* v_x_79_, lean_object* v_a_80_){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_81_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1);
v___x_82_ = lean_box(0);
v___x_83_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_78_, v_x_79_, v___x_81_, v_a_80_, v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_84_, lean_object* v_x_85_){
_start:
{
lean_object* v___f_86_; 
v___f_86_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_86_, 0, v_x_84_);
lean_closure_set(v___f_86_, 1, v_x_85_);
return v___f_86_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_87_, lean_object* v_x_88_, lean_object* v_x_89_, lean_object* v_inst_90_, lean_object* v_inst_91_){
_start:
{
lean_object* v___f_92_; 
v___f_92_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_92_, 0, v_x_88_);
lean_closure_set(v___f_92_, 1, v_x_89_);
return v___f_92_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInsertOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_93_, lean_object* v_x_94_, lean_object* v_a_95_, lean_object* v_s_96_){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_box(0);
v___x_98_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_93_, v_x_94_, v_s_96_, v_a_95_, v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInsertOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_99_, lean_object* v_x_100_){
_start:
{
lean_object* v___f_101_; 
v___f_101_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_instInsertOfEquivBEqOfLawfulHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_101_, 0, v_x_99_);
lean_closure_set(v___f_101_, 1, v_x_100_);
return v___f_101_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInsertOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_102_, lean_object* v_x_103_, lean_object* v_x_104_, lean_object* v_inst_105_, lean_object* v_inst_106_){
_start:
{
lean_object* v___f_107_; 
v___f_107_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_instInsertOfEquivBEqOfLawfulHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_107_, 0, v_x_103_);
lean_closure_set(v___f_107_, 1, v_x_104_);
return v___f_107_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_containsThenInsert___redArg(lean_object* v_x_108_, lean_object* v_x_109_, lean_object* v_m_110_, lean_object* v_a_111_){
_start:
{
lean_object* v_size_112_; lean_object* v_buckets_113_; lean_object* v___x_114_; lean_object* v___x_115_; uint64_t v___x_116_; uint64_t v___x_117_; uint64_t v___x_118_; uint64_t v___x_119_; uint64_t v_fold_120_; uint64_t v___x_121_; uint64_t v___x_122_; uint64_t v___x_123_; size_t v___x_124_; size_t v___x_125_; size_t v___x_126_; size_t v___x_127_; size_t v___x_128_; lean_object* v_bkt_129_; uint8_t v___x_130_; 
v_size_112_ = lean_ctor_get(v_m_110_, 0);
v_buckets_113_ = lean_ctor_get(v_m_110_, 1);
v___x_114_ = lean_array_get_size(v_buckets_113_);
lean_inc_ref(v_x_109_);
lean_inc_n(v_a_111_, 2);
v___x_115_ = lean_apply_1(v_x_109_, v_a_111_);
v___x_116_ = 32ULL;
v___x_117_ = lean_unbox_uint64(v___x_115_);
v___x_118_ = lean_uint64_shift_right(v___x_117_, v___x_116_);
v___x_119_ = lean_unbox_uint64(v___x_115_);
lean_dec_ref(v___x_115_);
v_fold_120_ = lean_uint64_xor(v___x_119_, v___x_118_);
v___x_121_ = 16ULL;
v___x_122_ = lean_uint64_shift_right(v_fold_120_, v___x_121_);
v___x_123_ = lean_uint64_xor(v_fold_120_, v___x_122_);
v___x_124_ = lean_uint64_to_usize(v___x_123_);
v___x_125_ = lean_usize_of_nat(v___x_114_);
v___x_126_ = ((size_t)1ULL);
v___x_127_ = lean_usize_sub(v___x_125_, v___x_126_);
v___x_128_ = lean_usize_land(v___x_124_, v___x_127_);
v_bkt_129_ = lean_array_uget_borrowed(v_buckets_113_, v___x_128_);
lean_inc(v_bkt_129_);
v___x_130_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_108_, v_a_111_, v_bkt_129_);
if (v___x_130_ == 0)
{
lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_156_; 
lean_inc_ref(v_buckets_113_);
lean_inc(v_size_112_);
v_isSharedCheck_156_ = !lean_is_exclusive(v_m_110_);
if (v_isSharedCheck_156_ == 0)
{
lean_object* v_unused_157_; lean_object* v_unused_158_; 
v_unused_157_ = lean_ctor_get(v_m_110_, 1);
lean_dec(v_unused_157_);
v_unused_158_ = lean_ctor_get(v_m_110_, 0);
lean_dec(v_unused_158_);
v___x_132_ = v_m_110_;
v_isShared_133_ = v_isSharedCheck_156_;
goto v_resetjp_131_;
}
else
{
lean_dec(v_m_110_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_156_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v_size_x27_136_; lean_object* v___x_137_; lean_object* v_buckets_x27_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v___x_144_; 
v___x_134_ = lean_box(0);
v___x_135_ = lean_unsigned_to_nat(1u);
v_size_x27_136_ = lean_nat_add(v_size_112_, v___x_135_);
lean_dec(v_size_112_);
lean_inc(v_bkt_129_);
v___x_137_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_137_, 0, v_a_111_);
lean_ctor_set(v___x_137_, 1, v___x_134_);
lean_ctor_set(v___x_137_, 2, v_bkt_129_);
v_buckets_x27_138_ = lean_array_uset(v_buckets_113_, v___x_128_, v___x_137_);
v___x_139_ = lean_unsigned_to_nat(4u);
v___x_140_ = lean_nat_mul(v_size_x27_136_, v___x_139_);
v___x_141_ = lean_unsigned_to_nat(3u);
v___x_142_ = lean_nat_div(v___x_140_, v___x_141_);
lean_dec(v___x_140_);
v___x_143_ = lean_array_get_size(v_buckets_x27_138_);
v___x_144_ = lean_nat_dec_le(v___x_142_, v___x_143_);
lean_dec(v___x_142_);
if (v___x_144_ == 0)
{
lean_object* v_val_145_; lean_object* v___x_147_; 
v_val_145_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_109_, v_buckets_x27_138_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 1, v_val_145_);
lean_ctor_set(v___x_132_, 0, v_size_x27_136_);
v___x_147_ = v___x_132_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_size_x27_136_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v_val_145_);
v___x_147_ = v_reuseFailAlloc_150_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = lean_box(v___x_130_);
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v___x_147_);
return v___x_149_;
}
}
else
{
lean_object* v___x_152_; 
lean_dec_ref(v_x_109_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 1, v_buckets_x27_138_);
lean_ctor_set(v___x_132_, 0, v_size_x27_136_);
v___x_152_ = v___x_132_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_size_x27_136_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_buckets_x27_138_);
v___x_152_ = v_reuseFailAlloc_155_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_box(v___x_130_);
v___x_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v___x_152_);
return v___x_154_;
}
}
}
}
else
{
lean_object* v___x_159_; lean_object* v___x_160_; 
lean_dec(v_a_111_);
lean_dec_ref(v_x_109_);
v___x_159_ = lean_box(v___x_130_);
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v_m_110_);
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_containsThenInsert(lean_object* v_00_u03b1_161_, lean_object* v_x_162_, lean_object* v_x_163_, lean_object* v_inst_164_, lean_object* v_inst_165_, lean_object* v_m_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_size_168_; lean_object* v_buckets_169_; lean_object* v___x_170_; lean_object* v___x_171_; uint64_t v___x_172_; uint64_t v___x_173_; uint64_t v___x_174_; uint64_t v___x_175_; uint64_t v_fold_176_; uint64_t v___x_177_; uint64_t v___x_178_; uint64_t v___x_179_; size_t v___x_180_; size_t v___x_181_; size_t v___x_182_; size_t v___x_183_; size_t v___x_184_; lean_object* v_bkt_185_; uint8_t v___x_186_; 
v_size_168_ = lean_ctor_get(v_m_166_, 0);
v_buckets_169_ = lean_ctor_get(v_m_166_, 1);
v___x_170_ = lean_array_get_size(v_buckets_169_);
lean_inc_ref(v_x_163_);
lean_inc_n(v_a_167_, 2);
v___x_171_ = lean_apply_1(v_x_163_, v_a_167_);
v___x_172_ = 32ULL;
v___x_173_ = lean_unbox_uint64(v___x_171_);
v___x_174_ = lean_uint64_shift_right(v___x_173_, v___x_172_);
v___x_175_ = lean_unbox_uint64(v___x_171_);
lean_dec_ref(v___x_171_);
v_fold_176_ = lean_uint64_xor(v___x_175_, v___x_174_);
v___x_177_ = 16ULL;
v___x_178_ = lean_uint64_shift_right(v_fold_176_, v___x_177_);
v___x_179_ = lean_uint64_xor(v_fold_176_, v___x_178_);
v___x_180_ = lean_uint64_to_usize(v___x_179_);
v___x_181_ = lean_usize_of_nat(v___x_170_);
v___x_182_ = ((size_t)1ULL);
v___x_183_ = lean_usize_sub(v___x_181_, v___x_182_);
v___x_184_ = lean_usize_land(v___x_180_, v___x_183_);
v_bkt_185_ = lean_array_uget_borrowed(v_buckets_169_, v___x_184_);
lean_inc(v_bkt_185_);
v___x_186_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_162_, v_a_167_, v_bkt_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_212_; 
lean_inc_ref(v_buckets_169_);
lean_inc(v_size_168_);
v_isSharedCheck_212_ = !lean_is_exclusive(v_m_166_);
if (v_isSharedCheck_212_ == 0)
{
lean_object* v_unused_213_; lean_object* v_unused_214_; 
v_unused_213_ = lean_ctor_get(v_m_166_, 1);
lean_dec(v_unused_213_);
v_unused_214_ = lean_ctor_get(v_m_166_, 0);
lean_dec(v_unused_214_);
v___x_188_ = v_m_166_;
v_isShared_189_ = v_isSharedCheck_212_;
goto v_resetjp_187_;
}
else
{
lean_dec(v_m_166_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_212_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v_size_x27_192_; lean_object* v___x_193_; lean_object* v_buckets_x27_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_190_ = lean_box(0);
v___x_191_ = lean_unsigned_to_nat(1u);
v_size_x27_192_ = lean_nat_add(v_size_168_, v___x_191_);
lean_dec(v_size_168_);
lean_inc(v_bkt_185_);
v___x_193_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_193_, 0, v_a_167_);
lean_ctor_set(v___x_193_, 1, v___x_190_);
lean_ctor_set(v___x_193_, 2, v_bkt_185_);
v_buckets_x27_194_ = lean_array_uset(v_buckets_169_, v___x_184_, v___x_193_);
v___x_195_ = lean_unsigned_to_nat(4u);
v___x_196_ = lean_nat_mul(v_size_x27_192_, v___x_195_);
v___x_197_ = lean_unsigned_to_nat(3u);
v___x_198_ = lean_nat_div(v___x_196_, v___x_197_);
lean_dec(v___x_196_);
v___x_199_ = lean_array_get_size(v_buckets_x27_194_);
v___x_200_ = lean_nat_dec_le(v___x_198_, v___x_199_);
lean_dec(v___x_198_);
if (v___x_200_ == 0)
{
lean_object* v_val_201_; lean_object* v___x_203_; 
v_val_201_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_163_, v_buckets_x27_194_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 1, v_val_201_);
lean_ctor_set(v___x_188_, 0, v_size_x27_192_);
v___x_203_ = v___x_188_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_size_x27_192_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v_val_201_);
v___x_203_ = v_reuseFailAlloc_206_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = lean_box(v___x_186_);
v___x_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v___x_203_);
return v___x_205_;
}
}
else
{
lean_object* v___x_208_; 
lean_dec_ref(v_x_163_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 1, v_buckets_x27_194_);
lean_ctor_set(v___x_188_, 0, v_size_x27_192_);
v___x_208_ = v___x_188_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_size_x27_192_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_buckets_x27_194_);
v___x_208_ = v_reuseFailAlloc_211_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = lean_box(v___x_186_);
v___x_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v___x_208_);
return v___x_210_;
}
}
}
}
else
{
lean_object* v___x_215_; lean_object* v___x_216_; 
lean_dec(v_a_167_);
lean_dec_ref(v_x_163_);
v___x_215_ = lean_box(v___x_186_);
v___x_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v_m_166_);
return v___x_216_;
}
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_contains___redArg(lean_object* v_x_217_, lean_object* v_x_218_, lean_object* v_m_219_, lean_object* v_a_220_){
_start:
{
uint8_t v___x_221_; 
v___x_221_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_217_, v_x_218_, v_m_219_, v_a_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_contains___redArg___boxed(lean_object* v_x_222_, lean_object* v_x_223_, lean_object* v_m_224_, lean_object* v_a_225_){
_start:
{
uint8_t v_res_226_; lean_object* v_r_227_; 
v_res_226_ = l_Std_ExtHashSet_contains___redArg(v_x_222_, v_x_223_, v_m_224_, v_a_225_);
lean_dec(v_m_224_);
v_r_227_ = lean_box(v_res_226_);
return v_r_227_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_contains(lean_object* v_00_u03b1_228_, lean_object* v_x_229_, lean_object* v_x_230_, lean_object* v_inst_231_, lean_object* v_inst_232_, lean_object* v_m_233_, lean_object* v_a_234_){
_start:
{
uint8_t v___x_235_; 
v___x_235_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_229_, v_x_230_, v_m_233_, v_a_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_contains___boxed(lean_object* v_00_u03b1_236_, lean_object* v_x_237_, lean_object* v_x_238_, lean_object* v_inst_239_, lean_object* v_inst_240_, lean_object* v_m_241_, lean_object* v_a_242_){
_start:
{
uint8_t v_res_243_; lean_object* v_r_244_; 
v_res_243_ = l_Std_ExtHashSet_contains(v_00_u03b1_236_, v_x_237_, v_x_238_, v_inst_239_, v_inst_240_, v_m_241_, v_a_242_);
lean_dec(v_m_241_);
v_r_244_ = lean_box(v_res_243_);
return v_r_244_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instMembershipOfEquivBEqOfLawfulHashable___redArg(){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = lean_box(0);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instMembershipOfEquivBEqOfLawfulHashable___redArg___boxed(lean_object* v___dummy_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Std_ExtHashSet_instMembershipOfEquivBEqOfLawfulHashable___redArg();
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instMembershipOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_249_, lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_inst_252_, lean_object* v_inst_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = lean_box(0);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instMembershipOfEquivBEqOfLawfulHashable___boxed(lean_object* v_00_u03b1_255_, lean_object* v_inst_256_, lean_object* v_inst_257_, lean_object* v_inst_258_, lean_object* v_inst_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Std_ExtHashSet_instMembershipOfEquivBEqOfLawfulHashable(v_00_u03b1_255_, v_inst_256_, v_inst_257_, v_inst_258_, v_inst_259_);
lean_dec_ref(v_inst_257_);
lean_dec_ref(v_inst_256_);
return v_res_260_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_instDecidableMem___redArg(lean_object* v_inst_261_, lean_object* v_inst_262_, lean_object* v_m_263_, lean_object* v_a_264_){
_start:
{
uint8_t v___x_265_; 
v___x_265_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_261_, v_inst_262_, v_m_263_, v_a_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instDecidableMem___redArg___boxed(lean_object* v_inst_266_, lean_object* v_inst_267_, lean_object* v_m_268_, lean_object* v_a_269_){
_start:
{
uint8_t v_res_270_; lean_object* v_r_271_; 
v_res_270_ = l_Std_ExtHashSet_instDecidableMem___redArg(v_inst_266_, v_inst_267_, v_m_268_, v_a_269_);
lean_dec(v_m_268_);
v_r_271_ = lean_box(v_res_270_);
return v_r_271_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_instDecidableMem(lean_object* v_00_u03b1_272_, lean_object* v_inst_273_, lean_object* v_inst_274_, lean_object* v_inst_275_, lean_object* v_inst_276_, lean_object* v_m_277_, lean_object* v_a_278_){
_start:
{
uint8_t v___x_279_; 
v___x_279_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_273_, v_inst_274_, v_m_277_, v_a_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instDecidableMem___boxed(lean_object* v_00_u03b1_280_, lean_object* v_inst_281_, lean_object* v_inst_282_, lean_object* v_inst_283_, lean_object* v_inst_284_, lean_object* v_m_285_, lean_object* v_a_286_){
_start:
{
uint8_t v_res_287_; lean_object* v_r_288_; 
v_res_287_ = l_Std_ExtHashSet_instDecidableMem(v_00_u03b1_280_, v_inst_281_, v_inst_282_, v_inst_283_, v_inst_284_, v_m_285_, v_a_286_);
lean_dec(v_m_285_);
v_r_288_ = lean_box(v_res_287_);
return v_r_288_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_erase___redArg(lean_object* v_x_289_, lean_object* v_x_290_, lean_object* v_m_291_, lean_object* v_a_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_289_, v_x_290_, v_m_291_, v_a_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_erase(lean_object* v_00_u03b1_294_, lean_object* v_x_295_, lean_object* v_x_296_, lean_object* v_inst_297_, lean_object* v_inst_298_, lean_object* v_m_299_, lean_object* v_a_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_295_, v_x_296_, v_m_299_, v_a_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_size___redArg(lean_object* v_m_302_){
_start:
{
lean_object* v_size_303_; 
v_size_303_ = lean_ctor_get(v_m_302_, 0);
lean_inc(v_size_303_);
return v_size_303_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_size___redArg___boxed(lean_object* v_m_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Std_ExtHashSet_size___redArg(v_m_304_);
lean_dec(v_m_304_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_size(lean_object* v_00_u03b1_306_, lean_object* v_x_307_, lean_object* v_x_308_, lean_object* v_inst_309_, lean_object* v_inst_310_, lean_object* v_m_311_){
_start:
{
lean_object* v_size_312_; 
v_size_312_ = lean_ctor_get(v_m_311_, 0);
lean_inc(v_size_312_);
return v_size_312_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_size___boxed(lean_object* v_00_u03b1_313_, lean_object* v_x_314_, lean_object* v_x_315_, lean_object* v_inst_316_, lean_object* v_inst_317_, lean_object* v_m_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Std_ExtHashSet_size(v_00_u03b1_313_, v_x_314_, v_x_315_, v_inst_316_, v_inst_317_, v_m_318_);
lean_dec(v_m_318_);
lean_dec_ref(v_x_315_);
lean_dec_ref(v_x_314_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x3f___redArg(lean_object* v_x_320_, lean_object* v_x_321_, lean_object* v_m_322_, lean_object* v_a_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_320_, v_x_321_, v_m_322_, v_a_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x3f___redArg___boxed(lean_object* v_x_325_, lean_object* v_x_326_, lean_object* v_m_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Std_ExtHashSet_get_x3f___redArg(v_x_325_, v_x_326_, v_m_327_, v_a_328_);
lean_dec(v_m_327_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x3f(lean_object* v_00_u03b1_330_, lean_object* v_x_331_, lean_object* v_x_332_, lean_object* v_inst_333_, lean_object* v_inst_334_, lean_object* v_m_335_, lean_object* v_a_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_331_, v_x_332_, v_m_335_, v_a_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x3f___boxed(lean_object* v_00_u03b1_338_, lean_object* v_x_339_, lean_object* v_x_340_, lean_object* v_inst_341_, lean_object* v_inst_342_, lean_object* v_m_343_, lean_object* v_a_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Std_ExtHashSet_get_x3f(v_00_u03b1_338_, v_x_339_, v_x_340_, v_inst_341_, v_inst_342_, v_m_343_, v_a_344_);
lean_dec(v_m_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get___redArg(lean_object* v_x_346_, lean_object* v_x_347_, lean_object* v_m_348_, lean_object* v_a_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_x_346_, v_x_347_, v_m_348_, v_a_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get___redArg___boxed(lean_object* v_x_351_, lean_object* v_x_352_, lean_object* v_m_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Std_ExtHashSet_get___redArg(v_x_351_, v_x_352_, v_m_353_, v_a_354_);
lean_dec(v_m_353_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get(lean_object* v_00_u03b1_356_, lean_object* v_x_357_, lean_object* v_x_358_, lean_object* v_inst_359_, lean_object* v_inst_360_, lean_object* v_m_361_, lean_object* v_a_362_, lean_object* v_h_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_x_357_, v_x_358_, v_m_361_, v_a_362_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get___boxed(lean_object* v_00_u03b1_365_, lean_object* v_x_366_, lean_object* v_x_367_, lean_object* v_inst_368_, lean_object* v_inst_369_, lean_object* v_m_370_, lean_object* v_a_371_, lean_object* v_h_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Std_ExtHashSet_get(v_00_u03b1_365_, v_x_366_, v_x_367_, v_inst_368_, v_inst_369_, v_m_370_, v_a_371_, v_h_372_);
lean_dec(v_m_370_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_getD___redArg(lean_object* v_x_374_, lean_object* v_x_375_, lean_object* v_m_376_, lean_object* v_a_377_, lean_object* v_fallback_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_374_, v_x_375_, v_m_376_, v_a_377_, v_fallback_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_getD___redArg___boxed(lean_object* v_x_380_, lean_object* v_x_381_, lean_object* v_m_382_, lean_object* v_a_383_, lean_object* v_fallback_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Std_ExtHashSet_getD___redArg(v_x_380_, v_x_381_, v_m_382_, v_a_383_, v_fallback_384_);
lean_dec(v_fallback_384_);
lean_dec(v_m_382_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_getD(lean_object* v_00_u03b1_386_, lean_object* v_x_387_, lean_object* v_x_388_, lean_object* v_inst_389_, lean_object* v_inst_390_, lean_object* v_m_391_, lean_object* v_a_392_, lean_object* v_fallback_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_387_, v_x_388_, v_m_391_, v_a_392_, v_fallback_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_getD___boxed(lean_object* v_00_u03b1_395_, lean_object* v_x_396_, lean_object* v_x_397_, lean_object* v_inst_398_, lean_object* v_inst_399_, lean_object* v_m_400_, lean_object* v_a_401_, lean_object* v_fallback_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Std_ExtHashSet_getD(v_00_u03b1_395_, v_x_396_, v_x_397_, v_inst_398_, v_inst_399_, v_m_400_, v_a_401_, v_fallback_402_);
lean_dec(v_fallback_402_);
lean_dec(v_m_400_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x21___redArg(lean_object* v_x_404_, lean_object* v_x_405_, lean_object* v_inst_406_, lean_object* v_m_407_, lean_object* v_a_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_404_, v_x_405_, v_inst_406_, v_m_407_, v_a_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x21___redArg___boxed(lean_object* v_x_410_, lean_object* v_x_411_, lean_object* v_inst_412_, lean_object* v_m_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Std_ExtHashSet_get_x21___redArg(v_x_410_, v_x_411_, v_inst_412_, v_m_413_, v_a_414_);
lean_dec(v_m_413_);
lean_dec(v_inst_412_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x21(lean_object* v_00_u03b1_416_, lean_object* v_x_417_, lean_object* v_x_418_, lean_object* v_inst_419_, lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_m_422_, lean_object* v_a_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_417_, v_x_418_, v_inst_421_, v_m_422_, v_a_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_get_x21___boxed(lean_object* v_00_u03b1_425_, lean_object* v_x_426_, lean_object* v_x_427_, lean_object* v_inst_428_, lean_object* v_inst_429_, lean_object* v_inst_430_, lean_object* v_m_431_, lean_object* v_a_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_ExtHashSet_get_x21(v_00_u03b1_425_, v_x_426_, v_x_427_, v_inst_428_, v_inst_429_, v_inst_430_, v_m_431_, v_a_432_);
lean_dec(v_m_431_);
lean_dec(v_inst_430_);
return v_res_433_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_isEmpty___redArg(lean_object* v_m_434_){
_start:
{
lean_object* v_size_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v_size_435_ = lean_ctor_get(v_m_434_, 0);
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = lean_nat_dec_eq(v_size_435_, v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_isEmpty___redArg___boxed(lean_object* v_m_438_){
_start:
{
uint8_t v_res_439_; lean_object* v_r_440_; 
v_res_439_ = l_Std_ExtHashSet_isEmpty___redArg(v_m_438_);
lean_dec(v_m_438_);
v_r_440_ = lean_box(v_res_439_);
return v_r_440_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_isEmpty(lean_object* v_00_u03b1_441_, lean_object* v_x_442_, lean_object* v_x_443_, lean_object* v_inst_444_, lean_object* v_inst_445_, lean_object* v_m_446_){
_start:
{
lean_object* v_size_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v_size_447_ = lean_ctor_get(v_m_446_, 0);
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = lean_nat_dec_eq(v_size_447_, v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_isEmpty___boxed(lean_object* v_00_u03b1_450_, lean_object* v_x_451_, lean_object* v_x_452_, lean_object* v_inst_453_, lean_object* v_inst_454_, lean_object* v_m_455_){
_start:
{
uint8_t v_res_456_; lean_object* v_r_457_; 
v_res_456_ = l_Std_ExtHashSet_isEmpty(v_00_u03b1_450_, v_x_451_, v_x_452_, v_inst_453_, v_inst_454_, v_m_455_);
lean_dec(v_m_455_);
lean_dec_ref(v_x_452_);
lean_dec_ref(v_x_451_);
v_r_457_ = lean_box(v_res_456_);
return v_r_457_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_ofList___redArg(lean_object* v_inst_481_, lean_object* v_inst_482_, lean_object* v_l_483_){
_start:
{
lean_object* v___f_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___f_484_ = ((lean_object*)(l_Std_ExtHashSet_ofList___redArg___closed__11));
v___x_485_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1);
v___x_486_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_484_, v_inst_481_, v_inst_482_, v___x_485_, v_l_483_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_ofList(lean_object* v_00_u03b1_487_, lean_object* v_inst_488_, lean_object* v_inst_489_, lean_object* v_l_490_){
_start:
{
lean_object* v___f_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___f_491_ = ((lean_object*)(l_Std_ExtHashSet_ofList___redArg___closed__11));
v___x_492_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1);
v___x_493_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_491_, v_inst_488_, v_inst_489_, v___x_492_, v_l_490_);
return v___x_493_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_filter___redArg___lam__0(lean_object* v_f_494_, lean_object* v_a_495_, lean_object* v_x_496_){
_start:
{
lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_497_ = lean_apply_1(v_f_494_, v_a_495_);
v___x_498_ = lean_unbox(v___x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_filter___redArg___lam__0___boxed(lean_object* v_f_499_, lean_object* v_a_500_, lean_object* v_x_501_){
_start:
{
uint8_t v_res_502_; lean_object* v_r_503_; 
v_res_502_ = l_Std_ExtHashSet_filter___redArg___lam__0(v_f_499_, v_a_500_, v_x_501_);
v_r_503_ = lean_box(v_res_502_);
return v_r_503_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_filter___redArg(lean_object* v_f_504_, lean_object* v_m_505_){
_start:
{
lean_object* v___f_506_; lean_object* v___x_507_; 
v___f_506_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_506_, 0, v_f_504_);
v___x_507_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_506_, v_m_505_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_filter(lean_object* v_00_u03b1_508_, lean_object* v_x_509_, lean_object* v_x_510_, lean_object* v_inst_511_, lean_object* v_inst_512_, lean_object* v_f_513_, lean_object* v_m_514_){
_start:
{
lean_object* v___f_515_; lean_object* v___x_516_; 
v___f_515_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_515_, 0, v_f_513_);
v___x_516_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_515_, v_m_514_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_filter___boxed(lean_object* v_00_u03b1_517_, lean_object* v_x_518_, lean_object* v_x_519_, lean_object* v_inst_520_, lean_object* v_inst_521_, lean_object* v_f_522_, lean_object* v_m_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Std_ExtHashSet_filter(v_00_u03b1_517_, v_x_518_, v_x_519_, v_inst_520_, v_inst_521_, v_f_522_, v_m_523_);
lean_dec_ref(v_x_519_);
lean_dec_ref(v_x_518_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insertMany___redArg___lam__0(lean_object* v_x_525_, lean_object* v_x_526_, lean_object* v_a_527_, lean_object* v_____s_528_){
_start:
{
lean_object* v___x_529_; lean_object* v_m_530_; lean_object* v___x_531_; 
v___x_529_ = lean_box(0);
v_m_530_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_525_, v_x_526_, v_____s_528_, v_a_527_, v___x_529_);
v___x_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_531_, 0, v_m_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insertMany___redArg(lean_object* v_x_532_, lean_object* v_x_533_, lean_object* v_inst_534_, lean_object* v_m_535_, lean_object* v_l_536_){
_start:
{
lean_object* v___f_537_; lean_object* v___x_538_; 
v___f_537_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_537_, 0, v_x_532_);
lean_closure_set(v___f_537_, 1, v_x_533_);
v___x_538_ = lean_apply_4(v_inst_534_, lean_box(0), v_l_536_, v_m_535_, v___f_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_insertMany(lean_object* v_00_u03b1_539_, lean_object* v_x_540_, lean_object* v_x_541_, lean_object* v_inst_542_, lean_object* v_inst_543_, lean_object* v_00_u03c1_544_, lean_object* v_inst_545_, lean_object* v_m_546_, lean_object* v_l_547_){
_start:
{
lean_object* v___f_548_; lean_object* v___x_549_; 
v___f_548_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_548_, 0, v_x_540_);
lean_closure_set(v___f_548_, 1, v_x_541_);
v___x_549_ = lean_apply_4(v_inst_545_, lean_box(0), v_l_547_, v_m_546_, v___f_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_union___redArg___lam__0(lean_object* v_x_550_, lean_object* v_x_551_, lean_object* v_a_552_, lean_object* v_b_553_, lean_object* v_acc_554_){
_start:
{
lean_object* v_r_555_; lean_object* v___x_556_; 
v_r_555_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_550_, v_x_551_, v_acc_554_, v_a_552_, v_b_553_);
v___x_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_556_, 0, v_r_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_union___redArg___lam__1(lean_object* v___x_557_, lean_object* v___f_558_, lean_object* v_a_559_, lean_object* v_x_560_, lean_object* v___y_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_557_, v___f_558_, v_a_559_, v___y_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_union___redArg(lean_object* v_x_565_, lean_object* v_x_566_, lean_object* v_m_u2081_567_, lean_object* v_m_u2082_568_){
_start:
{
lean_object* v___x_569_; lean_object* v_size_570_; lean_object* v_buckets_571_; lean_object* v_size_572_; uint8_t v___x_573_; 
v___x_569_ = ((lean_object*)(l_Std_ExtHashSet_ofList___redArg___closed__9));
v_size_570_ = lean_ctor_get(v_m_u2081_567_, 0);
v_buckets_571_ = lean_ctor_get(v_m_u2081_567_, 1);
v_size_572_ = lean_ctor_get(v_m_u2082_568_, 0);
v___x_573_ = lean_nat_dec_le(v_size_570_, v_size_572_);
if (v___x_573_ == 0)
{
lean_object* v___f_574_; lean_object* v___x_575_; 
v___f_574_ = ((lean_object*)(l_Std_ExtHashSet_union___redArg___closed__0));
v___x_575_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_574_, v_x_565_, v_x_566_, v_m_u2081_567_, v_m_u2082_568_);
return v___x_575_;
}
else
{
lean_object* v___f_576_; lean_object* v___f_577_; size_t v_sz_578_; size_t v___x_579_; lean_object* v___x_580_; 
lean_inc_ref(v_buckets_571_);
lean_dec(v_m_u2081_567_);
v___f_576_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_576_, 0, v_x_565_);
lean_closure_set(v___f_576_, 1, v_x_566_);
v___f_577_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_577_, 0, v___x_569_);
lean_closure_set(v___f_577_, 1, v___f_576_);
v_sz_578_ = lean_array_size(v_buckets_571_);
v___x_579_ = ((size_t)0ULL);
v___x_580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_569_, v_buckets_571_, v___f_577_, v_sz_578_, v___x_579_, v_m_u2082_568_);
return v___x_580_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_union(lean_object* v_00_u03b1_581_, lean_object* v_x_582_, lean_object* v_x_583_, lean_object* v_inst_584_, lean_object* v_inst_585_, lean_object* v_m_u2081_586_, lean_object* v_m_u2082_587_){
_start:
{
lean_object* v___x_588_; lean_object* v_size_589_; lean_object* v_buckets_590_; lean_object* v_size_591_; uint8_t v___x_592_; 
v___x_588_ = ((lean_object*)(l_Std_ExtHashSet_ofList___redArg___closed__9));
v_size_589_ = lean_ctor_get(v_m_u2081_586_, 0);
v_buckets_590_ = lean_ctor_get(v_m_u2081_586_, 1);
v_size_591_ = lean_ctor_get(v_m_u2082_587_, 0);
v___x_592_ = lean_nat_dec_le(v_size_589_, v_size_591_);
if (v___x_592_ == 0)
{
lean_object* v___f_593_; lean_object* v___x_594_; 
v___f_593_ = ((lean_object*)(l_Std_ExtHashSet_union___redArg___closed__0));
v___x_594_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_593_, v_x_582_, v_x_583_, v_m_u2081_586_, v_m_u2082_587_);
return v___x_594_;
}
else
{
lean_object* v___f_595_; lean_object* v___f_596_; size_t v_sz_597_; size_t v___x_598_; lean_object* v___x_599_; 
lean_inc_ref(v_buckets_590_);
lean_dec(v_m_u2081_586_);
v___f_595_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_595_, 0, v_x_582_);
lean_closure_set(v___f_595_, 1, v_x_583_);
v___f_596_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_596_, 0, v___x_588_);
lean_closure_set(v___f_596_, 1, v___f_595_);
v_sz_597_ = lean_array_size(v_buckets_590_);
v___x_598_ = ((size_t)0ULL);
v___x_599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_588_, v_buckets_590_, v___f_596_, v_sz_597_, v___x_598_, v_m_u2082_587_);
return v___x_599_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instUnionOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_600_, lean_object* v_x_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_union), 7, 5);
lean_closure_set(v___x_602_, 0, lean_box(0));
lean_closure_set(v___x_602_, 1, v_x_600_);
lean_closure_set(v___x_602_, 2, v_x_601_);
lean_closure_set(v___x_602_, 3, lean_box(0));
lean_closure_set(v___x_602_, 4, lean_box(0));
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instUnionOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_603_, lean_object* v_x_604_, lean_object* v_x_605_, lean_object* v_inst_606_, lean_object* v_inst_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_union), 7, 5);
lean_closure_set(v___x_608_, 0, lean_box(0));
lean_closure_set(v___x_608_, 1, v_x_604_);
lean_closure_set(v___x_608_, 2, v_x_605_);
lean_closure_set(v___x_608_, 3, lean_box(0));
lean_closure_set(v___x_608_, 4, lean_box(0));
return v___x_608_;
}
}
static lean_object* _init_l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_609_; lean_object* v___f_610_; 
v___x_609_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_610_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_610_, 0, v___x_609_);
return v___f_610_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0(lean_object* v_x_611_, lean_object* v_x_612_, lean_object* v_m_u2081_613_, lean_object* v_m_u2082_614_){
_start:
{
lean_object* v___f_615_; uint8_t v___x_616_; 
v___f_615_ = lean_obj_once(&l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0, &l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0_once, _init_l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0);
v___x_616_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_x_611_, v_x_612_, v___f_615_, v_m_u2081_613_, v_m_u2082_614_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed(lean_object* v_x_617_, lean_object* v_x_618_, lean_object* v_m_u2081_619_, lean_object* v_m_u2082_620_){
_start:
{
uint8_t v_res_621_; lean_object* v_r_622_; 
v_res_621_ = l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0(v_x_617_, v_x_618_, v_m_u2081_619_, v_m_u2082_620_);
v_r_622_ = lean_box(v_res_621_);
return v_r_622_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_623_, lean_object* v_x_624_){
_start:
{
lean_object* v___f_625_; 
v___f_625_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_625_, 0, v_x_623_);
lean_closure_set(v___f_625_, 1, v_x_624_);
return v___f_625_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_626_, lean_object* v_x_627_, lean_object* v_x_628_, lean_object* v_inst_629_, lean_object* v_inst_630_){
_start:
{
lean_object* v___f_631_; 
v___f_631_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_631_, 0, v_x_627_);
lean_closure_set(v___f_631_, 1, v_x_628_);
return v___f_631_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___redArg(lean_object* v_inst_632_, lean_object* v_inst_633_, lean_object* v_x_634_, lean_object* v_x_635_){
_start:
{
lean_object* v___f_636_; uint8_t v___x_637_; 
v___f_636_ = lean_obj_once(&l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0, &l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0_once, _init_l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0);
v___x_637_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_632_, v_inst_633_, v___f_636_, v_x_634_, v_x_635_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___redArg___boxed(lean_object* v_inst_638_, lean_object* v_inst_639_, lean_object* v_x_640_, lean_object* v_x_641_){
_start:
{
uint8_t v_res_642_; lean_object* v_r_643_; 
v_res_642_ = l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___redArg(v_inst_638_, v_inst_639_, v_x_640_, v_x_641_);
v_r_643_ = lean_box(v_res_642_);
return v_r_643_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_instDecidableEqOfLawfulBEq(lean_object* v_00_u03b1_644_, lean_object* v_inst_645_, lean_object* v_inst_646_, lean_object* v_inst_647_, lean_object* v_x_648_, lean_object* v_x_649_){
_start:
{
uint8_t v___x_650_; 
v___x_650_ = l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___redArg(v_inst_645_, v_inst_647_, v_x_648_, v_x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___boxed(lean_object* v_00_u03b1_651_, lean_object* v_inst_652_, lean_object* v_inst_653_, lean_object* v_inst_654_, lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
uint8_t v_res_657_; lean_object* v_r_658_; 
v_res_657_ = l_Std_ExtHashSet_instDecidableEqOfLawfulBEq(v_00_u03b1_651_, v_inst_652_, v_inst_653_, v_inst_654_, v_x_655_, v_x_656_);
v_r_658_ = lean_box(v_res_657_);
return v_r_658_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_inter___redArg(lean_object* v_x_659_, lean_object* v_x_660_, lean_object* v_m_u2081_661_, lean_object* v_m_u2082_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_x_659_, v_x_660_, v_m_u2081_661_, v_m_u2082_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_inter(lean_object* v_00_u03b1_664_, lean_object* v_x_665_, lean_object* v_x_666_, lean_object* v_inst_667_, lean_object* v_inst_668_, lean_object* v_m_u2081_669_, lean_object* v_m_u2082_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_x_665_, v_x_666_, v_m_u2081_669_, v_m_u2082_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInterOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_672_, lean_object* v_x_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_inter), 7, 5);
lean_closure_set(v___x_674_, 0, lean_box(0));
lean_closure_set(v___x_674_, 1, v_x_672_);
lean_closure_set(v___x_674_, 2, v_x_673_);
lean_closure_set(v___x_674_, 3, lean_box(0));
lean_closure_set(v___x_674_, 4, lean_box(0));
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instInterOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_675_, lean_object* v_x_676_, lean_object* v_x_677_, lean_object* v_inst_678_, lean_object* v_inst_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_inter), 7, 5);
lean_closure_set(v___x_680_, 0, lean_box(0));
lean_closure_set(v___x_680_, 1, v_x_676_);
lean_closure_set(v___x_680_, 2, v_x_677_);
lean_closure_set(v___x_680_, 3, lean_box(0));
lean_closure_set(v___x_680_, 4, lean_box(0));
return v___x_680_;
}
}
LEAN_EXPORT uint8_t l_Std_ExtHashSet_diff___redArg___lam__0(lean_object* v_x_681_, lean_object* v_x_682_, lean_object* v_m_u2082_683_, uint8_t v___x_684_, lean_object* v_k_685_, lean_object* v_x_686_){
_start:
{
uint8_t v___x_687_; 
v___x_687_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_681_, v_x_682_, v_m_u2082_683_, v_k_685_);
if (v___x_687_ == 0)
{
return v___x_684_;
}
else
{
uint8_t v___x_688_; 
v___x_688_ = 0;
return v___x_688_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_diff___redArg___lam__0___boxed(lean_object* v_x_689_, lean_object* v_x_690_, lean_object* v_m_u2082_691_, lean_object* v___x_692_, lean_object* v_k_693_, lean_object* v_x_694_){
_start:
{
uint8_t v___x_110__boxed_695_; uint8_t v_res_696_; lean_object* v_r_697_; 
v___x_110__boxed_695_ = lean_unbox(v___x_692_);
v_res_696_ = l_Std_ExtHashSet_diff___redArg___lam__0(v_x_689_, v_x_690_, v_m_u2082_691_, v___x_110__boxed_695_, v_k_693_, v_x_694_);
lean_dec(v_m_u2082_691_);
v_r_697_ = lean_box(v_res_696_);
return v_r_697_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_diff___redArg(lean_object* v_x_698_, lean_object* v_x_699_, lean_object* v_m_u2081_700_, lean_object* v_m_u2082_701_){
_start:
{
lean_object* v_size_702_; lean_object* v_size_703_; uint8_t v___x_704_; 
v_size_702_ = lean_ctor_get(v_m_u2081_700_, 0);
v_size_703_ = lean_ctor_get(v_m_u2082_701_, 0);
v___x_704_ = lean_nat_dec_le(v_size_702_, v_size_703_);
if (v___x_704_ == 0)
{
lean_object* v___f_705_; lean_object* v___x_706_; 
v___f_705_ = ((lean_object*)(l_Std_ExtHashSet_union___redArg___closed__0));
v___x_706_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_705_, v_x_698_, v_x_699_, v_m_u2081_700_, v_m_u2082_701_);
return v___x_706_;
}
else
{
lean_object* v___x_707_; lean_object* v___f_708_; lean_object* v___x_709_; 
v___x_707_ = lean_box(v___x_704_);
v___f_708_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_708_, 0, v_x_698_);
lean_closure_set(v___f_708_, 1, v_x_699_);
lean_closure_set(v___f_708_, 2, v_m_u2082_701_);
lean_closure_set(v___f_708_, 3, v___x_707_);
v___x_709_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_708_, v_m_u2081_700_);
return v___x_709_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_diff(lean_object* v_00_u03b1_710_, lean_object* v_x_711_, lean_object* v_x_712_, lean_object* v_inst_713_, lean_object* v_inst_714_, lean_object* v_m_u2081_715_, lean_object* v_m_u2082_716_){
_start:
{
lean_object* v_size_717_; lean_object* v_size_718_; uint8_t v___x_719_; 
v_size_717_ = lean_ctor_get(v_m_u2081_715_, 0);
v_size_718_ = lean_ctor_get(v_m_u2082_716_, 0);
v___x_719_ = lean_nat_dec_le(v_size_717_, v_size_718_);
if (v___x_719_ == 0)
{
lean_object* v___f_720_; lean_object* v___x_721_; 
v___f_720_ = ((lean_object*)(l_Std_ExtHashSet_union___redArg___closed__0));
v___x_721_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_720_, v_x_711_, v_x_712_, v_m_u2081_715_, v_m_u2082_716_);
return v___x_721_;
}
else
{
lean_object* v___x_722_; lean_object* v___f_723_; lean_object* v___x_724_; 
v___x_722_ = lean_box(v___x_719_);
v___f_723_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_723_, 0, v_x_711_);
lean_closure_set(v___f_723_, 1, v_x_712_);
lean_closure_set(v___f_723_, 2, v_m_u2082_716_);
lean_closure_set(v___f_723_, 3, v___x_722_);
v___x_724_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_723_, v_m_u2081_715_);
return v___x_724_;
}
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instSDiffOfEquivBEqOfLawfulHashable___redArg(lean_object* v_x_725_, lean_object* v_x_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_diff), 7, 5);
lean_closure_set(v___x_727_, 0, lean_box(0));
lean_closure_set(v___x_727_, 1, v_x_725_);
lean_closure_set(v___x_727_, 2, v_x_726_);
lean_closure_set(v___x_727_, 3, lean_box(0));
lean_closure_set(v___x_727_, 4, lean_box(0));
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_instSDiffOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_728_, lean_object* v_x_729_, lean_object* v_x_730_, lean_object* v_inst_731_, lean_object* v_inst_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = lean_alloc_closure((void*)(l_Std_ExtHashSet_diff), 7, 5);
lean_closure_set(v___x_733_, 0, lean_box(0));
lean_closure_set(v___x_733_, 1, v_x_729_);
lean_closure_set(v___x_733_, 2, v_x_730_);
lean_closure_set(v___x_733_, 3, lean_box(0));
lean_closure_set(v___x_733_, 4, lean_box(0));
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_ofArray___redArg(lean_object* v_inst_738_, lean_object* v_inst_739_, lean_object* v_l_740_){
_start:
{
lean_object* v___f_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___f_741_ = ((lean_object*)(l_Std_ExtHashSet_ofArray___redArg___closed__1));
v___x_742_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1);
v___x_743_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_741_, v_inst_738_, v_inst_739_, v___x_742_, v_l_740_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Std_ExtHashSet_ofArray(lean_object* v_00_u03b1_744_, lean_object* v_inst_745_, lean_object* v_inst_746_, lean_object* v_l_747_){
_start:
{
lean_object* v___f_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___f_748_ = ((lean_object*)(l_Std_ExtHashSet_ofArray___redArg___closed__1));
v___x_749_ = lean_obj_once(&l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1, &l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_ExtHashSet_instEmptyCollection___redArg___closed__1);
v___x_750_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_748_, v_inst_745_, v_inst_746_, v___x_749_, v_l_747_);
return v___x_750_;
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
